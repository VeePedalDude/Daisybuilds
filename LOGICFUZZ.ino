// don't judge me too much on organization and method.  There's a fair amount of chatgpt and claude copy pasta and copiolt why is there squigly lines everywhere
//This is heavily inspired by the parasite studio designs at it's core it's an 8-bitar kinda.  
// There are ranges listed in a few areas if you want to play around with the interval values.  This was basically tuned on one guitar and a PA speaker I use for an amp. 
// If you want something special find my youtube and I try to cook it up for the community. 
#include "DaisyDuino.h"
#include <math.h>

//  Safety guards 
#ifndef MORPH_NORM_HZ
#define MORPH_NORM_HZ   4.0f    // detector 
#endif
#ifndef NORM_MIN
#define NORM_MIN        0.60f
#endif
#ifndef NORM_MAX
#define NORM_MAX        1.60f
#endif

// Controls 
#define POT_LEVEL_PIN A1     // Level
#define POT_SAG_PIN   A2     // SAG 
#define POT_TONE_PIN  A3     // TONE 
#define POT_TRUTH_PIN A4     // TRUTH (logic mixer morph)
#define POT_RATE_PIN  A5     // RATE 
#define POT_DEPTH_PIN A6     // DEPTH 
#define MOD_TRUTH_PIN D7     // LFO→TRUTH 
#define MOD_TONE_PIN  D8     // LFO→TONE  
#define OCT_UP_PIN    D9     // logic octave up 
#define OCT_DN_PIN    D10    // logic octave down 

// hardware 
#define ADC_MAX        1023.0f
#define POT_SMOOTH     0.01f

// Crossover
#define XOVER_LOW_HZ    180.0f
#define XOVER_HIGH_HZ  1600.0f

// Postmix tone split should work with A3
// 
#define TONE_SPLIT_HZ   900.0f

//  Logic trim 
#define MIX_TRIM        0.55f

// LFO 
#define LFO_MIN_HZ      0.05f
#define LFO_MAX_HZ      8.00f

// Octave stuff
#define OCTUP_DELAY_HZ  1800.0f   // small lag for XOR doubler 
#define OCT_DN_DEPTH    0.35f
#define OCT_UP_DEPTH    0.35f

// powersag
#define SAG_V0       1.0f
#define SAG_ATK      0.02f   // droop
#define SAG_REL      0.004f  // recover

// Globals 
float sample_rate;
volatile float pot_level = 0.75f; // 0..1
volatile float pot_sag   = 0.50f; // 0..1
volatile float pot_tone  = 0.50f; // 0..1
volatile float pot_truth = 0.00f; // 0..1 (0=rails sum, 1=MAJ), continuous morph
volatile int   oct_up_on = 0, oct_dn_on = 0;
volatile int   tone_mod_on = 0, truth_mod_on = 0;
volatile float pot_rate  = 0.25f; // 0..1 → 0.05..8 Hz
volatile float pot_depth = 0.00f; // 0..1 → 0..±0.5 mod

// LFO state
static float lfo_phase = 0.0f;

// more sag stuff
static float sag_v = SAG_V0, sag_env = 0.0f;
static float sag_hp_y = 0.0f, sag_hp_x1 = 0.0f;

//  Utilities 
static inline float fast_tanh(float x){ return tanhf(x); }
static inline float fast_abs(float x){ return x >= 0.0f ? x : -x; }
static inline float clamp01(float x){ if(x < 0.0f) return 0.0f; if(x > 1.0f) return 1.0f; return x; }
static inline float onepole_alpha(float cutoff_hz, float fs){
  float a = -2.0f * (float)M_PI * (cutoff_hz / fs);
  float alpha = 1.0f - expf(a);
  if(alpha < 0.0f) alpha = 0.0f; if(alpha > 1.0f) alpha = 1.0f; return alpha;
}

//  jitter noise more fuzz quarks
static uint32_t rng = 22222u;
static inline float frand(){ rng = 1664525u*rng + 1013904223u; uint32_t v = (rng >> 9) & 0x7FFFFFu; return (float)v / 8388607.0f * 2.0f - 1.0f; }

// Slew 
static inline float slew_step(float z, float target, float a_up, float a_dn){ float a = (target > z) ? a_up : a_dn; return z + a * (target - z); }

// daisyduino doesn't have biquad 
struct RBQ {
  float b0,b1,b2,a1,a2,z1,z2; // a0=1
  void reset(){ z1=z2=0.0f; }
  float process(float x){ float y=b0*x+z1; z1=b1*x-a1*y+z2; z2=b2*x-a2*y; return y; }
  void make_lp(float fs,float fc,float Q){
    float w0=2.0f*(float)M_PI*(fc/fs), cw=cosf(w0), sw=sinf(w0), alpha=sw/(2.0f*Q);
    float a0=1.0f+alpha, a1t=-2.0f*cw, a2t=1.0f-alpha;
    float b0t=(1.0f-cw)*0.5f, b1t=1.0f-cw, b2t=(1.0f-cw)*0.5f;
    b0=b0t/a0; b1=b1t/a0; b2=b2t/a0; a1=a1t/a0; a2=a2t/a0; reset();
  }
  void make_hp(float fs,float fc,float Q){
    float w0=2.0f*(float)M_PI*(fc/fs), cw=cosf(w0), sw=sinf(w0), alpha=sw/(2.0f*Q);
    float a0=1.0f+alpha, a1t=-2.0f*cw, a2t=1.0f-alpha;
    float b0t=(1.0f+cw)*0.5f, b1t=-(1.0f+cw), b2t=(1.0f+cw)*0.5f;
    b0=b0t/a0; b1=b1t/a0; b2=b2t/a0; a1=a1t/a0; a2=a2t/a0; reset();
  }
};

//  LR4 stacks 
RBQ LP_f1[2], HP_f1[2], LP_f2[2], HP_f2[2];

// 
static float stL = -1.0f, stM = -1.0f, stH = -1.0f; // logic 
static float zL = 0.0f, zM = 0.0f, zH = 0.0f;       // slewed 

// Logic-gate mixer 
static float zNAND = 0.0f, zXOR = 0.0f, zXNOR = 0.0f, zMAJ = 0.0f;

// loudness detector 
static float venv0 = 0.0f, venv1 = 0.0f, venv2 = 0.0f, venv3 = 0.0f, venv4 = 0.0f;
static float norm_alpha = 0.0f;

// tone
static float tone_lp = 0.0f;   // LP integrator 
static float tone_hp_y = 0.0f; // HP output 
static float tone_hp_x1 = 0.0f; // HP input
static float tone_hp_R  = 0.0f; // HP 

// Octave each band
static float zOCTDN_L = 0.0f;      // Low band /2 rail slewed
static float tff_L    = -1.0f;     // LowT flip‑flop state
static int   prev_low_bool = 0;    // Low edge detect
static float oct_dly_H = 0.0f;     // High XOR doubler
static float zOCTUP_H  = 0.0f;     // XOR rail
static float octup_alpha = 0.0f;   // 

// Edge base speed
static float edge_alpha_base = 0.0f; 
static float tone_alpha       = 0.0f; 

// presplit 
static inline float FF1_SagStage(float x, float fs)
{
  // more power preclip
  float pre = x * 8.0f;
  float sat = fast_tanh(pre);
  float i_est = fast_abs(sat);
  // envelope
  if(i_est > sag_env) sag_env += SAG_ATK * (i_est - sag_env); else sag_env += SAG_REL * (i_est - sag_env);
  // knob maps
  float s = pot_sag; // 0..1
  float amt  = 0.15f + 1.05f * (s * s * s); // 0.15..1.20
  float vmin = 0.50f - 0.30f * s;           // 0.50..0.20
  // virtual supply
  float v_tgt = SAG_V0 - amt * sag_env; if(v_tgt < vmin) v_tgt = vmin; if(v_tgt > SAG_V0) v_tgt = SAG_V0;
  float k = (v_tgt < sag_v) ? SAG_ATK : SAG_REL; sag_v += k * (v_tgt - sag_v);
  // bias & headroom
  float bias = -(1.0f - sag_v) * 0.12f;
  float head = 0.85f * sag_v + 0.10f;
  float a = pre + bias;
  float pos = fast_tanh(a / head) * head;
  float neg = fast_tanh(a / (0.8f*head)) * (0.8f*head);
  float y   = 0.5f * (pos + neg);
  // gentle make-up
  y *= 1.0f + 0.8f * (1.0f - sag_v);
  // dynamic gate HP (starve → higher fc)
  float sv = (1.0f - sag_v);
  float fc = 20.0f + (600.0f - 20.0f) * (sv * sv);
  float R = expf(-2.0f * (float)M_PI * (fc / fs));
  float hp = y - sag_hp_x1 + R * sag_hp_y; sag_hp_x1 = y; sag_hp_y = hp; return hp;
}

// Band Schmitt and jitter get jit wid it.
static inline void schmitt_advance(float vin, float bias, float width, float jit_amp, float &state)
{
  float jit = jit_amp * frand();
  float up = bias + 0.5f * width + jit;
  float dn = bias - 0.5f * width - jit;
  if(state < 0.0f){ if(vin >= up) state = +1.0f; }
  else            { if(vin <= dn) state = -1.0f; }
}

// Callback 
void AudioCallback(float **in, float **out, size_t size)
{
  // LFO setup 
  const float mod_amp = 0.5f * (pot_depth * pot_depth); // 0..0.5
  const float lfo_hz = LFO_MIN_HZ + (LFO_MAX_HZ - LFO_MIN_HZ) * pot_rate;
  const float lfo_inc = lfo_hz / sample_rate;
  const int enTone = tone_mod_on;
  const int enTruth = truth_mod_on;

  const float level = pot_level; // 0..1
  const float levelGain = 2.0f * (level * level);

  for(size_t i = 0; i < size; ++i)
  {
    // triangle LFO 
    lfo_phase += lfo_inc; if(lfo_phase >= 1.0f) lfo_phase -= 1.0f;
    float lfoTri = 2.0f * fabsf(2.0f * lfo_phase - 1.0f) - 1.0f; // 1→-1 triangle
    // Preamp with sag & gate
    float x = FF1_SagStage(in[0][i], sample_rate);

    // 3way LR split
    float low = LP_f1[0].process(x);  low = LP_f1[1].process(low);
    float hp1 = HP_f1[0].process(x);  hp1 = HP_f1[1].process(hp1);
    float mid = LP_f2[0].process(hp1); mid = LP_f2[1].process(mid);
    float high= HP_f2[0].process(hp1); high= HP_f2[1].process(high);

    // Comparator drive 
    float dL = fast_tanh(low  * 6.0f);
    float dM = fast_tanh(mid  * 6.0f);
    float dH = fast_tanh(high * 6.0f);

    // there's a bunch of stuff going on here 
    float starve = (1.0f - sag_v);
    float wL = 0.10f + 0.08f * starve;   // base widths per band
    float wM = 0.12f + 0.06f * starve;
    float wH = 0.08f + 0.08f * starve;
    float jit = 0.02f * (0.3f + 0.7f * starve);

    // make it weird
    float bL = -0.02f * (1.0f + 0.5f * starve);
    float bM =  0.00f;
    float bH = +0.02f * (1.0f + 0.5f * starve);

    // Update Schmitt 
    schmitt_advance(dL, bL, wL, jit, stL);
    schmitt_advance(dM, bM, wM, jit, stM);
    schmitt_advance(dH, bH, wH, jit, stH);

    // Edge slew 
    float a_up = edge_alpha_base * (0.25f + 0.75f * sag_v);
    float a_dn = edge_alpha_base * (0.45f + 0.55f * sag_v);
    float rail = 0.6f + 0.4f * sag_v;

    // Slew on rails 
    zL = slew_step(zL, stL * rail, a_up, a_dn);
    zM = slew_step(zM, stM * rail, a_up, a_dn);
    zH = slew_step(zH, stH * rail, a_up, a_dn);

    // logic gates 
    int bLo = stL > 0.0f, bMi = stM > 0.0f, bHi = stH > 0.0f;

    // ===== Per-band Logic Octaves =====
    // Reuse current edge slew & rail (a_up, a_dn, rail)
    // Low band: Octave Down (/2 via T‑flip‑flop on rising edges of low band)
    if(bLo && !prev_low_bool) { tff_L = -tff_L; }
    zOCTDN_L = slew_step(zOCTDN_L, tff_L * rail, a_up, a_dn);
    prev_low_bool = bLo;
    if(oct_dn_on) { zL = (1.0f - OCT_DN_DEPTH) * zL + OCT_DN_DEPTH * zOCTDN_L; }

    // High band: Octave Up (XOR high band with a tiny delayed copy)
    oct_dly_H += octup_alpha * ( (bHi ? +rail : -rail) - oct_dly_H );
    int dly_boolH = (oct_dly_H > 0.0f) ? 1 : 0;
    int xor_pulseH = (bHi ^ dly_boolH);
    zOCTUP_H = slew_step(zOCTUP_H, (xor_pulseH ? +rail : -rail), a_up, a_dn);
    if(oct_up_on) { zH = (1.0f - OCT_UP_DEPTH) * zH + OCT_UP_DEPTH * zOCTUP_H; }

    // Logic gates this is part of the magic for the Truth control
    float gNAND = (!(bLo & bMi)) ? +rail : -rail;            // NAND(L, M)
    float gXOR  = (bMi ^ bHi)      ? +rail : -rail;          // XOR(M, H)
    float gXNOR = (!(bLo ^ bHi))   ? +rail : -rail;          // XNOR(L, H)
    float gMAJ  = ((bLo + bMi + bHi) >= 2) ? +rail : -rail;  // MAJORITY(L,M,H)

    // Slew gate edges too
    zNAND = slew_step(zNAND, gNAND, a_up, a_dn);
    zXOR  = slew_step(zXOR,  gXOR,  a_up, a_dn);
    zXNOR = slew_step(zXNOR, gXNOR, a_up, a_dn);
    zMAJ  = slew_step(zMAJ,  gMAJ,  a_up, a_dn);

    // Truth Morph mixer (A4)
    float tTruth = clamp01(pot_truth + (enTruth ? (mod_amp * lfoTri) : 0.0f)); // 0..1

    // Voices 
    float vBase = (zL + zM + zH) * (1.0f/3.0f);
    float v1 = zXNOR;
    float v2 = zXOR;
    float v3 = zNAND;
    float v4 = zMAJ;

    //  detectors per voice
    venv0 += norm_alpha * (vBase*vBase - venv0);
    venv1 += norm_alpha * (v1*v1     - venv1);
    venv2 += norm_alpha * (v2*v2     - venv2);
    venv3 += norm_alpha * (v3*v3     - venv3);
    venv4 += norm_alpha * (v4*v4     - venv4);

    // Triangle weights 
    float w0 = fmaxf(0.0f, 1.0f - fabsf(tTruth - 0.00f) / 0.25f);
    float w1 = fmaxf(0.0f, 1.0f - fabsf(tTruth - 0.25f) / 0.25f);
    float w2 = fmaxf(0.0f, 1.0f - fabsf(tTruth - 0.50f) / 0.25f);
    float w3 = fmaxf(0.0f, 1.0f - fabsf(tTruth - 0.75f) / 0.25f);
    float w4 = fmaxf(0.0f, 1.0f - fabsf(tTruth - 1.00f) / 0.25f);
    float ws = w0 + w1 + w2 + w3 + w4; if(ws < 1e-6f) ws = 1.0f;
    w0 /= ws; w1 /= ws; w2 /= ws; w3 /= ws; w4 /= ws;

    // Estimate mix power and normalize 
    const float eps = 1e-6f;
    float ms_est   = (w0*w0)*venv0 + (w1*w1)*venv1 + (w2*w2)*venv2 + (w3*w3)*venv3 + (w4*w4)*venv4 + eps;
    float ms_target= (venv0 + venv1 + venv2 + venv3 + venv4) * 0.2f + eps; // average of voices
    float gNorm    = sqrtf(ms_target / ms_est);
    if(gNorm < NORM_MIN) gNorm = NORM_MIN; else if(gNorm > NORM_MAX) gNorm = NORM_MAX;

    // morph  normalization
    float yMix = MIX_TRIM * gNorm * ( w0 * vBase
                                     + w1 * v1
                                     + w2 * v2
                                     + w3 * v3
                                     + w4 * v4 );

    // tone control
    tone_lp += tone_alpha * (yMix - tone_lp);
    float yLP = tone_lp;
    // simple HP (y[n] = x[n] − x[n−1] + R*y[n−1])
    float yHP = yMix - tone_hp_x1 + tone_hp_R * tone_hp_y;
    tone_hp_x1 = yMix;
    tone_hp_y  = yHP;

    // Crossfade 
    float tTone = clamp01(pot_tone + (enTone ? (mod_amp * lfoTri) : 0.0f)); // 0..1 (0=LP,1=HP)
    float yTone = 0.25f * yMix + (1.0f - tTone) * yLP + tTone * yHP;

    // Level 
    float y = yTone * levelGain;
    out[0][i] = y;
    out[1][i] = y;
  }
}

void setup()
{
  DAISY.init(DAISY_SEED, AUDIO_SR_48K);
  sample_rate = DAISY.get_samplerate();

  const float Qbw = 0.70710678f; // LR4 (Butterworth)
  LP_f1[0].make_lp(sample_rate, XOVER_LOW_HZ,  Qbw);
  LP_f1[1].make_lp(sample_rate, XOVER_LOW_HZ,  Qbw);
  HP_f1[0].make_hp(sample_rate, XOVER_LOW_HZ,  Qbw);
  HP_f1[1].make_hp(sample_rate, XOVER_LOW_HZ,  Qbw);
  LP_f2[0].make_lp(sample_rate, XOVER_HIGH_HZ, Qbw);
  LP_f2[1].make_lp(sample_rate, XOVER_HIGH_HZ, Qbw);
  HP_f2[0].make_hp(sample_rate, XOVER_HIGH_HZ, Qbw);
  HP_f2[1].make_hp(sample_rate, XOVER_HIGH_HZ, Qbw);

  // Edge base ~8 kHz
  edge_alpha_base = onepole_alpha(8000.0f, sample_rate);
  tone_alpha      = onepole_alpha(TONE_SPLIT_HZ, sample_rate);
  tone_hp_R       = expf(-2.0f * (float)M_PI * (TONE_SPLIT_HZ / sample_rate));
  octup_alpha     = onepole_alpha(OCTUP_DELAY_HZ, sample_rate);
  norm_alpha      = onepole_alpha(MORPH_NORM_HZ, sample_rate);

  pinMode(POT_LEVEL_PIN, INPUT);
  pinMode(POT_SAG_PIN,   INPUT);
  pinMode(POT_TONE_PIN,  INPUT);
  pinMode(POT_TRUTH_PIN, INPUT);
  pinMode(POT_RATE_PIN,  INPUT);
  pinMode(POT_DEPTH_PIN, INPUT);
  pinMode(MOD_TRUTH_PIN, INPUT_PULLUP);
  pinMode(MOD_TONE_PIN,  INPUT_PULLUP);
  pinMode(OCT_UP_PIN,    INPUT_PULLUP);
  pinMode(OCT_DN_PIN,    INPUT_PULLUP);

  DAISY.begin(AudioCallback);
}

void loop()
{
  // Read A1 LEVEL
  int rl = analogRead(POT_LEVEL_PIN);
  float lvl = (float)rl / ADC_MAX;
  pot_level += POT_SMOOTH * (lvl - pot_level);

  // Read A2 SAG
  int rs = analogRead(POT_SAG_PIN);
  float sag = (float)rs / ADC_MAX;
  pot_sag += POT_SMOOTH * (sag - pot_sag);

  // Read A3 TONE
  int rt = analogRead(POT_TONE_PIN);
  float ton = (float)rt / ADC_MAX;
  pot_tone += POT_SMOOTH * (ton - pot_tone);

  // Read A4 TRUTH morph
  int rtr = analogRead(POT_TRUTH_PIN);
  float trv = (float)rtr / ADC_MAX;
  pot_truth += POT_SMOOTH * (trv - pot_truth);

  // Read A5 RATE
  int rr = analogRead(POT_RATE_PIN);
  float rvl = (float)rr / ADC_MAX;
  pot_rate += POT_SMOOTH * (rvl - pot_rate);

  // Read A6 DEPTH
  int rdpt = analogRead(POT_DEPTH_PIN);
  float dvl = (float)rdpt / ADC_MAX;
  pot_depth += POT_SMOOTH * (dvl - pot_depth);

  // Read toggles for LFO routing 
  tone_mod_on  = !digitalRead(MOD_TONE_PIN)  ? 1 : 0; // LOW=ON (pulled up)
  truth_mod_on = !digitalRead(MOD_TRUTH_PIN) ? 1 : 0;

  // Read octave toggles 
  oct_up_on = !digitalRead(OCT_UP_PIN) ? 1 : 0;   // LOW = ON (pulled up)
  oct_dn_on = !digitalRead(OCT_DN_PIN) ? 1 : 0;
}