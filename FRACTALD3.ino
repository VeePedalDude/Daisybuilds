// FractalDelay
//  - A1 time, A3 mix, A4 level, A5 drive

#include "DaisyDuino.h"
#include <cmath>

#define BUF_SAMPLES 24000
static float delayBuf[BUF_SAMPLES];
static int   wpos = 0;

// Switch pins (active-low)
#define SW_V0  D10
#define SW_V1  D9
#define SW_V2  D8
#define SW_TEX D7

// Texture presets (D7)
#define TEX_LOW_PRESET   0.15f
#define TEX_HIGH_PRESET  0.85f

// Processed-return max gain
#define PROC_FB_MAX      0.22f

// Reverse state for D0 branches
#define MAX_BRANCHES 16
static float rev_phase[MAX_BRANCHES] = {0.f};
static int   rev_len  [MAX_BRANCHES] = {64};

// Cross-delay modulation state (smoother, slower)
static float xmod_lfo1 = 0.f, xmod_lfo2 = 0.f, xmod_lfo3 = 0.f;
static float xmod_phase1 = 0.f, xmod_phase2 = 0.f, xmod_phase3 = 0.f;
static float xmod_target1 = 0.f, xmod_target2 = 0.f, xmod_target3 = 0.f;

// Sparkle effect state
static float sparkle_hp = 0.f;
static float sparkle_lp = 0.f;
static float sparkle_env = 0.f;

// Smoothed controls - ALL variables declared here
static volatile float kTime=0.f, kFB=0.f, kMix=0.5f, kLevel=1.f, kDrive=0.f, kRet=0.f, kTex=0.f, kSparkle=0.f;
static float sTime=0.f, sFB=0.f, sMix=0.5f, sLevel=1.f, sDrive=0.f, sRet=0.f, sTex=0.f, sSparkle=0.f;

// Smoothed gates
static volatile float kGate0=0.f, kGate1=0.f, kGate2=0.f;
static float sGate0=0.f, sGate1=0.f, sGate2=0.f;

// Drive Character features
static float dc_B = 0.0f, dc_Eoct = 0.0f, dc_C = 0.0f;

// Helpers
static inline float clampf(float x, float lo, float hi){ return (x<lo)?lo:(x>hi)?hi:x; }
static inline float lerpf (float a, float b, float t)  { return a + t*(b-a); }
static inline float softsignf(float x){ return x / (1.0f + fabsf(x)); }

// Fractional read from circular buffer
static inline float readDelayFrac(const float* buf, int w, int maxlen, float delaySamples)
{
  if(delaySamples < 1.f) delaySamples = 1.f;
  if(delaySamples >= (float)maxlen) delaySamples = (float)maxlen - 1.f;
  float pos = (float)w - delaySamples;
  while(pos < 0.f) pos += (float)maxlen;
  int   i0   = (int)pos;
  int   i1   = i0 + 1; if(i1 >= maxlen) i1 -= maxlen;
  float frac = pos - (float)i0;
  return lerpf(buf[i0], buf[i1], frac);
}

static inline float octaveUpShaper(float x) { return fabsf(x) - 0.5f * x; }
static inline float depthNorm(int depth) { return 1.0f / sqrtf(1.0f + (float)depth); }

// --- Smoother Cross-Delay Modulation ---
static inline void updateCrossModulation(float rate, float depth)
{
  const float sr = DAISY.get_samplerate();
  
  // Much slower modulation for stability
  const float freq1 = 0.07f * rate;  // Reduced from 0.13f
  const float freq2 = 0.11f * rate;  // Reduced from 0.21f
  const float freq3 = 0.17f * rate;  // Reduced from 0.34f
  
  // Update phases
  xmod_phase1 += freq1 / sr;
  xmod_phase2 += freq2 / sr;
  xmod_phase3 += freq3 / sr;
  
  if(xmod_phase1 >= 1.f) xmod_phase1 -= 1.f;
  if(xmod_phase2 >= 1.f) xmod_phase2 -= 1.f;
  if(xmod_phase3 >= 1.f) xmod_phase3 -= 1.f;
  
  // Generate target values
  xmod_target1 = depth * sinf(2.f * M_PI * xmod_phase1);
  xmod_target2 = depth * sinf(2.f * M_PI * xmod_phase2);
  xmod_target3 = depth * sinf(2.f * M_PI * xmod_phase3);
  
  // Heavy smoothing to prevent zipper noise
  const float a = 0.0005f;  // Much smoother than before
  xmod_lfo1 += a * (xmod_target1 - xmod_lfo1);
  xmod_lfo2 += a * (xmod_target2 - xmod_lfo2);
  xmod_lfo3 += a * (xmod_target3 - xmod_lfo3);
}

// --- Fractal Sparkle Effect ---
// Lightweight brightness enhancer modulated by fractal energy
static inline float processFractalSparkle(float input, float fractalMod, float amount)
{
  if(amount < 0.01f) return 0.f;
  
  // Extract high frequencies with simple high-pass
  const float hp_cutoff = 0.85f;  // Gentle high-pass
  float hp_out = input - sparkle_hp;
  sparkle_hp = input - hp_cutoff * hp_out;
  
  // Envelope follower on fractal energy
  const float env_attack = 0.98f;
  const float env_release = 0.995f;
  float target = fabsf(fractalMod);
  if(target > sparkle_env)
    sparkle_env = env_attack * sparkle_env + (1.0f - env_attack) * target;
  else
    sparkle_env = env_release * sparkle_env + (1.0f - env_release) * target;
  
  // Apply fractal-modulated excitation to highs
  float excited = hp_out * (1.0f + 2.0f * sparkle_env);
  
  // Soft saturation for sparkle character
  excited = tanhf(excited * 1.5f);
  
  // Mix with subtle low-pass of the excited signal for shimmer
  const float lp_cutoff = 0.3f;
  sparkle_lp = sparkle_lp + lp_cutoff * (excited - sparkle_lp);
  
  // Combine direct excited highs with filtered version
  float sparkle = excited * 0.7f + sparkle_lp * 0.3f;
  
  return amount * sparkle * 0.4f;  // Scale for mix
}

// --- D0 fractal with texture ---
static inline float fractalSum_D0_tex(const float* buf, int w, int maxlen, float d_base, int depth, float tex)
{
  static const int divs[3] = {2,4,8};
  if(d_base < 1.f) d_base = 1.f;
  if(depth <= 0) return 0.f;
  if(depth > 4)  depth = 4;

  float w_fwd = lerpf(0.85f, 0.45f, tex);
  float w_oct = lerpf(0.10f, 0.35f, tex);
  float w_rev = lerpf(0.05f, 0.35f, tex);
  float wn = 1.0f / (w_fwd + w_oct + w_rev);
  w_fwd *= wn; w_oct *= wn; w_rev *= wn;

  float lenScaleBase = 0.35f + 0.50f * tex;

  float sum = 0.f;
  for(int gen = 1; gen <= depth; ++gen)
  {
    float amp = powf(0.5f, (float)gen);
    for(int k = 0; k < 3; ++k)
    {
      int   bi = (gen - 1) * 3 + k; if(bi >= MAX_BRANCHES) continue;
      float ds = d_base / (float)divs[k];

      float yf = readDelayFrac(buf, w, maxlen, ds);
      float yo = octaveUpShaper(yf);

      int   L  = (int)(lenScaleBase * ds);
      if(L < 32) L = 32; if(L > 2048) L = 2048;
      rev_len[bi] = L;
      float phase = rev_phase[bi];
      float t     = phase / (float)L;
      float win   = 1.f - fabsf(2.f * t - 1.f);
      float yr    = readDelayFrac(buf, w, maxlen, ds + phase) * win;
      phase += 1.f; if(phase >= (float)L) phase = 0.f;
      rev_phase[bi] = phase;

      sum += amp * (w_fwd * yf + w_oct * yo + w_rev * yr);
    }
  }
  return sum * depthNorm(depth);
}

// --- D1 fractal with texture ---
static inline float fractalSum_D1_tex(const float* buf, int w, int maxlen, float d_base, int depth, float tex)
{
  static const int divs[3] = {2,4,8};
  if(d_base < 1.f) d_base = 1.f;
  if(depth <= 0) return 0.f;
  if(depth > 2)  depth = 2;

  float w_fwd = lerpf(0.80f, 0.60f, tex);
  float w_oct = lerpf(0.20f, 0.40f, tex);
  float wn = 1.0f / (w_fwd + w_oct);
  w_fwd *= wn; w_oct *= wn;

  float sum = 0.f;
  for(int gen = 1; gen <= depth; ++gen)
  {
    float amp = powf(0.5f, (float)gen);
    for(int k = 0; k < 3; ++k)
    {
      float ds = d_base / (float)divs[k];
      float yf = readDelayFrac(buf, w, maxlen, ds);
      float yo = octaveUpShaper(yf);
      sum += amp * (w_fwd * yf + w_oct * yo);
    }
  }
  return sum * depthNorm(depth);
}

// --- D2 fractal ---
static inline float fractalSum_D2(const float* buf, int w, int maxlen, float d_base, int depth)
{
  static const int divs[3] = {2,4,8};
  if(d_base < 1.f) d_base = 1.f;
  if(depth <= 0) return 0.f;
  if(depth > 1)  depth = 1;

  float sum = 0.f;
  for(int gen = 1; gen <= depth; ++gen)
  {
    float amp = powf(0.5f, (float)gen);
    for(int k = 0; k < 3; ++k)
    {
      float ds = d_base / (float)divs[k];
      float yf = readDelayFrac(buf, w, maxlen, ds);
      sum += amp * yf;
    }
  }
  return sum * depthNorm(depth);
}

void AudioCallback(float **in, float **out, size_t size)
{
  const float timeNorm   = kTime;
  const float beta       = 0.85f * clampf(kFB,0.f,1.f);
  const float levelKn    = clampf(kLevel,0.f,1.f);
  const float driveKn    = clampf(kDrive,0.f,1.f);
  const float tex        = clampf(kTex,  0.f,1.f);
  const float retGain    = PROC_FB_MAX * clampf(kRet,0.f,1.f);
  const float mix        = clampf(kMix,  0.f,1.f);
  const float sparkleAmt = clampf(kSparkle, 0.f, 1.f);

  const float sr       = DAISY.get_samplerate();
  const float baseMs   = 20.f + timeNorm * 480.f;
  
  // Gentler cross-modulation depth
  float xmodDepth = 0.04f + 0.06f * timeNorm;  // Reduced from 0.08-0.12
  updateCrossModulation(1.0f + 1.0f * tex, xmodDepth);
  
  // Apply smoothed modulation to delay times
  float d0_base = clampf(baseMs * 0.001f * sr, 1.f, (float)BUF_SAMPLES - 2.f);
  float d0 = d0_base * (1.0f + xmod_lfo1);
  float d1 = clampf(d0_base * (2.f/3.f) * (1.0f + xmod_lfo2), 1.f, (float)BUF_SAMPLES - 2.f);
  float d2 = clampf(d0_base * (3.f/5.f) * (1.0f + xmod_lfo3), 1.f, (float)BUF_SAMPLES - 2.f);

  const int   depth0 = 4, depth1 = 2, depth2 = 1;
  const float gF0 = 0.26f * depthNorm(depth0);
  const float gF1 = 0.17f * depthNorm(depth1);
  const float gF2 = 0.13f * depthNorm(depth2);

  const float c0 = 1.00f, c1 = 0.55f, c2 = 0.45f;
  const float g0 = clampf(kGate0, 0.f, 1.f);
  const float g1 = clampf(kGate1, 0.f, 1.f);
  const float g2 = clampf(kGate2, 0.f, 1.f);

  const float w0 = 1.00f, w1 = 0.80f, w2 = 0.65f;

  // Master level mapping
  const float level_dB  = -12.0f + 21.0f * levelKn;
  const float level_lin = powf(10.0f, level_dB / 20.0f);

  static float lim_env = 0.0f, lim_gain = 1.0f;
  static bool  lim_inited = false;
  static float lim_aAtk, lim_aRel;
  const float LIM_THR = 0.95f;
  if(!lim_inited){
    lim_aAtk = expf(-1.0f / (0.003f * sr));
    lim_aRel = expf(-1.0f / (0.050f * sr));
    lim_inited = true;
  }

  for(size_t i = 0; i < size; ++i)
  {
    float xi = 0.5f * (in[0][i] + in[1][i]);

    // Base taps with modulated delays
    float y0 = readDelayFrac(delayBuf, wpos, BUF_SAMPLES, d0);
    float y1 = readDelayFrac(delayBuf, wpos, BUF_SAMPLES, d1);
    float y2 = readDelayFrac(delayBuf, wpos, BUF_SAMPLES, d2);

    // Fractal sums
    float f0 = gF0 * fractalSum_D0_tex(delayBuf, wpos, BUF_SAMPLES, d0, depth0, tex);
    float f1 = gF1 * fractalSum_D1_tex(delayBuf, wpos, BUF_SAMPLES, d1, depth1, tex);
    float f2 = gF2 * fractalSum_D2    (delayBuf, wpos, BUF_SAMPLES, d2, depth2);

    // Drive Character
    const float eps = 1e-6f;
    float B_now    = fabsf(f0) + 0.5f*fabsf(f1) + 0.35f*fabsf(f2);
    float Eoct_now = fabsf(f1);
    float C_now    = fabsf(y0 - y2) / (fabsf(y0) + fabsf(y2) + eps);

    const float aDC = 0.005f;
    dc_B    += aDC * (B_now    - dc_B);
    dc_Eoct += aDC * (Eoct_now - dc_Eoct);
    dc_C    += aDC * (C_now    - dc_C);

    float pre_dB =  9.0f * driveKn + 3.0f * dc_C;
    float hard   = powf(10.0f, pre_dB / 20.0f);

    float asym    = 0.12f * (dc_B - 0.20f);
    float evenmix = clampf(0.10f + 0.50f * dc_Eoct, 0.0f, 0.65f);

    float xpre   = xi + asym * softsignf(xi);
    float y_odd  = tanhf(hard * xpre);
    float y_even = fabsf(xpre) - 0.5f * xpre;
    float makeup = powf(10.0f, (3.0f * driveKn) / 20.0f);

    float pre = ((1.0f - evenmix) * y_odd + evenmix * y_even) * makeup;

    // Processed voices
    float v0 = y0 + f0;
    float v1 = y1 + f1;
    float v2 = y2 + f2;

    // Standard feedback
    float fb_signal = c0 * y0 + c1 * y1 + c2 * y2;
    fb_signal += retGain * (g0 * v0 + g1 * v1 + g2 * v2);
    
    float fb_in = tanhf(0.9f * beta * fb_signal);

    // Write to buffer
    float write = pre + fb_in;
    delayBuf[wpos] = clampf(write, -1.f, 1.f);
    if(++wpos >= BUF_SAMPLES) wpos = 0;

    // Wet sum
    float wet = w0 * y0 + w1 * y1 + w2 * y2 + (f0 + f1 + f2);
    
    // Add fractal sparkle when enabled (D7 HIGH)
    // Use fractal sum magnitudes to modulate sparkle intensity
    float fractalEnergy = clampf(fabsf(f0) + fabsf(f1) * 0.5f + fabsf(f2) * 0.3f, -1.f, 1.f);
    float sparkle = processFractalSparkle(wet, fractalEnergy, sparkleAmt);
    wet = wet + sparkle;
    
    float y = (1.f - mix) * xi + mix * wet;

    // Master gain + limiter
    float post = y * level_lin;
    float a = fabsf(post);
    lim_env = (a > lim_env) ? (lim_aAtk * lim_env + (1.f - lim_aAtk) * a)
                            : (lim_aRel * lim_env + (1.f - lim_aRel) * a);
    float target = (lim_env > LIM_THR) ? (LIM_THR / (lim_env + 1e-9f)) : 1.0f;
    lim_gain = 0.2f * target + 0.8f * lim_gain;
    float y_out = post * lim_gain;

    out[0][i] = y_out;
    out[1][i] = y_out;
  }
}

void setup()
{
  DAISY.init(DAISY_SEED, AUDIO_SR_48K);
  
  // Clear buffers
  for(int i = 0; i < BUF_SAMPLES; ++i) delayBuf[i] = 0.f;
  for(int i = 0; i < MAX_BRANCHES; ++i){ rev_phase[i] = 0.f; rev_len[i] = 64; }
  
  // Initialize sparkle state
  sparkle_hp = sparkle_lp = sparkle_env = 0.f;
  
  pinMode(SW_V0,  INPUT_PULLUP);
  pinMode(SW_V1,  INPUT_PULLUP);
  pinMode(SW_V2,  INPUT_PULLUP);
  pinMode(SW_TEX, INPUT_PULLUP);
  
  DAISY.begin(AudioCallback);
}

void loop()
{
  float rTime  = analogRead(A1) / 1023.f;
  float rFB    = analogRead(A2) / 1023.f;
  float rMix   = analogRead(A3) / 1023.f;
  float rLevel = analogRead(A4) / 1023.f;
  float rDrive = analogRead(A5) / 1023.f;
  float rRet   = analogRead(A6) / 1023.f;

  bool v0_on   = (digitalRead(SW_V0)  == LOW);
  bool v1_on   = (digitalRead(SW_V1)  == LOW);
  bool v2_on   = (digitalRead(SW_V2)  == LOW);
  bool tex_hi  = (digitalRead(SW_TEX) == LOW);

  // D7 controls both texture preset AND sparkle enable
  float targTex     = tex_hi ? TEX_HIGH_PRESET : TEX_LOW_PRESET;
  float targSparkle = tex_hi ? 0.6f : 0.0f;  // Enable sparkle when D7 is HIGH

  float targTime  = clampf(rTime,  0.f, 1.f);
  float targFB    = clampf(rFB,    0.f, 1.f);
  float targMix   = clampf(rMix,   0.f, 1.f);
  float targLevel = clampf(rLevel, 0.f, 1.f);
  float targDrive = clampf(rDrive, 0.f, 1.f);
  float targRet   = clampf(rRet,   0.f, 1.f);

  float targG0 = v0_on ? 1.f : 0.f;
  float targG1 = v1_on ? 1.f : 0.f;
  float targG2 = v2_on ? 1.f : 0.f;

  const float lam  = 0.04f;
  const float lamG = 0.12f;

  sTime    += lam  * (targTime    - sTime);
  sFB      += lam  * (targFB      - sFB);
  sMix     += lam  * (targMix     - sMix);
  sLevel   += lam  * (targLevel   - sLevel);
  sDrive   += lam  * (targDrive   - sDrive);
  sRet     += lam  * (targRet     - sRet);
  sTex     += lam  * (targTex     - sTex);
  sSparkle += lam  * (targSparkle - sSparkle);

  sGate0 += lamG * (targG0 - sGate0);
  sGate1 += lamG * (targG1 - sGate1);
  sGate2 += lamG * (targG2 - sGate2);

  kTime    = sTime;
  kFB      = sFB;
  kMix     = sMix;
  kLevel   = sLevel;
  kDrive   = sDrive;
  kRet     = sRet;
  kTex     = sTex;
  kSparkle = sSparkle;

  kGate0 = sGate0;
  kGate1 = sGate1;
  kGate2 = sGate2;
}