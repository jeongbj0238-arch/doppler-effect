/* ============================================================
   도플러 효과 시뮬레이터
   교과서: (동아출판) 역학과 에너지 pp.106~111 「03 도플러 효과」
   성취기준: [12역학03-03]

   1 음원 이동    음원 앞쪽은 파장이 짧아지고 뒤쪽은 길어진다 (p.108 그림 III-15)
   2 관찰자 이동  파장은 그대로, 관찰자가 받는 소리의 속력이 달라진다 (p.109 그림 III-16)
   3 같은 속력    같은 속력이라도 누가 움직이느냐에 따라 진동수가 다르다 (p.109 예제)
   4 반사파       표적에 부딪혀 되돌아온 소리로 속력을 잰다 (pp.106·110·111)

   ※ 관찰자가 듣는 진동수는 공식으로 넣지 않는다. 마루가 관찰자에게 닿은 시각을
      기록해 그 간격으로 잰다. 공식값은 비교용으로 따로 계산한다.
   ※ 시뮬레이션 시계 state.tau 는 실제 시간(초)이다. 화면에서는 slow배 느리게 흐른다.
      그래서 화면 속도를 바꿔도 파면 모양과 측정값은 변하지 않는다.
   ※ 모든 물체는 한 직선(진행 방향) 위에 있다. 교과서 그림과 같다.
   ============================================================ */

(() => {
  "use strict";

  /* ---------------------------------------------------------
     캔버스에 직접 그리는 색.
     CSS의 --hi, --lo 등과는 별개의 하드코딩 상수다.
     색을 바꿀 때는 doppler-effect.css와 여기를 함께 고쳐야 한다.
     --------------------------------------------------------- */
  const COLOR_STAGE = "#ffffff";
  const COLOR_RING  = "rgba(23, 23, 23, 0.5)";
  const COLOR_ECHO  = "rgba(121, 40, 202, 0.8)";   // 되돌아오는 파면
  const COLOR_AXIS  = "#e6e6e6";
  const COLOR_GRID  = "#f0f0f0";
  const COLOR_INK   = "#171717";
  const COLOR_BODY  = "#4d4d4d";
  const COLOR_MUTE  = "#8f8f8f";
  const COLOR_REF   = "#dcdcdc";
  const COLOR_HI    = "#0070f3";   // 높아짐 — 파장이 짧아진 쪽
  const COLOR_LO    = "#ee0000";   // 낮아짐 — 파장이 길어진 쪽

  const V_SOUND = 340;                  // 음속 (m/s), 고정
  const V_MAX = 0.9 * V_SOUND;          // 움직이는 물체의 속력 상한 — 끌 때도 이보다 빨라지지 않는다
  const WORLD_W = 12;                   // 무대 가로 폭 (m)
  const EDGE = 5.6;                     // 물체가 멈추는 끝 (가운데에서 ±m)
  // 관찰자를 끝에서 떨어뜨려 둬야 음원이 지나친 뒤에도 한참 더 가며 낮아진 소리를 들려준다
  const OBS_X = 3.2;                    // 탭 1 관찰자 A·B 위치 (±m)
  const LANE_X = 4.5;                   // 탭 3 두 줄의 출발 위치 (±m)
  const LANE_STOP = 1.0;                // 탭 3 — 다가갈 때 이 거리에서 멈춘다
  const GAP = 1.2;                      // 탭 4 — 박쥐와 표적이 이보다 가까워지지 않는다
  const ARC_HALF = (50 * Math.PI) / 180;   // 탭 4 — 파면을 부채꼴로 그리는 반각
  const HEARING_MAX = 20000;            // 사람이 들을 수 있는 가장 높은 소리 (Hz)
  const STRIP_PERIODS = 5;              // 파형 띠에 담는 원래 소리의 주기 수
  const SAME_TOL = 5e-4;                // 이보다 덜 다르면 "같다"
  const MOVE_EPS = 0.05;                // 이보다 느리면 "정지" (m/s)
  const FLASH_SEC = 0.22;               // 마루가 닿을 때 깜빡이는 시간 (화면 초)
  const VOLUME = 0.07;
  const EXAMPLE = { f: 500, v: 20 };    // 교과서 p.109 예제
  const Q3 = { f: 31500, v: 4 };        // 확인 문제 3 (p.111)
  const TARGET_NAME = { tree: "나무", bird: "새", wall: "벽" };

  const $ = (id) => document.getElementById(id);
  const clamp = (x, a, b) => Math.min(b, Math.max(a, x));
  const fmtNum = (x) => {
    const r = Math.round(x * 10) / 10;
    return Number.isInteger(r) ? String(r) : r.toFixed(1);
  };

  const state = {
    tab: 1,
    phase: "idle",      // idle · running · paused
    tau: 0,             // 실제 시간 (s)
    slow: 300,
    f: 500,
    speed: { 1: 170, 2: 170, 3: 170, 4: 20 },   // 탭마다 따로 기억 (탭 3은 부호 있음: + 다가옴)
    dir: 0,             // 버튼으로 정한 방향 −1 · 0 · +1
    drag: null,         // 끄는 동안 { body, dx, targetX, released }
    showLambda: true,
    showRef: true,
  };

  let canvas = null;
  let graph = null;
  let cardEls = [];
  let models = null;

  /* ---------------------------------------------------------
     물체 · 받는 쪽 · 세계
     세계 하나 = 소리를 내는 물체 하나 + 그 소리를 받는 것들 + 퍼져 나가는 마루
     --------------------------------------------------------- */
  const body = (x) => ({ x, x0: x, v: 0, facing: 1 });
  const receiver = (b, listen, reflect = false) =>
    ({ body: b, listen, reflect, arrivals: [], flashAt: -1, lastEcho: null });
  const world = (emitter, receivers) =>
    ({ emitter, receivers, crests: [], nextEmit: 0, lastEmit: null });

  // 프레임 안에서의 위치 (프레임 처음 x0 → 끝 x 를 선형 보간)
  const lerpX = (b, t0, t1, t) => (t1 > t0 ? b.x0 + (b.x - b.x0) * ((t - t0) / (t1 - t0)) : b.x);

  function addCrest(w, c) {
    c.passed = w.receivers.map(() => false);
    w.crests.push(c);
  }

  // 마루는 프레임 경계가 아니라 정확한 시각에 낸다
  function emit(w, t0, t1) {
    const b = w.emitter;
    while (w.nextEmit <= t1) {
      const te = w.nextEmit;
      const xe = lerpX(b, t0, t1, te);
      const prev = w.lastEmit;
      // 직전 마루 이후 음원이 실제로 움직인 평균 속도와 그 사이의 주기.
      // 관찰자가 재는 도착 간격이 정확히 이 두 값으로 정해진다.
      addCrest(w, {
        kind: "out", te, xe,
        vAvg: prev ? (xe - prev.xe) / (te - prev.te) : b.v,
        fe: prev ? 1 / (te - prev.te) : state.f,
      });
      w.lastEmit = { te, xe };
      w.nextEmit = te + 1 / state.f;
    }
  }

  // 마루가 받는 쪽에 닿은 시각을 프레임 안에서 보간해 기록한다 (받는 쪽이 움직여도 된다)
  function detect(w, t0, t1) {
    const now = performance.now() / 1000;
    const n = w.crests.length;
    w.receivers.forEach((rc, i) => {
      const b = rc.body;
      for (let k = 0; k < n; k++) {
        const c = w.crests[k];
        if (c.passed[i] || c.kind !== rc.listen) continue;
        const g1 = V_SOUND * (t1 - c.te) - Math.abs(b.x - c.xe);
        if (g1 < 0) continue;
        const ts = Math.max(t0, c.te);
        const gs = V_SOUND * (ts - c.te) - Math.abs(lerpX(b, t0, t1, ts) - c.xe);
        const ta = gs >= 0 ? ts : ts + (t1 - ts) * (-gs / (g1 - gs));
        const xo = lerpX(b, t0, t1, ta);
        c.passed[i] = true;
        rc.arrivals.push({ t: ta, xo, xc: c.xe, vsT: c.vAvg * Math.sign(xo - c.xe), fe: c.fe });
        rc.flashAt = now;
        if (rc.reflect) reflect(w, rc, ta, xo);
      }
      if (rc.arrivals.length > 600) rc.arrivals.splice(0, rc.arrivals.length - 600);
    });
  }

  // 표적은 받은 마루를 그 자리에서 다시 내보낸다 — 움직이는 음원이 되는 셈
  function reflect(w, rc, ta, xo) {
    const prev = rc.lastEcho;
    addCrest(w, {
      kind: "echo", te: ta, xe: xo,
      vAvg: prev ? (xo - prev.xe) / (ta - prev.te) : rc.body.v,
      fe: prev ? 1 / (ta - prev.te) : state.f,
    });
    rc.lastEcho = { te: ta, xe: xo };
  }

  /* 탭 3 — 시작하는 순간을 "이미 한동안 그렇게 움직이던 상황"으로 채운다.
     둘 다 등속이라 지나간 마루와 그 도착 시각을 식으로 정확히 만들 수 있다.
     받는 쪽이 마루 중심을 넘어가지 않는 범위(since 이후)에서만 만든다. */
  function prefill(w, vE, vR, since) {
    const f = state.f;
    const rc = w.receivers[0];
    const xr0 = rc.body.x;
    w.crests = [];
    for (let k = Math.ceil(since * f); k <= -1; k++) {
      const te = k / f;
      const c = { kind: "out", te, xe: w.emitter.x + vE * te, vAvg: vE, fe: f, passed: [false] };
      const s = Math.sign(xr0 - c.xe);
      const ta = (V_SOUND * te + s * (xr0 - c.xe)) / (V_SOUND - s * vR);
      if (ta <= 0) {
        const xo = xr0 + vR * ta;
        c.passed[0] = true;
        rc.arrivals.push({ t: ta, xo, xc: c.xe, vsT: vE * Math.sign(xo - c.xe), fe: f });
      }
      w.crests.push(c);
    }
    const last = w.crests[w.crests.length - 1];
    w.lastEmit = last ? { te: last.te, xe: last.xe } : null;
    w.nextEmit = 0;
  }

  function cleanup(w, hWorld) {
    w.crests = w.crests.filter((c) => {
      const r = V_SOUND * (state.tau - c.te);
      const far = Math.max(Math.abs(c.xe - WORLD_W / 2), Math.abs(c.xe + WORLD_W / 2));
      if (r < Math.hypot(far, hWorld / 2) + 0.5) return true;
      return w.receivers.some((rc, i) => rc.listen === c.kind && !c.passed[i]);
    });
  }

  /* 마지막 두 마루의 도착 간격으로 잰 진동수와, 같은 조건의 공식값.
     vsT = 음원이 받는 쪽으로 다가온 속력, voT = 받는 쪽이 음원 쪽으로 다가간 속력 */
  function measure(rc) {
    const a = rc.arrivals;
    if (a.length < 2) return null;
    const k = a[a.length - 1];
    const p = a[a.length - 2];
    const dt = k.t - p.t;
    const voT = ((k.xo - p.xo) / dt) * Math.sign(k.xc - k.xo);
    return {
      fHeard: 1 / dt,
      fFormula: ((V_SOUND + voT) / (V_SOUND - k.vsT)) * k.fe,
      voT, vsT: k.vsT, fe: k.fe,
    };
  }

  /* 받는 쪽 양옆에서 가장 가까운 마루 두 개 — 그 사이가 받는 쪽에서의 파장 */
  function localLambda(w, rc) {
    const x = rc.body.x;
    let left = -Infinity;
    let right = Infinity;
    for (const c of w.crests) {
      if (c.kind !== rc.listen) continue;
      const r = V_SOUND * (state.tau - c.te);
      if (r <= 0) continue;
      for (const p of [c.xe - r, c.xe + r]) {
        if (p <= x && p > left) left = p;
        if (p > x && p < right) right = p;
      }
    }
    if (!isFinite(left) || !isFinite(right)) return null;
    return { left, right, lambda: right - left };
  }

  /* 기준보다 높아졌나(hi) 낮아졌나(lo). 파장은 역수로 넣는다. */
  function relation(value, base) {
    if (value > base * (1 + SAME_TOL)) return "hi";
    if (value < base * (1 - SAME_TOL)) return "lo";
    return "same";
  }
  const relOfSpeed = (u) => (Math.abs(u) < MOVE_EPS ? "same" : u > 0 ? "hi" : "lo");
  const colorOf = (rel) => (rel === "hi" ? COLOR_HI : rel === "lo" ? COLOR_LO : COLOR_INK);
  const relClass = (rel) => (rel === "hi" ? "is-hi" : rel === "lo" ? "is-lo" : "");
  const primeOf = (rel) => (rel === "hi" ? "′" : rel === "lo" ? "″" : "");

  /* ---------------------------------------------------------
     움직이기 — 버튼(방향 × 속력)과 끌기
     --------------------------------------------------------- */
  function setPos(b, x, dTau, smooth) {
    const vNow = (x - b.x) / dTau;
    b.x = x;
    // 끌 때는 손 떨림이 그대로 보이지 않게 표시용 속력만 부드럽게 한다
    b.v = smooth ? b.v + (vNow - b.v) * 0.3 : vNow;
    if (Math.abs(vNow) > 1e-9) b.facing = vNow > 0 ? 1 : -1;
  }

  function moveByControl(b, dTau, lo, hi) {
    const d = state.drag && state.drag.body === b ? state.drag : null;
    const isMover = tab().mover === b;
    let x = b.x;
    if (d) {
      const lim = V_MAX * dTau;
      x += clamp(d.targetX - x, -lim, lim);
    } else if (isMover && state.dir !== 0) {
      x += state.dir * state.speed[state.tab] * dTau;
    }
    const xc = clamp(x, lo, hi);
    // 손을 놓아도 놓은 자리까지는 간다 — 상한 속력 때문에 손보다 늦게 따라오기 때문
    if (d && d.released && (Math.abs(d.targetX - xc) < 1e-9 || xc !== x)) state.drag = null;
    if (!d && isMover && state.dir !== 0 && xc !== x) {
      state.dir = 0;
      updateDirButtons();
    }
    setPos(b, xc, dTau, !!d);
  }

  /* ---------------------------------------------------------
     탭 1 · 음원 이동
     --------------------------------------------------------- */
  const T1 = {
    hint: "음원을 끌어서 움직일 수 있다",
    example: "500 Hz 사이렌이 20 m/s로 다가올 때 (p.109)",
    speedLabel: () => "음원 속력",
    setup() {
      this.src = body(0);
      this.A = receiver(body(-OBS_X), "out");
      this.B = receiver(body(OBS_X), "out");
      this.w = world(this.src, [this.A, this.B]);
      this.mover = this.src;
    },
    bodies() { return [this.src, this.A.body, this.B.body]; },
    worlds() { return [this.w]; },
    limitsFor: () => [-EDGE, EDGE],
    draggables() { return [{ body: this.src, hx: 30, top: 26, bottom: 26 }]; },
    step(t0, t1, dTau) {
      moveByControl(this.src, dTau, -EDGE, EDGE);
      emit(this.w, t0, t1);
      detect(this.w, t0, t1);
    },
    render(ctx, W, H) {
      const g = band(W, 0, H);
      drawAxis(ctx, g);
      drawRings(ctx, g, this.w);
      drawReference(ctx, g);
      if (state.showLambda) [this.A, this.B].forEach((rc) => drawLambda(ctx, g, this.w, rc));
      drawPerson(ctx, g, this.A, "A");
      drawPerson(ctx, g, this.B, "B");
      drawVelocity(ctx, g, this.src, 30);
      drawVehicle(ctx, g, this.src);
      return g;
    },
    cards() {
      return [observerCard(this.w, this.A, "관찰자 A"), observerCard(this.w, this.B, "관찰자 B")];
    },
    runExample() {
      setF(EXAMPLE.f);
      setSpeed(EXAMPLE.v);
      resetTab();
      state.dir = 1;
      start();
      toast("500 Hz 사이렌이 20 m/s로 B에게 다가간다 (p.109 예제)");
    },
  };

  /* ---------------------------------------------------------
     탭 2 · 관찰자 이동
     --------------------------------------------------------- */
  const T2 = {
    hint: "관찰자를 끌어서 움직일 수 있다",
    example: "관찰자가 20 m/s로 500 Hz 사이렌에 다가갈 때 (p.109)",
    speedLabel: () => "관찰자 속력",
    setup() {
      this.src = body(0);
      this.O = receiver(body(4), "out");
      this.w = world(this.src, [this.O]);
      this.mover = this.O.body;
    },
    bodies() { return [this.src, this.O.body]; },
    worlds() { return [this.w]; },
    limitsFor: () => [-EDGE, EDGE],
    draggables() { return [{ body: this.O.body, hx: 18, top: 16, bottom: 36 }]; },
    step(t0, t1, dTau) {
      moveByControl(this.O.body, dTau, -EDGE, EDGE);
      emit(this.w, t0, t1);
      detect(this.w, t0, t1);
    },
    render(ctx, W, H) {
      const g = band(W, 0, H);
      drawAxis(ctx, g);
      drawRings(ctx, g, this.w);
      drawReference(ctx, g);
      if (state.showLambda) drawLambda(ctx, g, this.w, this.O);
      drawVehicle(ctx, g, this.src);
      drawPerson(ctx, g, this.O, "O");
      drawVelocity(ctx, g, this.O.body, 58);
      return g;
    },
    cards() { return [sourceCard("음원 S"), observerCard(this.w, this.O, "관찰자 O", true)]; },
    runExample() {
      setF(EXAMPLE.f);
      setSpeed(EXAMPLE.v);
      resetTab();
      state.dir = -1;
      start();
      toast("관찰자가 20 m/s로 500 Hz 사이렌에 다가간다 (p.109 예제)");
    },
  };

  /* ---------------------------------------------------------
     탭 3 · 같은 속력, 다른 진동수
     위 줄은 음원이, 아래 줄은 관찰자가 같은 속력 u로 움직인다.
     끝까지 가면 저절로 멈춰서 두 값을 나란히 남긴다.
     --------------------------------------------------------- */
  const T3 = {
    hint: "",
    example: "같은 20 m/s — 음원이 다가올 때와 관찰자가 다가갈 때 (p.109)",
    speedLabel: () => "속력 u",
    draggables: null,
    setup() {
      // 다가갈 때는 멀리서, 멀어질 때는 가까이에서 출발한다
      const away = state.speed[3] < 0;
      const l1 = { src: body(away ? LANE_X - LANE_STOP : -LANE_X), obs: receiver(body(LANE_X), "out") };
      const l2 = { src: body(-LANE_X), obs: receiver(body(away ? -LANE_X + LANE_STOP : LANE_X), "out") };
      l1.w = world(l1.src, [l1.obs]);
      l2.w = world(l2.src, [l2.obs]);
      this.l1 = l1;
      this.l2 = l2;
      this.done = false;
      this.mover = null;
    },
    bodies() { return [this.l1.src, this.l1.obs.body, this.l2.src, this.l2.obs.body]; },
    worlds() { return [this.l1.w, this.l2.w]; },
    limitsFor: () => [-EDGE, EDGE],
    // 안 그러면 소리가 9 m를 건너 관찰자에게 닿기까지 화면에서 8초를 기다려야 한다
    prefill() {
      const u = state.speed[3];
      const back = u >= 0
        ? Math.max((2 * LANE_X) / (V_SOUND - u), WORLD_W / V_SOUND)
        : Math.min(LANE_STOP / -u, 0.3);
      const since = -(back + 3 / state.f);
      this.l1.src.v = u;
      this.l2.obs.body.v = -u;
      prefill(this.l1.w, u, 0, since);
      prefill(this.l2.w, 0, -u, since);
    },
    step(t0, t1, dTau) {
      const u = state.speed[3];
      const s1 = this.l1.src;
      const o2 = this.l2.obs.body;
      let x1 = s1.x + u * dTau;   // 위 줄: 음원이 오른쪽 관찰자 쪽으로 (+)
      let x2 = o2.x - u * dTau;   // 아래 줄: 관찰자가 왼쪽 음원 쪽으로 (−)
      if (u > 0) {
        const lim1 = this.l1.obs.body.x - LANE_STOP;
        const lim2 = this.l2.src.x + LANE_STOP;
        if (x1 >= lim1 || x2 <= lim2) this.done = true;
        x1 = Math.min(x1, lim1);
        x2 = Math.max(x2, lim2);
      } else if (u < 0) {
        if (x1 <= -EDGE || x2 >= EDGE) this.done = true;
        x1 = Math.max(x1, -EDGE);
        x2 = Math.min(x2, EDGE);
      }
      setPos(s1, x1, dTau, false);
      setPos(o2, x2, dTau, false);
      // 끝에 닿은 프레임은 덜 움직여서 속력이 작게 계산된다 — 화살표에는 정한 속력을 그대로 둔다
      if (this.done) {
        s1.v = u;
        o2.v = -u;
      }
      emit(this.l1.w, t0, t1);
      detect(this.l1.w, t0, t1);
      emit(this.l2.w, t0, t1);
      detect(this.l2.w, t0, t1);
    },
    render(ctx, W, H) {
      const hb = H / 2;
      [this.l1, this.l2].forEach((L, i) => {
        const g = band(W, i * hb, hb);
        ctx.save();
        ctx.beginPath();
        ctx.rect(0, g.y0, W, hb);
        ctx.clip();
        drawAxis(ctx, g);
        drawRings(ctx, g, L.w);
        if (state.showLambda) drawLambda(ctx, g, L.w, L.obs);
        drawVehicle(ctx, g, L.src);
        drawPerson(ctx, g, L.obs, "O");
        if (i === 0) drawVelocity(ctx, g, L.src, 30);
        else drawVelocity(ctx, g, L.obs.body, 58);
        label(ctx, i === 0 ? "① 음원이 움직인다" : "② 관찰자가 움직인다",
          W - 14, g.y0 + 22, COLOR_INK, 13, "right", "600");
        ctx.restore();
      });
      ctx.fillStyle = "#ebebeb";
      ctx.fillRect(0, Math.round(hb) - 1, W, 1);
      return band(W, 0, hb);
    },
    cards() {
      return [
        observerCard(this.l1.w, this.l1.obs, "① 음원이 움직일 때"),
        observerCard(this.l2.w, this.l2.obs, "② 관찰자가 움직일 때"),
      ];
    },
    runExample() {
      setF(EXAMPLE.f);
      setSpeed(EXAMPLE.v);
      resetTab();
      start();
      toast("같은 20 m/s — 위는 음원이, 아래는 관찰자가 다가간다 (p.109 예제)");
    },
  };

  /* ---------------------------------------------------------
     탭 4 · 반사파로 속력 재기
     박쥐가 소리를 내고, 표적이 그 소리를 받아 되돌려 보낸다.
     도플러 효과가 두 번 일어난다 — 표적이 받을 때(f₁), 박쥐가 받을 때(f₂).
     ⚠ 확인 문제 3(31500 Hz)은 파장이 1 cm라 그대로 그릴 수 없다.
        그림은 설정의 진동수로 그리고, 숫자만 31500 Hz 기준으로 바꿔 보여 준다.
        진동수가 몇이든 f′/f 는 속력에만 달려 있어서 결과는 똑같다.
     --------------------------------------------------------- */
  const T4 = {
    hint: "박쥐와 표적을 끌어서 움직일 수 있다",
    example: "",
    speedLabel() { return this.mover === this.bat.body ? "박쥐 속력" : "표적 속력"; },
    // 박쥐와 표적이 멀면 소리가 갔다 오는 데만 화면에서 15초가 넘게 걸린다 — 6 m 안팎으로 둔다
    setup() {
      this.bat = receiver(body(-4), "echo");
      this.target = receiver(body(1.5), "out", true);
      this.w = world(this.bat.body, [this.target, this.bat]);
      this.kind = "tree";
      this.fNom = null;
      this.mover = this.target.body;
    },
    bodies() { return [this.bat.body, this.target.body]; },
    worlds() { return [this.w]; },
    limitsFor(b) {
      return b === this.bat.body ? [-EDGE, this.target.body.x - GAP] : [this.bat.body.x + GAP, EDGE];
    },
    draggables() {
      const t = this.kind === "wall" ? { hx: 14, top: 48, bottom: 48 } : { hx: 22, top: 20, bottom: 30 };
      return [{ body: this.bat.body, hx: 28, top: 18, bottom: 18 }, { body: this.target.body, ...t }];
    },
    step(t0, t1, dTau) {
      moveByControl(this.bat.body, dTau, ...this.limitsFor(this.bat.body));
      moveByControl(this.target.body, dTau, ...this.limitsFor(this.target.body));
      if (this.kind !== "bird" && Math.abs(this.target.body.v) > MOVE_EPS) this.kind = "bird";
      emit(this.w, t0, t1);
      detect(this.w, t0, t1);
    },
    render(ctx, W, H) {
      const g = band(W, 0, H);
      const xb = this.bat.body.x;
      const xt = this.target.body.x;
      drawAxis(ctx, g);
      drawArcs(ctx, g, this.w, "out", COLOR_RING, 1, -Infinity, xt);
      drawArcs(ctx, g, this.w, "echo", COLOR_ECHO, -1, xb, Infinity);
      drawEchoLegend(ctx, g);
      drawFlash(ctx, g, this.target, this.kind === "wall" ? 12 : 18);
      drawFlash(ctx, g, this.bat, 20);
      drawTarget(ctx, g, this.target.body, this.kind);
      drawBat(ctx, g, this.bat.body);
      drawVelocity(ctx, g, this.bat.body, 34);
      drawVelocity(ctx, g, this.target.body, this.kind === "wall" ? 60 : 34);
      label(ctx, "박쥐", g.px(xb), g.axisY + 40, COLOR_INK, 13, "center", "600");
      label(ctx, TARGET_NAME[this.kind], g.px(xt), g.axisY + (this.kind === "wall" ? 68 : 50),
        COLOR_INK, 13, "center", "600");
      return g;
    },
    cards() {
      const k = (this.fNom || state.f) / state.f;
      return [batCard(this, k), targetCard(this, k)];
    },
    preset(kind) {
      resetTab();
      const tb = this.target.body;
      if (kind === "near") {
        this.kind = "bird";
        tb.x = tb.x0 = 2.5;
        tb.facing = -1;
        state.speed[4] = 20;
        state.dir = -1;
      } else if (kind === "far") {
        this.kind = "bird";
        tb.x = tb.x0 = -1;
        state.speed[4] = 20;
        state.dir = 1;
      } else if (kind === "q3") {
        this.kind = "wall";
        this.fNom = Q3.f;
        tb.x = tb.x0 = 2;
        this.mover = this.bat.body;
        state.speed[4] = Q3.v;
        state.dir = 1;
      }
      applyTabUI();
      start();
      toast({
        tree: "정지한 나무에 소리를 보낸다 (그림 III-14 가)",
        near: "다가오는 새에 소리를 보낸다 (그림 III-14 나)",
        far: "멀어지는 새에 소리를 보낸다 (그림 III-14 나)",
        q3: "31500 Hz를 내는 박쥐가 4 m/s로 벽에 다가간다 (p.111 확인 문제 3)",
      }[kind]);
    },
  };

  const TABS = { 1: T1, 2: T2, 3: T3, 4: T4 };
  const tab = () => TABS[state.tab];

  /* ---------------------------------------------------------
     카드 내용
     --------------------------------------------------------- */
  function motionText(m) {
    const s = Math.abs(m.vsT) > MOVE_EPS;
    const o = Math.abs(m.voT) > MOVE_EPS;
    if (s && !o) return m.vsT > 0 ? "다가오는 음원" : "멀어지는 음원";
    if (o && !s) return m.voT > 0 ? "음원으로 다가감" : "음원에서 멀어짐";
    if (s && o) return "둘 다 움직임";
    return "정지";
  }

  function formulaText(m, scale = 1) {
    const s = Math.abs(m.vsT) > MOVE_EPS;
    const o = Math.abs(m.voT) > MOVE_EPS;
    const f = fmtNum(m.fe * scale);
    if (!s && !o) return `정지 → 원래 진동수 ${f} Hz 그대로`;
    const num = o ? `(${V_SOUND} ${m.voT > 0 ? "+" : "−"} ${fmtNum(Math.abs(m.voT))})` : `${V_SOUND}`;
    const den = s ? `(${V_SOUND} ${m.vsT > 0 ? "−" : "+"} ${fmtNum(Math.abs(m.vsT))})` : `${V_SOUND}`;
    return `공식  ${num} ÷ ${den} × ${f} = ${(m.fFormula * scale).toFixed(2)}`;
  }

  const waitText = (idleText, runText) => (state.phase === "idle" ? idleText : runText);

  // withPeriod — 탭 2: 관찰자가 움직일 때 짧아지는 것은 파장이 아니라 주기라는 것을 보여 준다
  function observerCard(w, rc, name, withPeriod = false) {
    const m = measure(rc);
    const lam = localLambda(w, rc);
    const fRel = m ? relation(m.fHeard, m.fe) : "same";
    const vRel = m ? relation(V_SOUND + m.voT, V_SOUND) : "same";
    const lRel = lam ? relation(V_SOUND / state.f / lam.lambda, 1) : "same";
    const rows = [
      { k: "v′", v: `${fmtNum(V_SOUND + (m ? m.voT : 0))} m/s`, rel: vRel },
      { k: "λ" + primeOf(lRel), v: lam ? `${lam.lambda.toFixed(3)} m` : "–", rel: lRel },
    ];
    if (withPeriod) rows.push({ k: "T" + primeOf(fRel), v: m ? `${(1000 / m.fHeard).toFixed(3)} ms` : "–", rel: fRel });
    return {
      name,
      tag: m ? { text: motionText(m), rel: fRel } : null,
      fSym: "f" + primeOf(fRel),
      fVal: m ? m.fHeard.toFixed(2) : null,
      fRel,
      rows,
      strip: { arrivals: rc.arrivals, color: colorOf(fRel) },
      formula: m ? formulaText(m) : waitText("시작을 누르면 음파가 나온다", "아직 소리가 닿지 않았다"),
      audioHz: m ? m.fHeard : null,
      siren: m ? m.fHeard / m.fe : null,
    };
  }

  function sourceCard(name) {
    return {
      name,
      tag: { text: "정지", rel: "same" },
      fSym: "f",
      fVal: state.f.toFixed(2),
      fRel: "same",
      rows: [
        { k: "v", v: `${V_SOUND} m/s`, rel: "same" },
        { k: "λ", v: `${(V_SOUND / state.f).toFixed(3)} m`, rel: "same" },
        { k: "T", v: `${(1000 / state.f).toFixed(3)} ms`, rel: "same" },
      ],
      strip: { source: true },
      formula: "음원이 내는 소리 · 어느 쪽으로나 파장이 같다",
      audioHz: state.f,
      siren: 1,
    };
  }

  function batCard(T, k) {
    const m = measure(T.bat);
    const f0 = T.fNom || state.f;
    const base = {
      name: "박쥐",
      fSym: "f₂",
      strip: { arrivals: T.bat.arrivals, color: COLOR_INK },
    };
    if (!m) {
      return {
        ...base, tag: null, fVal: null, fRel: "same",
        rows: [{ k: "보낸 f", v: `${fmtNum(f0)} Hz`, rel: "same" }, { k: "잰 속력", v: "–", rel: "same" }],
        formula: waitText("시작을 누르면 소리를 보낸다", "반사파가 아직 돌아오지 않았다"),
        audioHz: null,
      };
    }
    const f2 = m.fHeard * k;
    const fRel = relation(m.fHeard, state.f);
    // 반사파 진동수로 거꾸로 구한 속력 (+ 가까워짐) — f₂ = (v+u)/(v−u)·f 를 u에 대해 푼 것
    const u = (V_SOUND * (f2 - f0)) / (f2 + f0);
    const uRel = relOfSpeed(u);
    return {
      ...base,
      tag: { text: uRel === "same" ? "거리 그대로" : u > 0 ? "가까워지는 중" : "멀어지는 중", rel: uRel },
      fVal: f2.toFixed(2),
      fRel,
      rows: [
        { k: "보낸 f", v: `${fmtNum(f0)} Hz`, rel: "same" },
        { k: "잰 속력", v: `${fmtNum(Math.abs(u))} m/s`, rel: uRel },
      ],
      strip: { arrivals: T.bat.arrivals, color: colorOf(fRel) },
      formula: `속력 = 340 × (${f2.toFixed(1)} − ${fmtNum(f0)}) ÷ (${f2.toFixed(1)} + ${fmtNum(f0)}) = ${fmtNum(u).replace("-", "−")}`,
      audioHz: f2,
    };
  }

  function targetCard(T, k) {
    const m = measure(T.target);
    const tb = T.target.body;
    const bb = T.bat.body;
    // 서로 가까워지는 속력 (+) — 박쥐와 표적 중 누가 움직여도 같다
    const close = tb.v * Math.sign(bb.x - tb.x) + bb.v * Math.sign(tb.x - bb.x);
    const cRel = relOfSpeed(close);
    const fRel = m ? relation(m.fHeard, m.fe) : "same";
    return {
      name: `표적 · ${TARGET_NAME[T.kind]}`,
      tag: { text: cRel === "same" ? "거리 그대로" : close > 0 ? "가까워지는 중" : "멀어지는 중", rel: cRel },
      fSym: "f₁",
      fVal: m ? (m.fHeard * k).toFixed(2) : null,
      fRel,
      rows: [
        { k: "실제 속력", v: `${fmtNum(Math.abs(close))} m/s`, rel: cRel },
        { k: "v′", v: m ? `${fmtNum(V_SOUND + m.voT)} m/s` : "–", rel: m ? relation(V_SOUND + m.voT, V_SOUND) : "same" },
      ],
      strip: { arrivals: T.target.arrivals, color: colorOf(fRel) },
      formula: m ? formulaText(m, k) : waitText("시작을 누르면 소리를 보낸다", "아직 소리가 닿지 않았다"),
      audioHz: m ? m.fHeard * k : null,
    };
  }

  function applyCard(el, m) {
    el.name.textContent = m.name;
    el.tag.textContent = m.tag ? m.tag.text : "";
    el.tag.className = "obs-tag " + (m.tag ? relClass(m.tag.rel) : "");
    el.fbox.className = "obs-f " + (m.fVal == null ? "is-empty" : relClass(m.fRel));
    el.fsym.textContent = m.fSym;
    el.f.textContent = m.fVal == null ? "–" : m.fVal;
    el.row3.classList.toggle("hidden", m.rows.length < 3);
    m.rows.forEach((r, i) => {
      el.k[i].textContent = r.k;
      el.k[i].className = relClass(r.rel);
      el.v[i].textContent = r.v;
      el.v[i].className = relClass(r.rel);
    });
    el.form.textContent = m.formula;
    el.form.title = m.formula;
    el.spk.setAttribute("aria-label", `${m.name} 소리 켜기`);
  }

  function applyCards() {
    if (models) cardEls.forEach((el, i) => applyCard(el, models[i]));
  }

  /* ---------------------------------------------------------
     그리기 — 공용
     --------------------------------------------------------- */
  function band(W, y0, h) {
    const ppm = W / WORLD_W;
    return { w: W, y0, h, ppm, axisY: Math.round(y0 + h * 0.52), hWorld: h / ppm, px: (x) => W / 2 + x * ppm };
  }

  function roundRect(ctx, x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  function label(ctx, text, x, y, color, size = 12, align = "center", weight = "500", mono = false) {
    ctx.save();
    ctx.fillStyle = color;
    ctx.font = `${weight} ${size}px ${mono ? "'Geist Mono', monospace" : "Geist, 'Malgun Gothic', sans-serif"}`;
    ctx.textAlign = align;
    ctx.fillText(text, x, y);
    ctx.restore();
  }

  function drawAxis(ctx, g) {
    ctx.strokeStyle = COLOR_AXIS;
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(0, g.axisY + 0.5);
    ctx.lineTo(g.w, g.axisY + 0.5);
    ctx.stroke();
  }

  function drawRings(ctx, g, w) {
    ctx.strokeStyle = COLOR_RING;
    ctx.lineWidth = 1.75;
    // 원마다 따로 그어야 마루가 몰린 곳이 진하게 겹쳐 보인다
    for (const c of w.crests) {
      if (c.kind !== "out") continue;
      const r = V_SOUND * (state.tau - c.te) * g.ppm;
      if (r < 1) continue;
      ctx.beginPath();
      ctx.arc(g.px(c.xe), g.axisY, r, 0, Math.PI * 2);
      ctx.stroke();
    }
  }

  // 탭 4 — 박쥐 그림처럼 부채꼴로. 나가는 파면은 표적 앞까지, 되돌아오는 파면은 박쥐 앞까지만.
  function drawArcs(ctx, g, w, kind, color, dir, xMin, xMax) {
    const a0 = dir > 0 ? -ARC_HALF : Math.PI - ARC_HALF;
    const a1 = dir > 0 ? ARC_HALF : Math.PI + ARC_HALF;
    const left = isFinite(xMin) ? g.px(xMin) : 0;
    const right = isFinite(xMax) ? g.px(xMax) : g.w;
    ctx.save();
    ctx.beginPath();
    ctx.rect(left, g.y0, Math.max(0, right - left), g.h);
    ctx.clip();
    ctx.strokeStyle = color;
    ctx.lineWidth = 1.75;
    for (const c of w.crests) {
      if (c.kind !== kind) continue;
      const r = V_SOUND * (state.tau - c.te) * g.ppm;
      if (r < 1) continue;
      ctx.beginPath();
      ctx.arc(g.px(c.xe), g.axisY, r, a0, a1);
      ctx.stroke();
    }
    ctx.restore();
  }

  function drawReference(ctx, g) {
    const lam0 = V_SOUND / state.f;
    const xR = g.w - 18;
    const xL = xR - lam0 * g.ppm;
    const y = g.y0 + 38;
    ctx.save();
    ctx.strokeStyle = COLOR_MUTE;
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    ctx.moveTo(xL, y); ctx.lineTo(xR, y);
    ctx.moveTo(xL, y - 5); ctx.lineTo(xL, y + 5);
    ctx.moveTo(xR, y - 5); ctx.lineTo(xR, y + 5);
    ctx.stroke();
    ctx.restore();
    label(ctx, `정지한 음원의 파장 λ = ${lam0.toFixed(3)} m`, xR, g.y0 + 24, COLOR_MUTE, 12, "right");
  }

  function drawEchoLegend(ctx, g) {
    const xR = g.w - 18;
    [["나가는 소리", COLOR_RING], ["되돌아오는 소리", COLOR_ECHO]].forEach(([t, c], i) => {
      const y = g.y0 + 24 + i * 19;
      ctx.strokeStyle = c;
      ctx.lineWidth = 2.5;
      ctx.beginPath();
      ctx.moveTo(xR - 24, y - 4);
      ctx.lineTo(xR, y - 4);
      ctx.stroke();
      label(ctx, t, xR - 32, y, COLOR_BODY, 12, "right");
    });
  }

  function drawLambda(ctx, g, w, rc) {
    const lam = localLambda(w, rc);
    if (!lam) return;
    const rel = relation(V_SOUND / state.f / lam.lambda, 1);
    const col = colorOf(rel);
    const x1 = g.px(lam.left);
    const x2 = g.px(lam.right);
    const y = g.axisY - 30;
    ctx.save();
    ctx.strokeStyle = col;
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(x1, y); ctx.lineTo(x2, y);
    ctx.moveTo(x1, y - 6); ctx.lineTo(x1, y + 6);
    ctx.moveTo(x2, y - 6); ctx.lineTo(x2, y + 6);
    ctx.stroke();
    ctx.lineWidth = 1;
    ctx.setLineDash([2, 3]);
    ctx.beginPath();
    ctx.moveTo(x1, y + 6); ctx.lineTo(x1, g.axisY);
    ctx.moveTo(x2, y + 6); ctx.lineTo(x2, g.axisY);
    ctx.stroke();
    ctx.restore();
    label(ctx, "λ" + primeOf(rel), (x1 + x2) / 2, y - 9, col, 14, "center", "600");
  }

  // 마루가 닿을 때마다 동그랗게 깜빡인다 — 깜빡이는 빠르기가 곧 진동수
  function drawFlash(ctx, g, rc, r0) {
    const age = performance.now() / 1000 - rc.flashAt;
    if (rc.flashAt < 0 || age >= FLASH_SEC) return;
    const m = measure(rc);
    const k = age / FLASH_SEC;
    ctx.save();
    ctx.globalAlpha = 1 - k;
    ctx.strokeStyle = m ? colorOf(relation(m.fHeard, m.fe)) : COLOR_INK;
    ctx.lineWidth = 2.5;
    ctx.beginPath();
    ctx.arc(g.px(rc.body.x), g.axisY, r0 + 9 * k, 0, Math.PI * 2);
    ctx.stroke();
    ctx.restore();
  }

  function drawPerson(ctx, g, rc, name) {
    const x = g.px(rc.body.x);
    const y = g.axisY;
    drawFlash(ctx, g, rc, 10);
    ctx.fillStyle = COLOR_BODY;
    roundRect(ctx, x - 6, y + 10, 12, 22, 5);
    ctx.fill();
    // 머리를 진행 방향 직선 위에 둔다 — 마루가 머리에 닿는 순간이 "도착"
    ctx.fillStyle = "#ffffff";
    ctx.strokeStyle = COLOR_INK;
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.arc(x, y, 7, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();
    label(ctx, name, x, y + 50, COLOR_INK, 14, "center", "600");
  }

  function drawVelocity(ctx, g, b, yOff) {
    const sp = Math.abs(b.v);
    if (state.phase === "idle" || sp <= 0.5) return;
    const x = g.px(b.x);
    const d = b.v > 0 ? 1 : -1;
    const len = 18 + 62 * Math.min(1, sp / V_MAX);
    const ay = g.axisY - yOff;
    const xa = x - (d * len) / 2;
    const xb = x + (d * len) / 2;
    ctx.save();
    ctx.strokeStyle = COLOR_INK;
    ctx.fillStyle = COLOR_INK;
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(xa, ay);
    ctx.lineTo(xb - d * 6, ay);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(xb, ay);
    ctx.lineTo(xb - d * 9, ay - 5);
    ctx.lineTo(xb - d * 9, ay + 5);
    ctx.closePath();
    ctx.fill();
    ctx.restore();
    label(ctx, `${Math.round(sp)} m/s`, x, ay - 11, COLOR_INK, 12, "center", "500", true);
  }

  // 구급차 — 앞이 진행 방향을 보게 뒤집는다
  function drawVehicle(ctx, g, b) {
    ctx.save();
    ctx.translate(g.px(b.x), g.axisY);
    ctx.scale(b.facing, 1);
    ctx.fillStyle = "#ffffff";
    ctx.strokeStyle = COLOR_INK;
    ctx.lineWidth = 1.6;
    roundRect(ctx, -22, -11, 44, 20, 4);
    ctx.fill();
    ctx.stroke();
    ctx.fillStyle = COLOR_INK;
    roundRect(ctx, 11, -7, 8, 7, 1.5);
    ctx.fill();
    ctx.fillRect(-9.5, -3.3, 9, 2.6);
    ctx.fillRect(-6.3, -6.5, 2.6, 9);
    roundRect(ctx, -4, -15, 8, 4, 1.5);
    ctx.fill();
    ctx.beginPath();
    ctx.arc(-12, 10, 4, 0, Math.PI * 2);
    ctx.fill();
    ctx.beginPath();
    ctx.arc(12, 10, 4, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();
  }

  function drawBat(ctx, g, b) {
    ctx.save();
    ctx.translate(g.px(b.x), g.axisY);
    ctx.fillStyle = COLOR_INK;
    ctx.beginPath();
    ctx.moveTo(0, -3);
    ctx.quadraticCurveTo(-11, -13, -25, -7);
    ctx.quadraticCurveTo(-22, -1, -20, 4);
    ctx.quadraticCurveTo(-17, 0, -13, 4);
    ctx.quadraticCurveTo(-9, 0, -5, 5);
    ctx.lineTo(5, 5);
    ctx.quadraticCurveTo(9, 0, 13, 4);
    ctx.quadraticCurveTo(17, 0, 20, 4);
    ctx.quadraticCurveTo(22, -1, 25, -7);
    ctx.quadraticCurveTo(11, -13, 0, -3);
    ctx.closePath();
    ctx.fill();
    ctx.beginPath();
    ctx.ellipse(0, 1, 4.5, 7.5, 0, 0, Math.PI * 2);
    ctx.fill();
    ctx.beginPath();
    ctx.moveTo(-4, -4); ctx.lineTo(-3, -11); ctx.lineTo(-0.8, -5.5); ctx.closePath();
    ctx.moveTo(4, -4); ctx.lineTo(3, -11); ctx.lineTo(0.8, -5.5); ctx.closePath();
    ctx.fill();
    ctx.restore();
  }

  function drawTarget(ctx, g, b, kind) {
    const x = g.px(b.x);
    const y = g.axisY;
    ctx.save();
    if (kind === "tree") {
      ctx.fillStyle = COLOR_BODY;
      ctx.fillRect(x - 3, y + 6, 6, 28);
      // 잎 덩어리 — 원 세 개의 테두리를 먼저 긋고 안쪽을 덮어 바깥선만 남긴다
      const leaves = [[-8, 3, 10], [8, 3, 10], [0, -7, 12]];
      ctx.fillStyle = COLOR_INK;
      leaves.forEach(([dx, dy, r]) => {
        ctx.beginPath();
        ctx.arc(x + dx, y + dy, r + 2, 0, Math.PI * 2);
        ctx.fill();
      });
      ctx.fillStyle = "#ececec";
      leaves.forEach(([dx, dy, r]) => {
        ctx.beginPath();
        ctx.arc(x + dx, y + dy, r, 0, Math.PI * 2);
        ctx.fill();
      });
    } else if (kind === "wall") {
      const w = 14;
      const h = 92;
      ctx.fillStyle = "#f2f2f2";
      ctx.strokeStyle = COLOR_INK;
      ctx.lineWidth = 1.6;
      ctx.fillRect(x - w / 2, y - h / 2, w, h);
      ctx.strokeRect(x - w / 2, y - h / 2, w, h);
      ctx.strokeStyle = "#c8c8c8";
      ctx.lineWidth = 1;
      ctx.beginPath();
      for (let yy = y - h / 2 + 11.5; yy < y + h / 2 - 1; yy += 11.5) {
        ctx.moveTo(x - w / 2 + 1, yy);
        ctx.lineTo(x + w / 2 - 1, yy);
      }
      ctx.stroke();
    } else {
      ctx.translate(x, y);
      ctx.scale(b.facing, 1);
      ctx.fillStyle = COLOR_INK;
      ctx.beginPath(); ctx.ellipse(0, 0, 10, 6, 0, 0, Math.PI * 2); ctx.fill();
      ctx.beginPath(); ctx.arc(9, -4, 4.5, 0, Math.PI * 2); ctx.fill();
      ctx.beginPath(); ctx.moveTo(13, -5); ctx.lineTo(19, -3); ctx.lineTo(13, -1.5); ctx.closePath(); ctx.fill();
      ctx.beginPath(); ctx.moveTo(-9, -1); ctx.lineTo(-17, -6); ctx.lineTo(-17, 4); ctx.closePath(); ctx.fill();
      ctx.fillStyle = COLOR_BODY;
      ctx.beginPath(); ctx.moveTo(-5, -3); ctx.lineTo(4, -3); ctx.lineTo(-8, -17); ctx.closePath(); ctx.fill();
    }
    ctx.restore();
  }

  /* 받은 파형 — 도착 시각 사이를 한 주기로 채운다 */
  function drawStrip(cv, s) {
    const { w, h, ctx } = SimUtils.fitCanvas(cv);
    ctx.clearRect(0, 0, w, h);
    const mid = Math.round(h / 2) + 0.5;
    const amp = h * 0.38;
    const win = STRIP_PERIODS / state.f;
    const tStart = state.tau - win;

    ctx.strokeStyle = COLOR_AXIS;
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(0, mid);
    ctx.lineTo(w, mid);
    ctx.stroke();

    const sine = (color, width) => {
      ctx.strokeStyle = color;
      ctx.lineWidth = width;
      ctx.beginPath();
      for (let px = 0; px <= w; px++) {
        const t = tStart + (px / w) * win;
        const y = mid - amp * Math.cos(2 * Math.PI * state.f * t);
        if (px === 0) ctx.moveTo(px, y);
        else ctx.lineTo(px, y);
      }
      ctx.stroke();
    };

    if (s.source) {
      sine(COLOR_INK, 1.75);
      return;
    }
    if (state.phase === "idle") return;
    if (state.showRef) sine(COLOR_REF, 1.25);

    const a = s.arrivals;
    if (!a.length) return;
    ctx.strokeStyle = s.color;
    ctx.lineWidth = 1.75;
    ctx.beginPath();
    let j = 0;
    for (let px = 0; px <= w; px++) {
      const t = tStart + (px / w) * win;
      let y = mid;
      if (t >= a[0].t) {
        while (j < a.length - 1 && a[j + 1].t <= t) j++;
        const tj = a[j].t;
        const per = j < a.length - 1 ? a[j + 1].t - tj : j > 0 ? tj - a[j - 1].t : 1 / a[j].fe;
        y = mid - amp * Math.cos((2 * Math.PI * (t - tj)) / per);
      }
      if (px === 0) ctx.moveTo(px, y);
      else ctx.lineTo(px, y);
    }
    ctx.stroke();
  }

  /* 탭 3 그래프 — 곡선은 공식, 점은 두 줄에서 잰 값 */
  function renderGraph() {
    const { w, h, ctx } = SimUtils.fitCanvas(graph);
    ctx.fillStyle = COLOR_STAGE;
    ctx.fillRect(0, 0, w, h);
    const L = 56;
    const R = 18;
    const Tp = 44;
    const B = 52;
    const pw = w - L - R;
    const ph = h - Tp - B;
    if (pw < 60 || ph < 60) return;

    const f = state.f;
    const yMax = f * 2.6;
    const X = (u) => L + ((u + V_MAX) / (2 * V_MAX)) * pw;
    const Y = (fr) => Tp + ph - (Math.min(fr, yMax) / yMax) * ph;

    ctx.lineWidth = 1;
    const step = SimUtils.niceStep(yMax, 5);
    for (let v = 0; v <= yMax + 1e-9; v += step) {
      ctx.strokeStyle = COLOR_GRID;
      ctx.beginPath();
      ctx.moveTo(L, Math.round(Y(v)) + 0.5);
      ctx.lineTo(L + pw, Math.round(Y(v)) + 0.5);
      ctx.stroke();
      label(ctx, String(Math.round(v)), L - 7, Y(v) + 4, COLOR_MUTE, 11, "right", "400", true);
    }
    for (let u = -300; u <= 300; u += 100) {
      ctx.strokeStyle = u === 0 ? "#d4d4d4" : COLOR_GRID;
      ctx.beginPath();
      ctx.moveTo(Math.round(X(u)) + 0.5, Tp);
      ctx.lineTo(Math.round(X(u)) + 0.5, Tp + ph);
      ctx.stroke();
      label(ctx, String(Math.abs(u)), X(u), Tp + ph + 16, COLOR_MUTE, 11, "center", "400", true);
    }
    label(ctx, "← 멀어짐     속력 (m/s)     다가옴 →", L + pw / 2, Tp + ph + 38, COLOR_BODY, 12);
    label(ctx, "들리는 진동수 (Hz)", L - 7, Tp - 12, COLOR_BODY, 12, "left");

    ctx.save();
    ctx.setLineDash([3, 4]);
    ctx.strokeStyle = COLOR_MUTE;
    ctx.beginPath();
    ctx.moveTo(L, Y(f));
    ctx.lineTo(L + pw, Y(f));
    ctx.stroke();
    ctx.restore();
    label(ctx, `원래 ${f} Hz`, L + pw - 4, Y(f) - 6, COLOR_MUTE, 11, "right");

    // ① 음원이 움직일 때 v/(v−u)·f — 위로 치솟아 그래프를 벗어나는 곳에서 끊는다
    const uExit = V_SOUND * (1 - f / yMax);
    ctx.strokeStyle = COLOR_INK;
    ctx.lineWidth = 2;
    ctx.beginPath();
    for (let i = 0; i <= 240; i++) {
      const u = Math.min(-V_MAX + (i / 240) * 2 * V_MAX, uExit);
      const y = Y((V_SOUND / (V_SOUND - u)) * f);
      if (i === 0) ctx.moveTo(X(u), y);
      else ctx.lineTo(X(u), y);
      if (u >= uExit) break;
    }
    ctx.stroke();

    // ② 관찰자가 움직일 때 (v+u)/v·f — 직선
    ctx.save();
    ctx.setLineDash([7, 5]);
    ctx.beginPath();
    ctx.moveTo(X(-V_MAX), Y(((V_SOUND - V_MAX) / V_SOUND) * f));
    ctx.lineTo(X(V_MAX), Y(((V_SOUND + V_MAX) / V_SOUND) * f));
    ctx.stroke();
    ctx.restore();

    const u = state.speed[3];
    ctx.save();
    ctx.setLineDash([2, 3]);
    ctx.strokeStyle = "#bdbdbd";
    ctx.beginPath();
    ctx.moveTo(X(u), Tp);
    ctx.lineTo(X(u), Tp + ph);
    ctx.stroke();
    ctx.restore();

    const m1 = measure(T3.l1.obs);
    const m2 = measure(T3.l2.obs);
    const dot = (m, filled, dy) => {
      if (!m) return;
      const fr = m.fHeard;
      const x = X(u);
      if (fr > yMax) {
        ctx.fillStyle = COLOR_INK;
        ctx.beginPath();
        ctx.moveTo(x, Tp - 2);
        ctx.lineTo(x - 6, Tp + 8);
        ctx.lineTo(x + 6, Tp + 8);
        ctx.closePath();
        ctx.fill();
        const leftSide = x > L + pw * 0.6;
        label(ctx, `${fr.toFixed(2)} Hz`, x + (leftSide ? -10 : 10), Tp + 9, COLOR_INK, 12,
          leftSide ? "right" : "left", "600", true);
        return;
      }
      const y = Y(fr);
      ctx.beginPath();
      ctx.arc(x, y, 5.5, 0, Math.PI * 2);
      ctx.fillStyle = filled ? COLOR_INK : "#ffffff";
      ctx.strokeStyle = COLOR_INK;
      ctx.lineWidth = 2;
      ctx.fill();
      ctx.stroke();
      const right = x < L + pw * 0.7;
      label(ctx, fr.toFixed(2), x + (right ? 10 : -10), y + dy, COLOR_INK, 12, right ? "left" : "right", "600", true);
    };
    dot(m1, true, -8);
    dot(m2, false, 16);

    // 범례 — 곡선이 낮게 지나가는 왼쪽 위 빈자리에
    const lx = L + 12;
    const ly = Tp + 18;
    ctx.fillStyle = "rgba(255, 255, 255, 0.9)";
    ctx.fillRect(lx - 6, ly - 13, 172, 44);
    ctx.strokeStyle = COLOR_INK;
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(lx, ly - 4);
    ctx.lineTo(lx + 24, ly - 4);
    ctx.stroke();
    label(ctx, "① 음원이 움직일 때", lx + 32, ly, COLOR_BODY, 12, "left");
    ctx.save();
    ctx.setLineDash([7, 5]);
    ctx.beginPath();
    ctx.moveTo(lx, ly + 16);
    ctx.lineTo(lx + 24, ly + 16);
    ctx.stroke();
    ctx.restore();
    label(ctx, "② 관찰자가 움직일 때", lx + 32, ly + 20, COLOR_BODY, 12, "left");
  }

  function render() {
    const T = tab();
    const { w, h, ctx } = SimUtils.fitCanvas(canvas);
    ctx.fillStyle = COLOR_STAGE;
    ctx.fillRect(0, 0, w, h);
    T.lastG = T.render(ctx, w, h);
    if (state.tab === 3) renderGraph();
    cardEls.forEach((el, i) => drawStrip(el.strip, models[i].strip));
  }

  /* ---------------------------------------------------------
     소리 — 고른 카드가 지금 재는 진동수를 그대로 낸다
     탭 1~3은 구급차 사이렌(삐뽀), 탭 4는 한 음.
     사이렌은 두 음 모두에 지금 잰 비율 f′/f 를 곱한다 — 도플러 효과는 소리 전체를 같은 비율로 바꾼다.
     ⚠ 삐·뽀 박자는 실제 빠르기로 울린다. 화면처럼 300배 느리게 하면 사이렌으로 들리지 않는다.
       높낮이 변화만 화면의 시뮬레이션을 따라간다.
     --------------------------------------------------------- */
  const SIREN_HI = 4 / 3;      // 삐 — 낮은 음 뽀(= f)보다 완전4도 위
  const SIREN_HALF = 0.45;     // 삐·뽀 한 음의 길이 (실제 초)
  const VOLUME_SIREN = 0.05;

  const audio = { ctx: null, osc: null, gain: null, who: -1, wave: null, mode: "" };

  // 지금 낼 음과, 그중 가장 높은 음 (사람 귀에 들리는지 판단용)
  function soundPlan(m) {
    if (!m || !m.audioHz) return null;
    if (m.siren == null) return { hz: m.audioHz, top: m.audioHz, siren: false };
    const lo = state.f * m.siren;
    const high = audio.ctx && Math.floor(audio.ctx.currentTime / SIREN_HALF) % 2 === 0;
    return { hz: high ? lo * SIREN_HI : lo, top: lo * SIREN_HI, siren: true };
  }

  function setWave(siren) {
    const mode = siren ? "siren" : "sine";
    if (audio.mode === mode) return;
    audio.mode = mode;
    if (siren) audio.osc.setPeriodicWave(audio.wave);
    else audio.osc.type = "sine";
  }

  function updateSpeakers() {
    cardEls.forEach((el, i) => {
      el.spk.classList.toggle("is-on", audio.who === i);
      el.spk.setAttribute("aria-pressed", String(audio.who === i));
    });
  }

  function toggleSound(i) {
    const next = audio.who === i ? -1 : i;
    if (next >= 0 && !audio.ctx) {
      const AC = window.AudioContext || window.webkitAudioContext;
      if (!AC) {
        toast("이 브라우저에서는 소리를 낼 수 없다");
        return;
      }
      audio.ctx = new AC();
      audio.osc = audio.ctx.createOscillator();
      audio.gain = audio.ctx.createGain();
      // 사이렌 음색 — 기본음에 배음을 조금 섞어 전자 사이렌처럼, 그러나 날카롭지 않게
      audio.wave = audio.ctx.createPeriodicWave(
        new Float32Array([0, 0, 0, 0, 0, 0]),
        new Float32Array([0, 1, 0.35, 0.22, 0.1, 0.06]));
      audio.osc.type = "sine";
      audio.mode = "sine";
      audio.gain.gain.value = 0;
      audio.osc.connect(audio.gain);
      audio.gain.connect(audio.ctx.destination);
      audio.osc.start();
    }
    if (audio.ctx && audio.ctx.state === "suspended") audio.ctx.resume();
    audio.who = next;
    updateSpeakers();
    if (next >= 0) {
      const p = soundPlan(models[next]);
      if (p && p.top > HEARING_MAX) toast(`${models[next].name} · ${HEARING_MAX} Hz를 넘는 초음파라 사람 귀에는 들리지 않는다`);
      else toast(`${models[next].name} · 볼륨을 낮추고 들어 보세요`);
    }
    updateSound();
  }

  function updateSound() {
    if (!audio.ctx) return;
    const t = audio.ctx.currentTime;
    const m = audio.who >= 0 && models ? models[audio.who] : null;
    const p = state.phase === "running" && !document.hidden ? soundPlan(m) : null;
    let vol = 0;
    if (p && p.hz >= 20 && p.top <= HEARING_MAX) {
      setWave(p.siren);
      audio.osc.frequency.setTargetAtTime(p.hz, t, p.siren ? 0.006 : 0.015);
      // 높은 음일수록 같은 크기도 날카롭게 들려서 줄인다
      vol = (p.siren ? VOLUME_SIREN : VOLUME) * Math.min(1, Math.sqrt(800 / p.hz));
    }
    audio.gain.gain.setTargetAtTime(vol, t, 0.03);
  }

  let toastTimer = 0;
  function toast(msg) {
    const el = $("toast");
    el.textContent = msg;
    el.classList.remove("hidden");
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => el.classList.add("hidden"), 2800);
  }

  /* ---------------------------------------------------------
     조작
     --------------------------------------------------------- */
  const speedRange = (n) => (n === 3 ? [-Math.round(V_MAX), Math.round(V_MAX)] : [0, Math.round(V_MAX)]);

  function syncSpeedUI() {
    const n = state.tab;
    const [lo, hi] = speedRange(n);
    const v = state.speed[n];
    ["vsInput", "vsNum"].forEach((id) => {
      $(id).min = lo;
      $(id).max = hi;
      $(id).value = v;
    });
    const mach = `음속의 ${(Math.abs(v) / V_SOUND).toFixed(2)}배`;
    $("vsMeta").textContent = n !== 3 ? mach : v === 0 ? "정지" : `${v > 0 ? "다가옴" : "멀어짐"} · ${mach}`;
    $("speedLabel").textContent = tab().speedLabel();
    updateEquation();
  }

  /* 탭 3 일반식 — 두 줄이 각각 vₒ = 0, vₛ = 0 인 경우임을 지금 속력으로 보여 준다 */
  function updateEquation() {
    const u = state.speed[3];
    const f = state.f;
    const a = Math.abs(u);
    const den = u === 0 ? `${V_SOUND}` : `(${V_SOUND} ${u > 0 ? "−" : "+"} ${a})`;
    const num = u === 0 ? `${V_SOUND}` : `(${V_SOUND} ${u > 0 ? "+" : "−"} ${a})`;
    const f1 = (V_SOUND / (V_SOUND - u)) * f;
    const f2 = ((V_SOUND + u) / V_SOUND) * f;
    $("eqSub1").innerHTML = `① v<sub>o</sub> = 0 → ${V_SOUND} ÷ ${den} × ${f} = <b>${f1.toFixed(2)}</b>`;
    $("eqSub2").innerHTML = `② v<sub>s</sub> = 0 → ${num} ÷ ${V_SOUND} × ${f} = <b>${f2.toFixed(2)}</b>`;
  }

  function setSpeed(v) {
    const n = state.tab;
    const [lo, hi] = speedRange(n);
    state.speed[n] = clamp(Math.round(Number(v) || 0), lo, hi);
    syncSpeedUI();
    // 탭 3은 다가갈 때와 멀어질 때 출발 위치가 달라서 처음부터 다시 놓는다
    if (n === 3) {
      const wasRunning = state.phase === "running";
      resetTab();
      if (wasRunning) start();
    }
  }

  function setF(v) {
    state.f = clamp(Math.round(Number(v) || 500), 200, 1000);
    $("fInput").value = state.f;
    $("fNum").value = state.f;
    updateEquation();
  }

  function setDir(d) {
    if (state.tab === 3) return;
    state.drag = null;
    state.dir = d;
    if (d !== 0 && state.phase !== "running") start();
    updateDirButtons();
  }

  function updateDirButtons() {
    document.querySelectorAll(".btn.dir").forEach((b) =>
      b.classList.toggle("is-active", Number(b.dataset.dir) === state.dir));
  }

  function setMover(which) {
    T4.mover = which === "bat" ? T4.bat.body : T4.target.body;
    state.dir = 0;
    state.drag = null;
    updateDirButtons();
    updateMoverUI();
    syncSpeedUI();
  }

  function updateMoverUI() {
    if (!T4.bat) return;
    const isBat = T4.mover === T4.bat.body;
    document.querySelectorAll("#moverSeg button").forEach((b) =>
      b.classList.toggle("is-active", (b.dataset.mover === "bat") === isBat));
  }

  function updatePlayButtons() {
    const finished = state.tab === 3 && T3.done;
    $("playBtn").textContent = finished ? "다시" : state.phase === "paused" ? "계속" : "시작";
    $("playBtn").disabled = state.phase === "running";
    $("pauseBtn").disabled = state.phase !== "running";
  }

  function updateStatus() {
    const T = tab();
    $("statusTag").textContent = { idle: "대기 중", running: "진행 중", paused: "일시정지" }[state.phase];
    const parts = [T.hint, `실제보다 ${state.slow}배 느리게`];
    if (state.tab === 4 && T4.fNom) parts.push("파면 간격은 넓혀 그림");
    $("stageHint").textContent = parts.filter(Boolean).join(" · ");
  }

  function applyTabUI() {
    const n = state.tab;
    document.querySelectorAll(".tab").forEach((b) => b.classList.toggle("is-active", Number(b.dataset.tab) === n));
    document.querySelectorAll(".btn.dir").forEach((b) => b.classList.toggle("hidden", n === 3));
    $("moverSeg").classList.toggle("hidden", n !== 4);
    $("presetRow").classList.toggle("hidden", n !== 4);
    $("exampleBtn").classList.toggle("hidden", n === 4);
    $("exampleBtn").title = tab().example;
    $("stage").classList.toggle("with-graph", n === 3);
    $("graphCol").classList.toggle("hidden", n !== 3);
    $("stageNote").classList.toggle("hidden", n !== 4);
    syncSpeedUI();
    updateMoverUI();
    updateDirButtons();
    updatePlayButtons();
    updateStatus();
    applyCards();
  }

  function resetTab() {
    state.phase = "idle";
    state.tau = 0;
    state.dir = 0;
    state.drag = null;
    tab().setup();
    models = tab().cards();
    updatePlayButtons();
    updateStatus();
    updateDirButtons();
    updateMoverUI();
    syncSpeedUI();
    applyCards();
    updateSound();
  }

  function setTab(n) {
    if (n === state.tab) return;
    state.tab = n;
    audio.who = -1;
    updateSpeakers();
    resetTab();
    applyTabUI();
  }

  function start() {
    if (state.tab === 3 && T3.done) resetTab();
    if (state.tab === 3 && state.phase === "idle") T3.prefill();
    state.phase = "running";
    lastTs = null;
    updatePlayButtons();
    updateDirButtons();
    updateStatus();
  }

  function pause() {
    if (state.phase !== "running") return;
    state.phase = "paused";
    state.drag = null;
    updatePlayButtons();
    updateStatus();
    updateSound();
  }

  /* ---------------------------------------------------------
     끌기 — 마우스·터치 모두 (전자칠판)
     --------------------------------------------------------- */
  function canvasPoint(e) {
    const r = canvas.getBoundingClientRect();
    return { mx: e.clientX - r.left, my: e.clientY - r.top };
  }

  function hitTest(e) {
    const T = tab();
    const g = T.lastG;
    if (!g || !T.draggables) return null;
    const { mx, my } = canvasPoint(e);
    for (const d of T.draggables()) {
      if (Math.abs(mx - g.px(d.body.x)) <= d.hx && my >= g.axisY - d.top && my <= g.axisY + d.bottom) return d.body;
    }
    return null;
  }

  function pointerX(e) {
    const g = tab().lastG;
    return (canvasPoint(e).mx - g.w / 2) / g.ppm;
  }

  function bindDrag() {
    canvas.addEventListener("pointerdown", (e) => {
      if (state.phase === "paused") return;
      const hit = hitTest(e);
      if (!hit) return;
      e.preventDefault();
      canvas.setPointerCapture(e.pointerId);
      state.dir = 0;
      updateDirButtons();
      if (state.tab === 4) {
        T4.mover = hit;
        updateMoverUI();
        syncSpeedUI();
      }
      state.drag = { body: hit, dx: hit.x - pointerX(e), targetX: hit.x, released: false };
      canvas.style.cursor = "grabbing";
    });

    canvas.addEventListener("pointermove", (e) => {
      const d = state.drag;
      if (d && !d.released) {
        const [lo, hi] = tab().limitsFor(d.body);
        d.targetX = clamp(pointerX(e) + d.dx, lo, hi);
        return;
      }
      canvas.style.cursor = state.phase !== "paused" && hitTest(e) ? "grab" : "default";
    });

    const end = () => {
      if (!state.drag) return;
      if (state.phase === "running") state.drag.released = true;
      else state.drag = null;
      canvas.style.cursor = "grab";
    };
    canvas.addEventListener("pointerup", end);
    canvas.addEventListener("pointercancel", end);
  }

  /* ---------------------------------------------------------
     재생
     --------------------------------------------------------- */
  let lastTs = null;
  let lastReadout = 0;

  function step(dtReal) {
    const T = tab();
    const dTau = dtReal / state.slow;
    const t0 = state.tau;
    const t1 = t0 + dTau;
    T.bodies().forEach((b) => { b.x0 = b.x; });
    T.step(t0, t1, dTau);
    state.tau = t1;
    const hw = T.lastG ? T.lastG.hWorld : 4;
    T.worlds().forEach((w) => cleanup(w, hw));
  }

  function frame(ts) {
    const dtReal = lastTs == null ? 0 : Math.min((ts - lastTs) / 1000, 0.05);
    lastTs = ts;
    const T = tab();
    if (state.phase === "running" && dtReal > 0) {
      step(dtReal);
      if (state.tab === 3 && T3.done) {
        pause();
        toast("끝까지 왔다 · 두 값을 비교해 보자");
      }
    } else if (state.phase === "idle" && state.drag) {
      const b = state.drag.body;
      const [lo, hi] = T.limitsFor(b);
      b.x = b.x0 = clamp(state.drag.targetX, lo, hi);
    }
    models = T.cards();
    render();
    updateSound();
    if (ts - lastReadout > 120) {
      applyCards();
      lastReadout = ts;
    }
    requestAnimationFrame(frame);
  }

  /* ---------------------------------------------------------
     이벤트
     --------------------------------------------------------- */
  function bind() {
    $("playBtn").addEventListener("click", start);
    $("pauseBtn").addEventListener("click", pause);
    $("resetBtn").addEventListener("click", resetTab);

    document.querySelectorAll(".tab").forEach((b) =>
      b.addEventListener("click", () => setTab(Number(b.dataset.tab))));
    document.querySelectorAll(".btn.dir").forEach((b) =>
      b.addEventListener("click", () => setDir(Number(b.dataset.dir))));
    document.querySelectorAll("#moverSeg button").forEach((b) =>
      b.addEventListener("click", () => setMover(b.dataset.mover)));
    document.querySelectorAll("#presetRow .chip").forEach((b) =>
      b.addEventListener("click", () => T4.preset(b.dataset.preset)));
    $("exampleBtn").addEventListener("click", () => tab().runExample());

    $("vsInput").addEventListener("input", (e) => setSpeed(e.target.value));
    $("vsNum").addEventListener("change", (e) => setSpeed(e.target.value));
    $("fInput").addEventListener("input", (e) => setF(e.target.value));
    $("fNum").addEventListener("change", (e) => setF(e.target.value));
    ["vsNum", "fNum"].forEach((id) =>
      $(id).addEventListener("keydown", (e) => { if (e.key === "Enter") e.target.blur(); }));

    $("slowSelect").addEventListener("change", (e) => {
      state.slow = Number(e.target.value);
      updateStatus();
    });
    $("showLambda").addEventListener("change", (e) => { state.showLambda = e.target.checked; });
    $("showRef").addEventListener("change", (e) => { state.showRef = e.target.checked; });

    cardEls.forEach((el, i) => el.spk.addEventListener("click", () => toggleSound(i)));

    $("settingsToggle").addEventListener("click", () => $("settingsOverlay").classList.remove("hidden"));
    $("settingsClose").addEventListener("click", () => $("settingsOverlay").classList.add("hidden"));
    $("settingsBackdrop").addEventListener("click", () => $("settingsOverlay").classList.add("hidden"));
    document.addEventListener("keydown", (e) => {
      if (e.key === "Escape") $("settingsOverlay").classList.add("hidden");
    });
    // 탭을 가리면 requestAnimationFrame이 멈춰 소리만 남는다 — 바로 끈다
    document.addEventListener("visibilitychange", updateSound);

    bindDrag();
  }

  /* ---------------------------------------------------------
     시작
     --------------------------------------------------------- */
  function init() {
    canvas = $("simCanvas");
    graph = $("graphCanvas");
    cardEls = [...document.querySelectorAll(".obs-card")].map((card) => {
      const q = (role) => card.querySelector(`[data-role="${role}"]`);
      return {
        name: q("name"), tag: q("tag"), spk: q("spk"), fbox: q("fbox"), fsym: q("fsym"), f: q("f"),
        k: [q("k1"), q("k2"), q("k3")], v: [q("v1"), q("v2"), q("v3")], row3: q("row3"),
        strip: q("strip"), form: q("form"),
      };
    });

    setF(state.f);
    T4.setup();          // 탭 4 버튼 상태를 그릴 때 박쥐·표적이 있어야 한다
    bind();
    resetTab();
    applyTabUI();
    requestAnimationFrame(frame);
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", init);
  else init();
})();
