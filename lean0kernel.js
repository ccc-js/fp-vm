#!/usr/bin/env node
'use strict';
/*
 * lean0kernel.js — 微型 Lean4 的可信任小核心 (純函數，無 I/O、無全域狀態、無 meta 儲存)
 *
 * 職責: 對「完全顯式、無未定元」的核心項做換名安全代換、whnf、defeq 與型別檢查。
 *  所有需要未定元 (?meta) 的工作 (隱式參數、一階合一) 屬於 elaborator (lean0c.js)，
 *  經由 flex 介面 { get(id)->term|undefined, set(id, term) } 注入；flex 為 null 時
 *  遇到 meta 即報錯 (防火牆：kernel 永遠不接受含未定元的項)。
 *
 * 核心項 (K 構造, 見 inferCheck 議)：
 *  var/const/sort(n)/pi(name,info,dom,body)/lam(name,dom,body)/app(f,a)/let(name,ty,val,body)
 *  sigma(name,fst,snd)/pair(a,b)/fst(p)/snd(p)
 *  nat/zero/succ(p)/natlit(v)/natrec(motive,zero,succ,target)
 *  bool/true/false/boolrec(motive,tt,ff,target)
 *  eq(ty,lhs,rhs)/refl/eqrec(motive,h,target)
 *
 * consts 表: Map name -> { type, value|null, kind, rigid? }，由呼叫方傳入。
 */
const K = (t, o) => Object.assign({ t }, o);
const SORT = (u) => K('sort', { u });

let freshN = 0;
const fresh = (b) => `${b}'${freshN++}`;

class KError extends Error {}
const fail = (msg) => { throw new KError(msg); };

/* ───────────── 代換 (capture-avoiding) ───────────── */
function freeVars(e, bound = new Set()) {
  const out = new Set();
  const go = (x, bd) => {
    if (!x || typeof x !== 'object') return;
    switch (x.t) {
      case 'var': if (!bd.has(x.name)) out.add(x.name); break;
      case 'lam': case 'pi':
        go(x.dom, bd);
        go(x.body, new Set([...bd, x.name]));
        break;
      case 'app': go(x.f, bd); go(x.a, bd); break;
      case 'let':
        go(x.ty, bd); go(x.val, bd);
        go(x.body, new Set([...bd, x.name]));
        break;
      case 'sigma':
        go(x.fst, bd);
        go(x.snd, new Set([...bd, x.name]));
        break;
      case 'pair': go(x.a, bd); go(x.b, bd); break;
      case 'fst': case 'snd': go(x.p, bd); break;
      case 'succ': go(x.p, bd); break;
      case 'eq': go(x.ty, bd); go(x.lhs, bd); go(x.rhs, bd); break;
      case 'natrec': go(x.motive, bd); go(x.zero, bd); go(x.succ, bd); go(x.target, bd); break;
      case 'boolrec': go(x.motive, bd); go(x.tt, bd); go(x.ff, bd); go(x.target, bd); break;
      case 'eqrec': go(x.motive, bd); go(x.h, bd); go(x.target, bd); break;
      default: break;
    }
  };
  go(e, bound);
  return out;
}

function subst(e, name, v) {
  const go = (x) => {
    if (!x || typeof x !== 'object') return x;
    switch (x.t) {
      case 'var': return x.name === name ? v : x;
      case 'lam': case 'pi': {
        if (x.name === name) {
          return x.t === 'lam'
            ? K('lam', { name: x.name, dom: x.dom && go(x.dom), body: x.body })
            : K('pi', { name: x.name, info: x.info, dom: go(x.dom), body: x.body });
        }
        if (freeVars(v).has(x.name)) {
          const n2 = fresh(x.name);
          const renamed = subst(x.body, x.name, K('var', { name: n2 }));
          return x.t === 'lam'
            ? K('lam', { name: n2, dom: x.dom && go(x.dom), body: go(renamed) })
            : K('pi', { name: n2, info: x.info, dom: go(x.dom), body: go(renamed) });
        }
        return x.t === 'lam'
          ? K('lam', { name: x.name, dom: x.dom && go(x.dom), body: go(x.body) })
          : K('pi', { name: x.name, info: x.info, dom: go(x.dom), body: go(x.body) });
      }
      case 'app': return K('app', { f: go(x.f), a: go(x.a) });
      case 'let':
        if (x.name === name) return K('let', { name: x.name, ty: go(x.ty), val: go(x.val), body: x.body });
        return K('let', { name: x.name, ty: go(x.ty), val: go(x.val), body: go(x.body) });
      case 'sigma':
        if (x.name === name) return K('sigma', { name: x.name, fst: go(x.fst), snd: x.snd });
        return K('sigma', { name: x.name, fst: go(x.fst), snd: go(x.snd) });
      case 'pair': return K('pair', { a: go(x.a), b: go(x.b) });
      case 'fst': return K('fst', { p: go(x.p) });
      case 'snd': return K('snd', { p: go(x.p) });
      case 'succ': return K('succ', { p: go(x.p) });
      case 'eq': return K('eq', { ty: go(x.ty), lhs: go(x.lhs), rhs: go(x.rhs) });
      case 'natrec': return K('natrec', { motive: go(x.motive), zero: go(x.zero), succ: go(x.succ), target: go(x.target) });
      case 'boolrec': return K('boolrec', { motive: go(x.motive), tt: go(x.tt), ff: go(x.ff), target: go(x.target) });
      case 'eqrec': return K('eqrec', { motive: go(x.motive), h: go(x.h), target: go(x.target) });
      default: return x;
    }
  };
  return go(e);
}

/* ───────────── whnf ─────────────
 * full=false (供 defeq/匹配)：beta＋iota＋zeta＋可 beta 的 delta；
 *   帶未定元的 rigid type-former 套用式保持摺疊 (保一階合一)。
 * full=true (供形狀檢查)：另展開無自由變數的閉值。 */
function hasStuckMeta(t, flex) {
  let found = false;
  const go = (x) => {
    if (found) return;
    x = deref(x, flex);
    if (!x || typeof x !== 'object') return;
    if (x.t === 'meta') { found = true; return; }
    for (const v of Object.values(x)) if (v && typeof v === 'object') go(v);
  };
  go(t);
  return found;
}

function deref(t, flex) {
  while (t && t.t === 'meta' && flex) {
    const v = flex.get(t.id);
    if (v === undefined || v === null) break;
    t = v;
  }
  return t;
}

function whnf(e, consts, full = false, flex = null) {
  let t = deref(e, flex);
  for (;;) {
    t = deref(t, flex);
    if (!t || typeof t !== 'object') return t;
    switch (t.t) {
      case 'app': {
        {
          let h0 = t;
          const sp = [];
          while (h0 && h0.t === 'app') { sp.unshift(h0.a); h0 = deref(h0.f, flex); }
          if (h0 && h0.t === 'const' && sp.length) {
            const c0 = consts.get(h0.name);
            if (c0 && c0.rigid && sp.some((s) => hasStuckMeta(s, flex))) return t;
          }
        }
        const f = whnf(t.f, consts, full, flex);
        if (f && f.t === 'lam') { t = subst(f.body, f.name, t.a); continue; }
        return K('app', { f, a: t.a });
      }
      case 'fst': {
        const p = whnf(t.p, consts, full, flex);
        if (p && p.t === 'pair') { t = p.a; continue; }
        return K('fst', { p });
      }
      case 'snd': {
        const p = whnf(t.p, consts, full, flex);
        if (p && p.t === 'pair') { t = p.b; continue; }
        return K('snd', { p });
      }
      case 'let': t = subst(t.body, t.name, t.val); continue;
      case 'natrec': {
        const n = whnf(t.target, consts, full, flex);
        if (n && n.t === 'zero') { t = t.zero; continue; }
        if (n && n.t === 'succ') { t = K('app', { f: K('app', { f: t.succ, a: n.p }), a: K('natrec', { motive: t.motive, zero: t.zero, succ: t.succ, target: n.p }) }); continue; }
        if (n && n.t === 'natlit') {
          if (n.v === 0) { t = t.zero; continue; }
          let r = t.zero;
          for (let i = 1; i <= n.v; i++) r = K('app', { f: K('app', { f: t.succ, a: K('natlit', { v: i - 1 }) }), a: r });
          t = r; continue;
        }
        return K('natrec', { motive: t.motive, zero: t.zero, succ: t.succ, target: n });
      }
      case 'boolrec': {
        const b = whnf(t.target, consts, full, flex);
        if (b && b.t === 'true') { t = t.tt; continue; }
        if (b && b.t === 'false') { t = t.ff; continue; }
        return t;
      }
      case 'eqrec': {
        const e2 = whnf(t.target, consts, full, flex);
        if (e2 && e2.t === 'refl') { t = t.h; continue; }
        return t;
      }
      case 'const': {
        {
          const c = consts.get(t.name);
          if (c && c.value && freeVars(c.value).size === 0) { t = c.value; continue; }
        }
        return t;
      }
      default: return t;
    }
  }
}

/* ───────────── defeq ─────────────
 * 同頭 rigid type-former 優先結構比對 (保一階合一；失敗落回一般路徑)；
 * meta 遇到 flex 則 get/set，無 flex 即報錯 (kernel 防火牆)。 */
function checkDeep(e, id, flex) {
  e = deref(e, flex);
  if (!e || typeof e !== 'object') return false;
  if (e.t === 'meta') return e.id === id;
  return Object.values(e).some((v) => v && typeof v === 'object' && checkDeep(v, id, flex));
}

function assignMeta(id, e, flex, fuel) {
  void fuel;
  e = deref(e, flex);
  if (e && e.t === 'meta' && e.id === id) return;
  if (!flex) fail('kernel 遇到未定元:' + JSON.stringify(a).slice(0,120));
  if (checkDeep(e, id, flex)) fail('defeq: occurs check 失敗 (無窮型別)');
  flex.set(id, e);
}

function defeq(a, b, consts, fuel = 200, flex = null) {
  if (fuel <= 0) fail('defeq 超時 (可能是無窮展開)');
  a = deref(a, flex); b = deref(b, flex);
  if (a && a.t === 'meta') {
    if (!flex) fail('kernel 遇到未定元:?' + a.id);
    assignMeta(a.id, b, flex); return;
  }
  if (b && b.t === 'meta') {
    if (!flex) fail('kernel 遇到未定元:?' + b.id);
    assignMeta(b.id, a, flex); return;
  }
  { /* 剛性同頭優先 */
    const headName = (x) => {
      while (x && x.t === 'app') x = deref(x.f, flex);
      return x && x.t === 'const' ? x.name : null;
    };
    const spine = (x) => { const r = []; while (x && x.t === 'app') { r.unshift(x.a); x = x.f; } return r; };
    const ha = headName(a), hb = headName(b);
    if (ha && ha === hb) {
      const c = consts.get(ha);
      if (c && c.rigid) {
        const aa = spine(a), ab = spine(b);
        if (aa.length === ab.length) {
          try {
            aa.forEach((x, i) => defeq(x, ab[i], consts, fuel - 1, flex));
            return;
          } catch (e) {
            if (!(e instanceof KError)) throw e;
          }
        }
      }
    }
  }
  a = whnf(a, consts); b = whnf(b, consts);
  if (a && a.t === 'meta') {
    if (!flex) fail('kernel 遇到未定元:?' + a.id);
    assignMeta(a.id, b, flex); return;
  }
  if (b && b.t === 'meta') {
    if (!flex) fail('kernel 遇到未定元:?' + b.id);
    assignMeta(b.id, a, flex); return;
  }
  { /* Nat: Zero ≡ Lit 0；Lit n ≡ Succ Lit(n-1)；大數先比值 */
    const wa = whnf(a, consts), wb = whnf(b, consts);
    if (wa && wb && wa.t === 'natlit' && wb.t === 'natlit') {
      if (wa.v !== wb.v) fail('defeq: 數字不同');
      return;
    }
    const un = (w) => {
      if (!w) return null;
      if (w.t === 'zero' || (w.t === 'natlit' && w.v === 0)) return { zero: true };
      if (w.t === 'natlit') return w.v > 10000 ? null : { pred: K('natlit', { v: w.v - 1 }) };
      if (w.t === 'succ') return { pred: w.p };
      return null;
    };
    const s1 = un(wa), s2 = un(wb);
    if (s1 || s2) {
      if (!s1 || !s2) fail('defeq: Nat 形狀不同');
      if (s1.zero && s2.zero) return;
      if (s1.zero || s2.zero) fail('defeq: Nat 形狀不同');
      return defeq(s1.pred, s2.pred, consts, fuel - 1, flex);
    }
  }
  if (!a || !b || a.t !== b.t) fail(`defeq: 形狀不同 (${a && a.t} vs ${b && b.t})`);
  const rec = (x, y) => defeq(x, y, consts, fuel - 1, flex);
  switch (a.t) {
    case 'var': if (a.name !== b.name) fail(`defeq: 變數不同 ${a.name} vs ${b.name}`); return;
    case 'const': if (a.name !== b.name) fail('defeq: 常數不同'); return;
    case 'sort': if (a.u !== b.u) fail('defeq: universe 不同'); return;
    case 'zero': case 'true': case 'false': case 'refl': case 'nat': case 'bool': return;
    case 'natlit': if (a.v !== b.v) fail('defeq'); return;
    case 'succ': return rec(a.p, b.p);
    case 'app': rec(a.f, b.f); return rec(a.a, b.a);
    case 'lam': case 'pi': {
      rec(a.dom, b.dom);
      const n = fresh('x');
      rec(subst(a.body, a.name, K('var', { name: n })), subst(b.body, b.name, K('var', { name: n })));
      return;
    }
    case 'let': rec(a.val, b.val); return rec(subst(a.body, a.name, a.val), subst(b.body, b.name, b.val));
    case 'sigma': rec(a.fst, b.fst); {
      const n = fresh('x');
      rec(subst(a.snd, a.name, K('var', { name: n })), subst(b.snd, b.name, K('var', { name: n })));
      return;
    }
    case 'pair': rec(a.a, b.a); return rec(a.b, b.b);
    case 'fst': return rec(a.p, b.p);
    case 'snd': return rec(a.p, b.p);
    case 'eq': rec(a.ty, b.ty); rec(a.lhs, b.lhs); return rec(a.rhs, b.rhs);
    case 'natrec': rec(a.motive, b.motive); rec(a.zero, b.zero); rec(a.succ, b.succ); return rec(a.target, b.target);
    case 'boolrec': rec(a.motive, b.motive); rec(a.tt, b.tt); rec(a.ff, b.ff); return rec(a.target, b.target);
    case 'eqrec': rec(a.motive, b.motive); rec(a.h, b.h); return rec(a.target, b.target);
    default: fail(`defeq: 未處理 ${a.t}`);
  }
}

/* ───────────── 型別推論/檢查 (全顯式項；無隱式插入、無 meta 建立) ───────────── */
function piSort(m, n) {
  if (n === 0) return 0;
  if (m === -1 || n === -1 || n === null || n === undefined) fail('binder 請標註型別 (無法推斷 sort)');
  return Math.max(m, n);
}

function sortOfK(ty, ctx, consts, flex = null) {
  const t = whnf(inferK(ty, ctx, consts, flex), consts, true, flex);
  if (!t || t.t !== 'sort') fail('需要 Sort (此處應為型別)');
  return t.u;
}

function inferK(e, ctx, consts, flex = null) {
  e = deref(e, flex);
  if (!e || typeof e !== 'object') fail('inferK: 非法項');
  const lookup = (n) => {
    for (let i = ctx.length - 1; i >= 0; i--) if (ctx[i].name === n) return ctx[i].type;
    return undefined;
  };
  switch (e.t) {
    case 'var': {
      const t = lookup(e.name);
      if (t === undefined) fail(`未定義 "${e.name}"`);
      return t;
    }
    case 'const': {
      const c = consts.get(e.name);
      if (!c) fail(`未定義 "${e.name}"`);
      return c.type;
    }
    case 'sort': return SORT(e.u + 1);
    case 'nat': case 'bool': return SORT(1);
    case 'zero': case 'natlit': return K('nat', {});
    case 'succ': return K('pi', { name: '_', info: 'exp', dom: K('nat', {}), body: K('nat', {}) });
    case 'true': case 'false': return K('bool', {});
    case 'refl': fail('rfl 需要期望型別');
    case 'lam': fail('inferK: lambda 需期望型別 (請用 checkK)');
    case 'app': {
      const ft = whnf(inferK(e.f, ctx, consts, flex), consts, true, flex);
      if (!ft || ft.t !== 'pi') fail('inferK: 非函數套用');
      checkK(e.a, ft.dom, ctx, consts, flex);
      return subst(ft.body, ft.name, e.a);
    }
    case 'pi': case 'sigma': {
      const d = e.dom ?? e.fst;
      const m = sortOfK(d, ctx, consts, flex);
      const nm = e.name;
      const b = sortOfK(subst(e.body ?? e.snd, nm, K('var', { name: nm })), [{ name: nm, type: d }, ...ctx], consts, flex);
      return SORT(piSort(m, b));
    }
    case 'pair': fail('inferK: pair 需要期望型別 (請用 checkK)');
    case 'fst': {
      const t = whnf(inferK(e.p, ctx, consts, flex), consts, true, flex);
      if (!t || t.t !== 'sigma') fail('fst 需要 Sigma');
      return t.fst;
    }
    case 'snd': {
      const t = whnf(inferK(e.p, ctx, consts, flex), consts, true, flex);
      if (!t || t.t !== 'sigma') fail('snd 需要 Sigma');
      return subst(t.snd, t.name, K('fst', { p: e.p }));
    }
    case 'let': {
      checkK(e.val, e.ty, ctx, consts, flex);
      return inferK(subst(e.body, e.name, e.val), ctx, consts, flex);
    }
    case 'eq': return SORT(0);
    case 'natrec': return K('app', { f: e.motive, a: e.target });
    case 'boolrec': return K('app', { f: e.motive, a: e.target });
    case 'eqrec': return K('app', { f: e.motive, a: K('zero', {}) });
    case 'meta': fail('kernel 遇到未定元:?' + e.id);
    default: fail(`inferK: 未處理 ${e.t}`);
  }
}

function checkK(e, expected, ctx, consts, flex = null) {
  e = deref(e, flex);
  const exp = whnf(deref(expected, flex), consts, true, flex);
  if (e.t === 'lam') {
    if (!exp || exp.t !== 'pi') fail('fun 的期望型別不是 Pi');
    checkK(e.body, subst(exp.body, exp.name, K('var', { name: e.name })), [{ name: e.name, type: exp.dom }, ...ctx], consts, flex);
    return;
  }
  if (e.t === 'pair' && exp && exp.t === 'sigma') {
    checkK(e.a, exp.fst, ctx, consts, flex);
    checkK(e.b, subst(exp.snd, exp.name, e.a), ctx, consts, flex);
    return;
  }
  if (e.t === 'natlit') {
    if (!exp || !(exp.t === 'nat')) fail('數字需要 Nat 型別');
    return;
  }
  if (e.t === 'refl') {
    if (!exp || exp.t !== 'eq') fail('rfl 需要 Eq 型別');
    defeq(exp.lhs, exp.rhs, consts, 200, flex);
    return;
  }
  if (e.t === 'zero' && exp && exp.t === 'nat') return;
  if ((e.t === 'true' || e.t === 'false') && exp && exp.t === 'bool') return;
  if (e.t === 'app') {
    let f = e, sargs = [];
    while (f.t === 'app') { sargs.unshift(f.a); f = deref(f.f, flex); }
    if (f.t === 'lam' && sargs.length) {
      let r = subst(f.body, f.name, sargs.shift());
      for (const a of sargs) r = K('app', { f: r, a });
      return checkK(r, expected, ctx, consts, flex);
    }
    if (f.t === 'const' && f.name === 'Nat.rec' && sargs.length === 4) {
      checkRecNode(K('natrec', { motive: sargs[0], zero: sargs[1], succ: sargs[2], target: sargs[3] }), exp, ctx, consts, flex);
      return;
    }
    if (f.t === 'const' && f.name === 'Bool.rec' && sargs.length === 4) {
      checkRecNode(K('boolrec', { motive: sargs[0], tt: sargs[1], ff: sargs[2], target: sargs[3] }), exp, ctx, consts, flex);
      return;
    }
    if (f.t === 'const' && f.name === 'Eq.subst' && sargs.length === 6) {
      checkRecNode(K('eqrec', { motive: sargs[1], h: sargs[5], target: sargs[4] }), exp, ctx, consts, flex);
      return;
    }
    let fty = inferK(f, ctx, consts, flex);
    let fterm = f;
    for (const a of sargs) {
      const w = whnf(fty, consts, true, flex);
      if (!w || w.t !== 'pi') fail('非函數套用');
      checkK(a, w.dom, ctx, consts, flex);
      fterm = K('app', { f: fterm, a });
      fty = subst(w.body, w.name, a);
    }
    void fterm;
    defeq(fty, expected, consts, 200, flex);
    return;
  }
  if (e.t === 'natrec' || e.t === 'boolrec' || e.t === 'eqrec') {
    checkRecNode(e, exp, ctx, consts, flex);
    return;
  }
  const inferred = inferK(e, ctx, consts, flex);
  defeq(inferred, expected, consts, 200, flex);
}

function checkRecNode(e, exp, ctx, consts, flex) {
  const natTy = K('nat', {}), boolTy = K('bool', {});
  const checkMotive = (motive, domTy, what) => {
    motive = whnf(deref(motive, flex), consts, true, flex);
    if (!motive || motive.t !== 'lam') fail(`${what} motive 必須是 fun`);
    if (domTy) { try { defeq(motive.dom, domTy, consts, 200, flex); } catch (err) { fail(`${what} motive 定義域不符`); } }
    const mv = fresh('m');
    const bs = sortOfK(subst(motive.body, motive.name, K('var', { name: mv })), [{ name: mv, type: motive.dom }], consts, flex);
    if (bs < 0) fail(`${what} motive 值域須為 Sort`);
    return K('pi', { name: motive.name, info: 'exp', dom: motive.dom, body: motive.body });
  };
  if (e.t === 'natrec') {
    const mty = checkMotive(e.motive, natTy, 'Nat.rec');
    const M = (x) => subst(mty.body, mty.name, x);
    checkK(e.zero, M(K('zero', {})), ctx, consts, flex);
    const kn = fresh('n'), ihn = fresh('ih');
    checkK(e.succ, K('pi', { name: kn, info: 'exp', dom: natTy, body: K('pi', { name: ihn, info: 'exp', dom: M(K('var', { name: kn })), body: M(K('succ', { p: K('var', { name: kn }) })) }) }), ctx, consts, flex);
    checkK(e.target, natTy, ctx, consts, flex);
    defeq(M(e.target), exp, consts, 200, flex);
    return;
  }
  if (e.t === 'boolrec') {
    const mty = checkMotive(e.motive, boolTy, 'Bool.rec');
    const M = (x) => subst(mty.body, mty.name, x);
    checkK(e.tt, M(K('true', {})), ctx, consts, flex);
    checkK(e.ff, M(K('false', {})), ctx, consts, flex);
    checkK(e.target, boolTy, ctx, consts, flex);
    defeq(M(e.target), exp, consts, 200, flex);
    return;
  }
  if (e.t === 'eqrec') {
    let P = whnf(deref(e.motive, flex), consts, true, flex);
    if (!P || P.t !== 'lam') fail('Eq.subst motive 必須是 fun');
    const tt = whnf(inferK(e.target, ctx, consts, flex), consts, true, flex);
    if (!tt || tt.t !== 'eq') fail('Eq.subst 需要等式證明');
    defeq(P.dom, tt.ty, consts, 200, flex);
    const px = fresh('p');
    sortOfK(subst(P.body, P.name, K('var', { name: px })), [{ name: px, type: P.dom }, ...ctx], consts, flex);
    checkK(e.h, subst(P.body, P.name, tt.lhs), ctx, consts, flex);
    defeq(subst(P.body, P.name, tt.rhs), exp, consts, 200, flex);
    return;
  }
  fail('checkRecNode: 未知節點');
}

/* checkDef: 定義的防火牆。type 須為 Sort；value 須具 type；回傳用到的公理。 */
function checkDef(ty, val, consts) {
  const ctx = [];
  const s = sortOfK(ty, ctx, consts, null);
  void s;
  checkK(val, ty, ctx, consts, null);
  const ax = new Set();
  const go = (x) => {
    x = deref(x, null);
    if (!x || typeof x !== 'object') return;
    if (x.t === 'const') {
      const c = consts.get(x.name);
      if (c && c.kind === 'axiom') ax.add(x.name);
    }
    for (const v of Object.values(x)) if (v && typeof v === 'object') go(v);
  };
  go(val);
  return ax;
}

module.exports = {
  K, SORT, fresh, KError, fail,
  freeVars, subst,
  whnf, defeq, piSort, sortOfK, inferK, checkK, checkDef,
};
