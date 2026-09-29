//! 🌟 スパイラル相似(同じ向き)を、定理のマッチングではなく合同閉包の局所伝播として適用する(--rules=spiral-prop)。
//!
//! 定理として書くと、全体の再探索(schedule_full_sweep)のたびに、E で頂点を共有する等しい角の組を図全体から舐め直す。
//! ここでは有向角の同値類が変化したとき(worklist に積まれたとき)だけ、その同値類の定義の組を見る。
//! 前提2(A・D での角の一致)は、A 側と D 側を角の同値類をキーにハッシュ結合して探す(点の組を総当たりしない)。
//! 探した手数は spiral_prop_work に数え、仕事量の予算に含める(数えないと壁時計の時間だけ食う)。
//!
//! 前提: ∠(EA,EB) = ∠(ED,EC)(E を通る4直線は相異なる)かつ ∠(AE,AB) = ∠(DE,DC)。
//! 結論: M = AB の中点、N = DC の中点について ∠(EA,EM) = ∠(ED,EN)・∠(EM,AB) = ∠(EN,DC)、
//!       対になる相似の角 ∠(AE,AD) = ∠(BE,BC)。定理版「スパイラル相似(同じ向き)」と同じ主張。
//! 前提1の同値類が変化したときにしか走らないので、前提2が後から成り立った場合は取りこぼす(来歴 #75)。
//!
//! 図形は作らない: 結論の中点・直線・角が図に既にあるときだけマージする(既存の局所伝播と同じく、合同閉包は
//! マージだけをする)。作る形にすると、発火のたびに中点・直線・角が増えて図が膨らみ、無関係な問題が最大100倍
//! 重くなった。さらに作った中点が次の相似の頂点になって中点の中点…を際限なく作り、数秒でメモリを食い尽くした(来歴 #75)。

use super::*;

const NAME: &str = "スパイラル相似(同じ向き・局所伝播)";
/// 1回の実行で結論を適用する組の上限(連鎖の防止の保険)。
const MAX_FIRINGS: usize = 200;

impl EGraph {
    fn sp_finite_points_on(&self, line: ClassId) -> Vec<ClassId> {
        let linf = self.line_infinity;
        let mut v: Vec<ClassId> = self.entities[line.0].components.first()
            .map(|c| c.subobjects.iter().map(|&s| self.get_rep(s))
                .filter(|&s| self.entities[s.0].entity_type == EntityType::Point && !self.is_connected(s, linf))
                .collect())
            .unwrap_or_default();
        v.sort_unstable_by_key(|x| x.0);
        v.dedup();
        v
    }

    fn sp_lines_through(&self, p: ClassId) -> Vec<ClassId> {
        let linf = self.line_infinity;
        let mut v: Vec<ClassId> = self.entities[p.0].components.first()
            .map(|c| c.subobjects.iter().map(|&s| self.get_rep(s))
                .filter(|&s| s != linf && self.entities[s.0].entity_type == EntityType::Line)
                .collect())
            .unwrap_or_default();
        v.sort_unstable_by_key(|x| x.0);
        v.dedup();
        v
    }

    fn sp_dir(&self, line: ClassId) -> Option<ClassId> {
        self.memo.get(&self.normalize_definition(&Definition::DirectionOf(line))).map(|&d| self.get_rep(d))
    }

    fn sp_angle(&self, d1: ClassId, d2: ClassId) -> Option<ClassId> {
        self.memo.get(&self.normalize_definition(&Definition::AnglePair(d1, d2))).map(|&a| self.get_rep(a))
    }

    fn sp_line_with_dir(&self, p: ClassId, dir: ClassId) -> Option<ClassId> {
        self.sp_lines_through(p).into_iter().find(|&l| self.sp_dir(l) == Some(dir))
    }

    /// 有向角の同値類 scalar が変化したときに呼ぶ。何かマージしたら true。
    pub(crate) fn propagate_spiral(&mut self, scalar: ClassId) -> bool {
        let scalar = self.get_rep(scalar);
        if !self.spiral_propagation || !self.is_angle_value(scalar) { return false; }
        if self.spiral_prop_work >= self.spiral_work_limit { return false; }
        let Some(pending) = self.spiral_pending.remove(&scalar.0) else { return false };
        let mut pending: Vec<(ClassId, ClassId)> = pending.into_iter().map(|(x, y)| (self.get_rep(x), self.get_rep(y))).collect();
        pending.sort_unstable_by_key(|p| (p.0.0, p.1.0));
        pending.dedup();
        let defs: Vec<(ClassId, ClassId)> = match self.entities[scalar.0].components.first() {
            Some(c) => c.definitions.iter().filter_map(|d| match d {
                Definition::AnglePair(x, y) => Some((self.get_rep(*x), self.get_rep(*y))),
                _ => None,
            }).collect(),
            None => return false,
        };
        if defs.len() < 2 { return false; }

        // 前提1の読み方: ∠(a,b) = ∠(d,c)。未処理の定義と同値類の定義の組だけを、両方の順・両方を裏返した読み方で試す。
        let mut readings: Vec<[ClassId; 4]> = Vec::new();
        for &(x, y) in &pending {
            for &(z, w) in &defs {
                if (x, y) == (z, w) { continue; }
                readings.push([x, y, z, w]);
                readings.push([y, x, w, z]);
                readings.push([z, w, x, y]);
                readings.push([w, z, y, x]);
            }
        }
        readings.sort_unstable_by_key(|r| (r[0].0, r[1].0, r[2].0, r[3].0));
        readings.dedup();

        // (E,A,B,D,C)、方向 (EA,EB,ED,EC,AB,DC)、前提2の同値類のキー
        let mut found: Vec<([ClassId; 5], [ClassId; 6], (ClassId, bool))> = Vec::new();
        let mut work: u64 = 0;
        for [a, b, d, c] in readings {
            if a == b || d == c { continue; }
            // E: 方向 a の直線上の有限点で、方向 b・d・c の直線も通るもの。
            let lines_a: Vec<ClassId> = self.entities[a.0].components.first()
                .map(|cc| cc.subobjects.iter().map(|&s| self.get_rep(s))
                    .filter(|&s| s != self.line_infinity && self.entities[s.0].entity_type == EntityType::Line).collect())
                .unwrap_or_default();
            for la in lines_a {
                for e in self.sp_finite_points_on(la) {
                    work += 1;
                    if self.spiral_prop_work + work >= self.spiral_work_limit { break; }
                    let (Some(lb), Some(ld), Some(lc)) = (self.sp_line_with_dir(e, b), self.sp_line_with_dir(e, d), self.sp_line_with_dir(e, c))
                        else { continue };
                    let ls = [la, lb, ld, lc];
                    if (0..4).any(|i| (i + 1..4).any(|j| ls[i] == ls[j])) { continue; }
                    // A 側: A ∈ la、A を通る別の直線 lab と lb の交点が B。キーは ∠(a, dir(lab)) の同値類(向きつき)。
                    let mut side_a: rustc_hash::FxHashMap<(ClassId, bool), Vec<(ClassId, ClassId, ClassId)>> = rustc_hash::FxHashMap::default();
                    let pts_b = self.sp_finite_points_on(lb);
                    for pa in self.sp_finite_points_on(la) {
                        if pa == e { continue; }
                        for lab in self.sp_lines_through(pa) {
                            work += 1;
                            if lab == la { continue; }
                            let Some(dab) = self.sp_dir(lab) else { continue };
                            for pb in self.sp_finite_points_on(lab) {
                                if pb == e || pb == pa || !pts_b.contains(&pb) { continue; }
                                if let Some(k) = self.sp_angle(a, dab) { side_a.entry((k, false)).or_default().push((pa, pb, dab)); }
                                if let Some(k) = self.sp_angle(dab, a) { side_a.entry((k, true)).or_default().push((pa, pb, dab)); }
                            }
                        }
                    }
                    if side_a.is_empty() { continue; }
                    let pts_c = self.sp_finite_points_on(lc);
                    for pd in self.sp_finite_points_on(ld) {
                        if pd == e { continue; }
                        for ldc in self.sp_lines_through(pd) {
                            work += 1;
                            if ldc == ld { continue; }
                            let Some(ddc) = self.sp_dir(ldc) else { continue };
                            for pc in self.sp_finite_points_on(ldc) {
                                if pc == e || pc == pd || !pts_c.contains(&pc) { continue; }
                                let keys = [self.sp_angle(d, ddc).map(|k| (k, false)), self.sp_angle(ddc, d).map(|k| (k, true))];
                                for key in keys.into_iter().flatten() {
                                    if let Some(list) = side_a.get(&key) {
                                        for &(pa, pb, dab) in list {
                                            let pts = [e, pa, pb, pd, pc];
                                            if (0..5).any(|i| (i + 1..5).any(|j| pts[i] == pts[j])) { continue; }
                                            found.push(([e, pa, pb, pd, pc], [a, b, d, c, dab, ddc], key));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        self.spiral_prop_work += work;
        found.sort_unstable_by_key(|(p, _, _)| p.map(|x| x.0));
        found.dedup_by_key(|(p, _, _)| *p);

        let mut changed = false;
        for (pts, dirs, _) in found {
            if self.spiral_fired.len() >= MAX_FIRINGS { break; }
            if !self.spiral_fired.insert(pts.map(|x| x.0)) { continue; }
            changed |= self.spiral_conclude(pts, dirs, scalar);
        }
        changed
    }

    /// ∠(x1,y1) = ∠(x2,y2) を、どちらの向きで読んでも図に既にある角どうしでマージする。無ければ何もしない。
    fn sp_merge_angles(&mut self, (x1, y1): (ClassId, ClassId), (x2, y2): (ClassId, ClassId),
                       premises: &[(String, Vec<ClassId>)], center: ClassId) -> bool {
        let pair = match ((self.sp_angle(x1, y1), self.sp_angle(x2, y2)), (self.sp_angle(y1, x1), self.sp_angle(y2, x2))) {
            ((Some(p), Some(q)), _) | (_, (Some(p), Some(q))) => (p, q),
            _ => return false,
        };
        let (x, y) = pair;
        if self.get_rep(x) == self.get_rep(y) { return false; }
        // 判定不能(None)も通さない: 図が大きくなると評価できない実体が増え、誤ったマージが素通りしうる。
        if self.numeric_plausibility_check(x, y, 2) != Some(true) {
            println!("  🚫 [健全性チェック] {} の結論 {} ≡ {} は数値で確かめられないので却下",
                NAME, self.entities[self.get_rep(x).0].name, self.entities[self.get_rep(y).0].name);
            return false;
        }
        let justification = Justification::Theorem { name: NAME.to_string(), premises: premises.to_vec() };
        if self.merge_entities_justified(x, y, justification) {
            println!("  ⚙️ [E-Graph自動マージ] {}(中心 {})により結合: {} ≡ {}", NAME, self.entities[center.0].name,
                self.entities[self.get_rep(x).0].name, self.entities[self.get_rep(y).0].name);
            return true;
        }
        false
    }

    fn spiral_conclude(&mut self, [e, a, b, d, c]: [ClassId; 5], [dea, deb, ded, dec, dab, ddc]: [ClassId; 6], e_class: ClassId) -> bool {
        let mut premises = vec![("Identical".to_string(), vec![e_class, e_class])];
        if let (Some(p), Some(q)) = (self.sp_angle(dea, deb), self.sp_angle(ded, dec)) { premises[0].1 = vec![p, q]; }
        if let (Some(p), Some(q)) = (self.sp_angle(dea, dab), self.sp_angle(ded, ddc)) {
            premises.push(("Identical".to_string(), vec![p, q]));
        } else if let (Some(p), Some(q)) = (self.sp_angle(dab, dea), self.sp_angle(ddc, ded)) {
            premises.push(("Identical".to_string(), vec![p, q]));
        }
        let mut changed = false;
        // 中点の対応: 中点 M・N と直線 EM・EN が図にあるときだけ。
        let mid = |s: &Self, p: ClassId, q: ClassId| s.memo.get(&s.normalize_definition(&Definition::Midpoint(p, q))).map(|&m| s.get_rep(m));
        if let (Some(m), Some(n)) = (mid(self, a, b), mid(self, d, c)) {
            let dem = self.find_common_line(&[e, m]).and_then(|l| self.sp_dir(l));
            let den = self.find_common_line(&[e, n]).and_then(|l| self.sp_dir(l));
            if let (Some(dem), Some(den)) = (dem, den) {
                changed |= self.sp_merge_angles((dea, dem), (ded, den), &premises, e);
                changed |= self.sp_merge_angles((dem, dab), (den, ddc), &premises, e);
            }
        }
        // 対になる相似 △EAD ∽ △EBC: 直線 AD・BC が図にあるときだけ。
        let dad = self.find_common_line(&[a, d]).and_then(|l| self.sp_dir(l));
        let dbc = self.find_common_line(&[b, c]).and_then(|l| self.sp_dir(l));
        if let (Some(dad), Some(dbc)) = (dad, dbc) {
            changed |= self.sp_merge_angles((dea, dad), (deb, dbc), &premises, e);
        }
        changed
    }
}
