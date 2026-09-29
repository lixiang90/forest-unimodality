import ForestUnimodality.JointDirectionGraph
import ForestUnimodality.JointDirectionBudget

/-! Exact normalization of the common Fourier-error measure, including
all square-root scales. No numerical envelope is assumed here. -/
namespace ForestUnimodality.JointDirectionScaling
open Real JointDirectionGraph JointDirectionBudget DirectionalErrorLayerBudget DirectionalMomentMonotonicity

theorem shared_error_scaled {m delta r L Z T:ℝ}
    (hm:0<m) (hd:0<delta) (_hr:0≤r) (_hL:0≤L) (hZ:0≤Z) (hT:0≤T)
    (hratio:r≤L*delta^2) :
    sqrt (Z*(delta^2*Z+r*T))≤delta/sqrt m*
      sqrt ((sqrt m*Z)^2+(L/m)*(sqrt m*Z)*(m*sqrt m*T)) := by
  have hs : sqrt m≠0 := (sqrt_pos.mpr hm).ne'
  have ha : (sqrt m*Z)^2+(L/m)*(sqrt m*Z)*(m*sqrt m*T)=m*(Z^2+L*Z*T) := by
    field_simp
    rw [sq_sqrt hm.le]
    ring
  rw [ha,sqrt_mul hm.le]
  have he : delta/sqrt m*(sqrt m*sqrt (Z^2+L*Z*T))=delta*sqrt (Z^2+L*Z*T) := by field_simp
  rw [he,←sqrt_sq hd.le,←sqrt_mul (sq_nonneg delta)]
  apply sqrt_le_sqrt
  rw [sq_sqrt (sq_nonneg delta)]
  nlinarith [mul_le_mul_of_nonneg_right hratio (mul_nonneg hZ hT)]

theorem normalizer_lower {v V m:ℝ} (hv:0<v) (hm:0<m) (hvV:v≤V) :
    1/sqrt m≤normalizer v m*sqrt (2*Real.pi*V) := by
  have hs : sqrt m≠0 := (sqrt_pos.mpr hm).ne'
  have hvs : sqrt (2*Real.pi*v)≠0 := (sqrt_pos.mpr (by positivity)).ne'
  have hle : sqrt (2*Real.pi*v)≤sqrt (2*Real.pi*V) := sqrt_le_sqrt (by gcongr)
  calc
    1/sqrt m=sqrt (2*Real.pi*v)/(sqrt (2*Real.pi*v)*sqrt m) := by field_simp
    _≤sqrt (2*Real.pi*V)/(sqrt (2*Real.pi*v)*sqrt m) :=
      div_le_div_of_nonneg_right hle (by positivity)
    _=normalizer v m*sqrt (2*Real.pi*V) := by
      unfold normalizer
      simp only [sqrt_mul (show 0≤2*Real.pi by positivity),sqrt_mul hv.le]
      ring

theorem error_bound (p:Parameters) (hp:Valid p) {m vq r:ℝ}
    (hm:p.start≤m) (hvq:0<vq) (hV:vq≤p.V) (hr:0≤r) (hr1:r<1)
    (hL:r≤p.lfactor*(1-r)^2) :
    sqrt (zeroBudget (4/9) m p.v p.eta p.D*((1-r)^2*zeroBudget (4/9) m p.v p.eta p.D+
      r*twoBudget (4/9) m p.v p.eta p.D))≤
      normalizer vq m*(1-r)*JointDirectionBudget.finiteError p m := by
  rcases hp with ⟨hs,hv,hVV,heta,hD,hR,hamp,hLf,rest⟩
  have hm0:=hs.trans_le hm
  have ham:1<(4/9)*m := (show 1<(4/9)*p.start from rest.2.2.2.1).trans_le
    (mul_le_mul_of_nonneg_left hm (by norm_num))
  have hu0:=uZero_nonneg (by norm_num : (0:ℝ)<4/9) hv heta hD hm0 ham
  have hu2:=uTwo_nonneg (by norm_num : (0:ℝ)<4/9) hv heta hD hm0 ham
  have hze:=uZero_eq (eta:=p.eta) (D:=p.D) (by norm_num : (0:ℝ)<4/9) hv hm0 ham
  have hte:=uTwo_eq (eta:=p.eta) (D:=p.D) (by norm_num : (0:ℝ)<4/9) hv hm0 ham
  have hZ:0≤zeroBudget (4/9) m p.v p.eta p.D := by rw [hze] at hu0;exact nonneg_of_mul_nonneg_right hu0 (sqrt_pos.mpr hm0)
  have hT:0≤twoBudget (4/9) m p.v p.eta p.D := by rw [hte] at hu2;exact nonneg_of_mul_nonneg_right hu2 (mul_pos hm0 (sqrt_pos.mpr hm0))
  have he:=shared_error_scaled hm0 (sub_pos.mpr hr1) hr hLf hZ hT hL
  rw [←hze,←hte] at he
  have hn:=normalizer_lower hvq hm0 hV
  have hn':=mul_le_mul_of_nonneg_right hn (mul_nonneg (sub_nonneg.mpr hr1.le)
    (sqrt_nonneg (uZero (4/9) p.v p.eta p.D m^2+p.lfactor/m*uZero (4/9) p.v p.eta p.D m*uTwo (4/9) p.v p.eta p.D m)))
  unfold JointDirectionBudget.finiteError
  exact he.trans (by convert! hn' using 1 <;> ring)


theorem step_lower (p:Parameters) (hp:Valid p) {m vq r:ℝ}
    (hm:p.start≤m) (hvq:p.v≤vq) (hr:0≤r) (hr1:r<1) (hamp:r/(1-r)≤p.amp) :
    -JointDirectionBudget.step p m≤r/(1-r)*
      (curve p m*(1/sqrt (vq*m))^2/2-Profile.gamma*(1/sqrt (vq*m))^4/24) := by
  rcases hp with ⟨hs,hv,hV,heta,hD,hR,hamp0,rest⟩
  have hm0:=hs.trans_le hm
  have hvq0:=hv.trans_le hvq
  have hsq : (1/sqrt (vq*m))^2=1/(vq*m) := by rw [div_pow,one_pow,sq_sqrt (mul_pos hvq0 hm0).le]
  have hfour : (1/sqrt (vq*m))^4=1/(vq^2*m^2) := by
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,hsq];ring
  rw [hsq,hfour]
  have hmax : 0≤max 0 (-curve p m) := le_max_left _ _
  have hc : -max 0 (-curve p m)≤curve p m := by linarith [le_max_right 0 (-curve p m)]
  have hdiv : max 0 (-curve p m)/(2*vq*m)≤max 0 (-curve p m)/(2*p.v*m) :=
    div_le_div_of_nonneg_left hmax (by positivity) (by gcongr)
  have hgamma : Profile.gamma/(24*vq^2*m^2)≤Profile.gamma/(24*p.v^2*m^2) :=
    div_le_div_of_nonneg_left Profile.gamma_pos.le (by positivity) (by gcongr)
  have hbase := div_le_div_of_nonneg_right hc (show 0≤2*vq*m by positivity)
  have hlower : -(max 0 (-curve p m)/(2*p.v*m)+Profile.gamma/(24*p.v^2*m^2))≤
      curve p m*(1/(vq*m))/2-Profile.gamma*(1/(vq^2*m^2))/24 := by
    have he : curve p m*(1/(vq*m))/2-Profile.gamma*(1/(vq^2*m^2))/24=
        curve p m/(2*vq*m)-Profile.gamma/(24*vq^2*m^2) := by ring
    rw [he]
    simp only [neg_div] at hbase
    linarith
  have hgp:=Profile.gamma_pos
  have hq : 0≤max 0 (-curve p m)/(2*p.v*m)+Profile.gamma/(24*p.v^2*m^2) := by positivity
  have ha:=mul_le_mul_of_nonneg_right hamp hq
  have hb:=mul_le_mul_of_nonneg_left hlower (div_nonneg hr (sub_nonneg.mpr hr1.le))
  unfold JointDirectionBudget.step
  linarith

#print axioms shared_error_scaled
#print axioms normalizer_lower
#print axioms error_bound
end ForestUnimodality.JointDirectionScaling
