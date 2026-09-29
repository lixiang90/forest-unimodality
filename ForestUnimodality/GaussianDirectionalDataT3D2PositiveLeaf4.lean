import ForestUnimodality.GaussianDirectionalDataT3D2PositiveDefs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataT3D2Positive

open PolynomialList BernsteinCertificate RationalCompactification

def matrix4 : List (List ℚ) := [
  [(105084231021875/85691213438976), (762165456875/6347497291776), (9944035475/470184984576), (138526805/34828517376), (2613203/2579890176), (13823/47775744), (125/884736)],
  [(18051719076625/14281868906496), (334100236475/3173748645888), (3738736615/235092492288), (6070987/2418647040), (16988429/32248627200), (5405/47775744), (5/147456)],
  [(164897629075/130173284304), (16128110705/176319369216), (1614183437/137137287168), (87356149/56435097600), (2260619/8957952000), (2081/55738368), (1/172032)],
  [(11145953670025/9025347711744), (210409973069/2674177099776), (1404364547/165072660480), (560965/611380224), (10625539/97044480000), (2027/201277440), (1/1863680)],
  [(7054218665915/6016898474496), (446202240011/6685442749440), (983583961/165072660480), (186943/363916800), (56681/1358622720), (5/2515968), 0],
  [(11979985197989/11030980536576), (15126186821/272369889792), (30346144013/7565830272000), (24803633/93405312000), (54827/4151347200), (1/4612608), 0],
  [(45278682914089/45962418902400), (3934987187/87298041600), (270016913/105080976000), (27253/222393600), (7/2246400), 0, 0],
  [(4815728874103/5471716536000), (3923775433/110539728000), (173939539/112586760000), (26551/555984000), (7/16848000), 0, 0],
  [(71243945891/91195275600), (182305333/6755205600), (127859/150115680), (131/9266400), 0, 0, 0],
  [(46357750627/66496555125), (194100497/9851341500), (120353/291891600), (131/54054000), 0, 0, 0],
  [(408861043/644815080), (196181/14329224), (53/331695), 0, 0, 0, 0],
  [(1600246043/2686729500), (176327/19901700), (106/2764125), 0, 0, 0, 0],
  [(80467/137781), (128/25515), 0, 0, 0, 0, 0],
  [(138578/229635), (256/127575), 0, 0, 0, 0, 0],
  [(1456/2187), 0, 0, 0, 0, 0, 0],
  [(2912/3645), 0, 0, 0, 0, 0, 0]
]

def cert4 : Certificate₂ := ⟨15, 6, fun i j => (matrix4[i.val]!).getD j.val 0⟩

theorem leaf4_coeff_nonneg : ∀ i j, 0 ≤ cert4.coeff i j := by decide +kernel

theorem leaf4_identity (x y : ℝ) :
    evalReal₂ compact (((1/2) : ℝ) + (1 - (1/2)) * x)
      ((0 : ℝ) + (1 - 0) * y) = value₂ cert4 x y := by
  dsimp only [value₂, cert4]
  norm_num [compact, value₂, cert4, matrix4, evalReal₂, eval, evalList,
    liftEvaluation, rationalEvaluation, List.finRange, List.ofFn_succ]
  norm_num [cert4, matrix4, Nat.choose]
  ring

theorem leaf4_nonneg : ∀ x ∈ Set.Icc ((1/2) : ℝ) 1,
    ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ evalReal₂ compact x y := by
  intro x hx y hy
  exact box_nonneg_of_identity compact (1/2) 1 0 1 cert4 (by norm_num) (by norm_num)
    leaf4_coeff_nonneg (by simpa using leaf4_identity) (by simpa using hx) (by simpa using hy)
#print axioms leaf4_nonneg

end ForestUnimodality.GaussianDirectionalDataT3D2Positive
