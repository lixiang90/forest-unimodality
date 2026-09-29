import ForestUnimodality.GaussianDirectionalDataT1PositiveDefs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataT1Positive

open PolynomialList BernsteinCertificate RationalCompactification

def matrix2 : List (List ℚ) := [
  [(197478415625/117546246144), (41107405625/208971104256), (744082025/23219011584), (3793655/644972544), (185881/143327232), (10463/31850496), (395/3538944)],
  [(68814988625/39182082048), (18701865275/104485552128), (291392035/11609505792), (1390991/358318080), (1238983/1791590400), (2065/15925248), (79/2949120)],
  [(41351222525/22856214528), (1642819435/10158317568), (262025431/13544423424), (5169533/2090188800), (131249/387072000), (101/2322432), (79/17203200)],
  [(364409876725/198087192576), (227747971/1572120576), (237714511/16303472640), (2989/1990656), (5665571/37739520000), (199/16773120), (79/186368000)],
  [(34921170305/18865446912), (28241729069/220096880640), (388367/36391680), (99329/116121600), (87749/1509580800), (79/33546240), 0],
  [(447699301541/242106568704), (77266333/689762304), (25093901/3335904000), (6194239/13837824000), (867/46592000), (79/307507200), 0],
  [(1857837332191/1008777369600), (897049961/9340531200), (1190993/235872000), (4289/20592000), (97/21964800), 0, 0],
  [(220687137457/120092544000), (805858853/10007712000), (551489/173745000), (8401/102960000), (97/164736000), 0, 0],
  [(3697038689/2001542400), (29205043/444787200), (1348517/741312000), (133/5491200), 0, 0, 0],
  [(21956689439/11675664000), (133914133/2594592000), (1306589/1441440000), (19/4576000), 0, 0, 0],
  [(13792343/7076160), (2837/73710), (187/524160), 0, 0, 0, 0],
  [(8699599/4212000), (43189/1638000), (187/2184000), 0, 0, 0, 0],
  [(339557/151200), (37/2400), 0, 0, 0, 0, 0],
  [(316769/126000), (37/6000), 0, 0, 0, 0, 0],
  [(349/120), 0, 0, 0, 0, 0, 0],
  [(349/100), 0, 0, 0, 0, 0, 0]
]

def cert2 : Certificate₂ := ⟨15, 6, fun i j => (matrix2[i.val]!).getD j.val 0⟩

theorem leaf2_coeff_nonneg : ∀ i j, 0 ≤ cert2.coeff i j := by decide +kernel

theorem leaf2_identity (x y : ℝ) :
    evalReal₂ compact (((1/2) : ℝ) + (1 - (1/2)) * x)
      ((0 : ℝ) + (1 - 0) * y) = value₂ cert2 x y := by
  dsimp only [value₂, cert2]
  norm_num [compact, value₂, cert2, matrix2, evalReal₂, eval, evalList,
    liftEvaluation, rationalEvaluation, List.finRange, List.ofFn_succ]
  norm_num [cert2, matrix2, Nat.choose]
  ring

theorem leaf2_nonneg : ∀ x ∈ Set.Icc ((1/2) : ℝ) 1,
    ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ evalReal₂ compact x y := by
  intro x hx y hy
  exact box_nonneg_of_identity compact (1/2) 1 0 1 cert2 (by norm_num) (by norm_num)
    leaf2_coeff_nonneg (by simpa using leaf2_identity) (by simpa using hx) (by simpa using hy)
#print axioms leaf2_nonneg

end ForestUnimodality.GaussianDirectionalDataT1Positive
