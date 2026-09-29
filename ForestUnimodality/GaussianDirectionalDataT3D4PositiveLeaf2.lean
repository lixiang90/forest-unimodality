import ForestUnimodality.GaussianDirectionalDataT3D4PositiveDefs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataT3D4Positive

open PolynomialList BernsteinCertificate RationalCompactification

def matrix2 : List (List ℚ) := [
  [(79571448090625/28563737812992), (20309219375/58773123072), (8253404575/156728328192), (51995665/5804752896), (165269/95551488), (11941/31850496), (115/1179648)],
  [(14176012792625/4760622968832), (38105781275/117546246144), (3335345255/78364164096), (39158291/6449725440), (1118867/1194393600), (4735/31850496), (23/983040)],
  [(17571019674325/5554060130304), (657807865/2176782336), (55149913/1632586752), (148618733/37623398400), (1082759/2322432000), (1867/37158912), (23/5734400)],
  [(40272918547325/12033796948992), (27676923311/99043596288), (102887021/3930301440), (3976691/1630347264), (5261479/25159680000), (1849/134184960), (69/186368000)],
  [(1012178138215/286518974976), (31662414817/123804495360), (1082608451/55024220160), (19137829/13586227200), (2573/31449600), (23/8386560), 0],
  [(13716204810223/3676993512192), (9589487/41513472), (35862404491/2521943424000), (92785373/124540416000), (10139/384384000), (23/76876800), 0],
  [(60529961494523/15320806300800), (8624767601/42032390400), (684206597/70053984000), (4981/14256000), (23/3660800), 0, 0],
  [(7676158650821/1823905512000), (8035145123/45034704000), (470163451/75057840000), (63751/463320000), (23/27456000), 0, 0],
  [(68718502979/15199212600), (251579/1667952), (9128267/2501928000), (23/561600), 0, 0, 0],
  [(217658409427/44331036750), (17897147/145945800), (8946089/4864860000), (23/3276000), 0, 0, 0],
  [(580456717/107469180), (124877/1326780), (23/31590), 0, 0, 0, 0],
  [(385687931/63969750), (5779/87750), (23/131625), 0, 0, 0, 0],
  [(7853228/1148175), (184/4725), 0, 0, 0, 0, 0],
  [(15110152/1913625), (368/23625), 0, 0, 0, 0, 0],
  [(33856/3645), 0, 0, 0, 0, 0, 0],
  [(67712/6075), 0, 0, 0, 0, 0, 0]
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

end ForestUnimodality.GaussianDirectionalDataT3D4Positive
