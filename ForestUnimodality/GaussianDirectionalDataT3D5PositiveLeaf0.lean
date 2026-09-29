import ForestUnimodality.GaussianDirectionalDataT3D5PositiveDefs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataT3D5Positive

open PolynomialList BernsteinCertificate RationalCompactification

def matrix0 : List (List ℚ) := [
  [(173295363584/261508830075), (714397952/1937102445), (1314738016/1793613375), (4744708/13286025), (208174/2460375), (511/7290), (128/675)],
  [(327181192448/435848050125), (6947935168/9685512225), (4367007088/8968066875), (300904/1476225), (1204349/12301875), (1442/18225), (64/1125)],
  [(1055081489152/1016978783625), (6106441216/7533176175), (1043986336/2989355625), (94393/688905), (1256063/19136250), (1361/42525), (32/2625)],
  [(1333779353728/881381612475), (25911824368/32643763425), (77496352/287863875), (108802/1148175), (5817463/165847500), (1307/122850), (16/11375)],
  [(89999516192/41970552975), (24525995576/32643763425), (17311498/80601885), (308206/4975425), (132943/8292375), (32/12285), 0],
  [(3101797191824/1077244193025), (173218516/241805655), (1256368181/7388506125), (209149/5613300), (11351/1842750), (16/45045), 0],
  [(6577986158552/1795406988375), (611705324/886620735), (40989541/315748125), (7988/394875), (863/482625), 0, 0],
  [(381327378772/85495570875), (1256102447/1899901575), (329926379/3518336250), (41018/4343625), (863/2895750), 0, 0],
  [(2731253024/518154975), (261910709/422200350), (7348778/117277875), (989/289575), 0, 0, 0],
  [(572626534/93002175), (554848067/985134150), (3384463/91216125), (989/1351350), 0, 0, 0],
  [(1168101923/161203770), (125063/255879), (1178/66339), 0, 0, 0, 0],
  [(670753189/76763700), (787547/1990170), (589/110565), 0, 0, 0, 0],
  [(1506053/137781), (1430/5103), 0, 0, 0, 0, 0],
  [(1316351/91854), (715/5103), 0, 0, 0, 0, 0],
  [(43625/2187), 0, 0, 0, 0, 0, 0],
  [(43625/1458), 0, 0, 0, 0, 0, 0]
]

def cert0 : Certificate₂ := ⟨15, 6, fun i j => (matrix0[i.val]!).getD j.val 0⟩

theorem leaf0_coeff_nonneg : ∀ i j, 0 ≤ cert0.coeff i j := by decide +kernel

theorem leaf0_identity (x y : ℝ) :
    evalReal₂ compact ((0 : ℝ) + (1 - 0) * x)
      ((0 : ℝ) + (1 - 0) * y) = value₂ cert0 x y := by
  dsimp only [value₂, cert0]
  norm_num [compact, value₂, cert0, matrix0, evalReal₂, eval, evalList,
    liftEvaluation, rationalEvaluation, List.finRange, List.ofFn_succ]
  norm_num [cert0, matrix0, Nat.choose]
  ring

theorem leaf0_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ evalReal₂ compact x y := by
  intro x hx y hy
  exact box_nonneg_of_identity compact 0 1 0 1 cert0 (by norm_num) (by norm_num)
    leaf0_coeff_nonneg (by simpa using leaf0_identity) (by simpa using hx) (by simpa using hy)
#print axioms leaf0_nonneg

end ForestUnimodality.GaussianDirectionalDataT3D5Positive
