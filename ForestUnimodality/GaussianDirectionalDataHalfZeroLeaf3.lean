import ForestUnimodality.GaussianDirectionalDataHalfZeroDefs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataHalfZero

open PolynomialList BernsteinCertificate RationalCompactification

def matrix3 : List (List ℚ) := [
  [(21578515625/272097792), 0, (1555015625/3386105856), 0, (4756025/376233984), 0, (1847605/2006581248), 0, (25/73728)],
  [(65219453125/589545216), 0, (3600021875/7336562688), 0, (32075/3354624), 0, (2103923/4347592704), 0, (5/53248)],
  [(14852984375/98257536), 0, (3748656875/7336562688), 0, (6145/870912), 0, (1695011/7245987840), 0, (1/53248)],
  [(36524084375/180138816), 0, (774724375/1494484992), 0, (208825/41513472), 0, (6831631/66421555200), 0, (3/1464320)],
  [(365046625/1364688), 0, (63671975/124540416), 0, (569/166400), 0, (4481/110702592), 0, 0],
  [(870035875/2501928), 0, (91148485/186810624), 0, (1881709/864864000), 0, (3827/276756480), 0, 0],
  [(186042275/416988), 0, (1687729/3773952), 0, (415/329472), 0, (5/1317888), 0, 0],
  [(1512020/2673), 0, (13454377/34594560), 0, (81/128128), 0, (1/1537536), 0, 0],
  [(16435921/23166), 0, (12365/39312), 0, (1/4004), 0, 0, 0, 0],
  [(85047881/96525), 0, (2491/10920), 0, (3/50050), 0, 0, 0, 0],
  [(126850/117), 0, (25/182), 0, 0, 0, 0, 0, 0],
  [(51580/39), 0, (5/91), 0, 0, 0, 0, 0, 0],
  [1600, 0, 0, 0, 0, 0, 0, 0, 0],
  [1920, 0, 0, 0, 0, 0, 0, 0, 0]
]

def cert3 : Certificate₂ := ⟨13, 8, fun i j => (matrix3[i.val]!).getD j.val 0⟩

theorem leaf3_coeff_nonneg : ∀ i j, 0 ≤ cert3.coeff i j := by decide +kernel

theorem leaf3_identity (x y : ℝ) :
    evalReal₂ compact (((1/2) : ℝ) + (1 - (1/2)) * x)
      ((0 : ℝ) + (1 - 0) * y) = value₂ cert3 x y := by
  dsimp only [value₂, cert3]
  norm_num [compact, value₂, cert3, matrix3, evalReal₂, eval, evalList,
    liftEvaluation, rationalEvaluation, List.finRange, List.ofFn_succ]
  norm_num [cert3, matrix3, Nat.choose]
  ring

theorem leaf3_nonneg : ∀ x ∈ Set.Icc ((1/2) : ℝ) 1,
    ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ evalReal₂ compact x y := by
  intro x hx y hy
  exact box_nonneg_of_identity compact (1/2) 1 0 1 cert3 (by norm_num) (by norm_num)
    leaf3_coeff_nonneg (by simpa using leaf3_identity) (by simpa using hx) (by simpa using hy)

#print axioms leaf3_nonneg
end ForestUnimodality.GaussianDirectionalDataHalfZero
