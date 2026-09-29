import ForestUnimodality.GaussianDirectionalDataHalfPositiveDefs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalDataHalfPositive

open PolynomialList BernsteinCertificate RationalCompactification

def matrix0 : List (List ℚ) := [
  [(407939584/358722675), (18643136/23914845), (18286304/22143375), (915266/2460375), (95302/820125), (161/1620), (8/45)],
  [(845986048/597871125), (634558208/597871125), (65772656/110716875), (67018/273375), (497393/4100625), (7/81), (4/75)],
  [(2669860736/1395032625), (21314144/18600435), (119453744/258339375), (229037/1275750), (517931/6378750), (67/1890), (2/175)],
  [(15949820608/6045141375), (2319851264/2015047125), (9482696/24877125), (358928/2764125), (349333/7897500), (1/84), (3/2275)],
  [(7208517152/2015047125), (2303876668/2015047125), (7951898/24877125), (80809/921375), (11423/552825), (4/1365), 0],
  [(6960106096/1477701225), (3415864/2985255), (24015769/91216125), (26201/482625), (991/122850), (2/5005), 0],
  [(593276344/98513415), (314472248/273648375), (10551416/50675625), (4852/160875), (76/32175), 0, 0],
  [(882829316/117277875), (5364682/4691115), (306724/1974375), (2302/160875), (38/96525), 0, 0],
  [(363370936/39092625), (14517068/13030875), (154552/1447875), (56/10725), 0, 0, 0],
  [(1046956028/91216125), (31957964/30405375), (72692/1126125), (4/3575), 0, 0, 0],
  [(7929976/552825), (104632/110565), (128/4095), 0, 0, 0, 0],
  [(16885948/921375), (1940/2457), (64/6825), 0, 0, 0, 0],
  [(113968/4725), (128/225), 0, 0, 0, 0, 0],
  [(51848/1575), (64/225), 0, 0, 0, 0, 0],
  [(704/15), 0, 0, 0, 0, 0, 0],
  [(352/5), 0, 0, 0, 0, 0, 0]
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
end ForestUnimodality.GaussianDirectionalDataHalfPositive
