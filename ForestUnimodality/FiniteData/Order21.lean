import ForestUnimodality.KernelCertificate
import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_21_11_1_checked :
    (Witness.rising).check 21 11 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_11_2_checked :
    (Witness.rising).check 21 11 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_11_3_checked :
    (Witness.rising).check 21 11 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_11_4_checked :
    (Witness.rising).check 21 11 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_11_5_checked :
    (Witness.rising).check 21 11 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_11_6 : Certificate := {
  objectiveScale := 121275000
  eta := 6548267880
  rows := #[⟨.count 2, 1455170640⟩, ⟨.count 3, 346361400⟩, ⟨.count 4, 138544560⟩, ⟨.count 5, 121275000⟩, ⟨.path 6, 17323200⟩, ⟨.path 7, 34650693⟩, ⟨.privateRow 6 0, 2808190⟩, ⟨.privateRow 7 0, 6927228⟩, ⟨.hall 5 2, 2013165⟩, ⟨.hall 4 3, 1855854⟩]
  caps := #[0, 274050, 42168, 132093, 53640, 0, 2435, 14553, 0, 0, 0] }

theorem case_21_11_6_checked :
    (Witness.linear .positive case_21_11_6).check 21 11 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_12_1_checked :
    (Witness.rising).check 21 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_12_2_checked :
    (Witness.rising).check 21 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_12_3_checked :
    (Witness.rising).check 21 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_12_4_checked :
    (Witness.rising).check 21 12 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_12_5_checked :
    (Witness.rising).check 21 12 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_12_6 : Certificate := {
  objectiveScale := 9375
  eta := 618660
  rows := #[⟨.count 2, 150045⟩, ⟨.count 3, 40185⟩, ⟨.count 4, 13380⟩, ⟨.count 5, 9360⟩, ⟨.path 6, 4018⟩]
  caps := #[0, 156, 0, 0, 13, 15, 0, 0, 0, 0] }

theorem case_21_12_6_checked :
    (Witness.linear .positive case_21_12_6).check 21 12 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_12_7 : Certificate := {
  objectiveScale := 809400000
  eta := 49226736720
  rows := #[⟨.count 2, 12806407740⟩, ⟨.count 3, 4201757280⟩, ⟨.count 4, 1692941040⟩, ⟨.count 5, 1015311360⟩, ⟨.count 6, 362044620⟩, ⟨.count 8, 809076240⟩, ⟨.path 5, 472946040⟩, ⟨.privateRow 3 7, 200002740⟩, ⟨.privateRow 4 5, 313743675⟩, ⟨.privateRow 4 6, 354773510⟩, ⟨.privateRow 5 3, 291902016⟩, ⟨.privateRow 5 4, 86176818⟩, ⟨.privateRow 6 1, 179369785⟩, ⟨.privateRow 7 0, 74882990⟩, ⟨.hall 2 9, 860635020⟩, ⟨.assumptionRow 7, 541852830⟩]
  caps := #[0, 4656480, 1329300, 328440, 202740, 0, 721715, 0, 323760, 0] }

theorem case_21_12_7_checked :
    (Witness.linear .conditional case_21_12_7).check 21 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_13_1_checked :
    (Witness.rising).check 21 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_13_2_checked :
    (Witness.rising).check 21 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_13_3_checked :
    (Witness.rising).check 21 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_13_4_checked :
    (Witness.rising).check 21 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_13_5_checked :
    (Witness.rising).check 21 13 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_13_6 : Certificate := {
  objectiveScale := 2
  eta := 42
  rows := #[⟨.assumptionRow 6, 5⟩]
  caps := #[0, 0, 17, 8, 5, 5, 7, 2, 0] }

theorem case_21_13_6_checked :
    (Witness.linear .conditional case_21_13_6).check 21 13 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_13_7 : Certificate := {
  objectiveScale := 5881200000
  eta := 517641169500
  rows := #[⟨.count 2, 127580871600⟩, ⟨.count 3, 41652128700⟩, ⟨.count 4, 16277985360⟩, ⟨.count 5, 9108508500⟩, ⟨.count 6, 1976083200⟩, ⟨.path 5, 3920666400⟩, ⟨.privateRow 2 11, 5526857700⟩, ⟨.privateRow 3 8, 7544109300⟩, ⟨.privateRow 3 9, 3000147150⟩, ⟨.privateRow 4 5, 1960027524⟩, ⟨.privateRow 4 6, 5074519905⟩, ⟨.privateRow 5 3, 2940452970⟩, ⟨.privateRow 5 4, 600235272⟩, ⟨.privateRow 6 1, 1593805200⟩, ⟨.privateRow 7 0, 701333100⟩, ⟨.privateRow 8 0, 972603450⟩, ⟨.assumptionRow 7, 5194079800⟩]
  caps := #[0, 0, 22769600, 2809800, 0, 17353168, 44109000, 0, 45579300] }

theorem case_21_13_7_checked :
    (Witness.linear .conditional case_21_13_7).check 21 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_13_8 : Certificate := {
  objectiveScale := 1149284500000
  eta := 138529926635100
  rows := #[⟨.count 2, 32707717442400⟩, ⟨.count 3, 8791336854300⟩, ⟨.count 4, 2451561752640⟩, ⟨.count 5, 462701939700⟩, ⟨.path 4, 1059855756960⟩, ⟨.path 5, 464557632000⟩, ⟨.privateRow 2 11, 2396947753200⟩, ⟨.privateRow 3 8, 1782540259500⟩, ⟨.privateRow 3 9, 1648533686800⟩, ⟨.privateRow 4 5, 243032297508⟩, ⟨.privateRow 4 6, 1412757971625⟩, ⟨.privateRow 4 7, 686720474440⟩, ⟨.privateRow 5 3, 292538876630⟩, ⟨.privateRow 5 4, 943305134772⟩, ⟨.privateRow 6 1, 195049998000⟩, ⟨.privateRow 6 2, 402019718100⟩, ⟨.privateRow 7 0, 255732219600⟩, ⟨.privateRow 8 0, 115043378450⟩]
  caps := #[0, 35505508500, 1985629800, 4953290125, 1966900320, 8824953508, 0, 37335327900, 0] }

theorem case_21_13_8_checked :
    (Witness.linear .negative case_21_13_8).check 21 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_14_1_checked :
    (Witness.rising).check 21 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_14_2_checked :
    (Witness.rising).check 21 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_14_3_checked :
    (Witness.rising).check 21 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_14_4_checked :
    (Witness.rising).check 21 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_14_5_checked :
    (Witness.rising).check 21 14 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_14_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0] }

theorem case_21_14_6_checked :
    (Witness.linear .positive case_21_14_6).check 21 14 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_14_7 : Certificate := {
  objectiveScale := 7
  eta := 196
  rows := #[⟨.assumptionRow 7, 12⟩]
  caps := #[0, 0, 73, 32, 17, 12, 56, 30] }

theorem case_21_14_7_checked :
    (Witness.linear .conditional case_21_14_7).check 21 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_14_8 : Certificate := {
  objectiveScale := 7
  eta := 51
  rows := #[⟨.assumptionRow 8, 5⟩]
  caps := #[0, 0, 28, 13, 8, 54, 96, 68] }

theorem case_21_14_8_checked :
    (Witness.linear .conditional case_21_14_8).check 21 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_15_1_checked :
    (Witness.rising).check 21 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_15_2_checked :
    (Witness.rising).check 21 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_15_3_checked :
    (Witness.rising).check 21 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_15_4_checked :
    (Witness.rising).check 21 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_15_5_checked :
    (Witness.rising).check 21 15 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_15_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0] }

theorem case_21_15_6_checked :
    (Witness.linear .positive case_21_15_6).check 21 15 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_15_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_21_15_7_checked :
    (Witness.linear .positive case_21_15_7).check 21 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_15_8 : Certificate := {
  objectiveScale := 24
  eta := 264
  rows := #[⟨.assumptionRow 8, 19⟩]
  caps := #[0, 0, 122, 52, 33, 735, 639] }

theorem case_21_15_8_checked :
    (Witness.linear .conditional case_21_15_8).check 21 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_15_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 42, 42] }

theorem case_21_15_9_checked :
    (Witness.linear .negative case_21_15_9).check 21 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_16_1_checked :
    (Witness.rising).check 21 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_16_2_checked :
    (Witness.rising).check 21 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_16_3_checked :
    (Witness.rising).check 21 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_16_4_checked :
    (Witness.rising).check 21 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_16_5_checked :
    (Witness.rising).check 21 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_16_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1] }

theorem case_21_16_6_checked :
    (Witness.linear .positive case_21_16_6).check 21 16 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_16_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_21_16_7_checked :
    (Witness.linear .positive case_21_16_7).check 21 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_16_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_21_16_8_checked :
    (Witness.linear .positive case_21_16_8).check 21 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_16_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 132, 132] }

theorem case_21_16_9_checked :
    (Witness.linear .negative case_21_16_9).check 21 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_16_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_21_16_10_checked :
    (Witness.linear .negative case_21_16_10).check 21 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_17_1_checked :
    (Witness.rising).check 21 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_17_2_checked :
    (Witness.rising).check 21 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_17_3_checked :
    (Witness.rising).check 21 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_17_4_checked :
    (Witness.rising).check 21 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_17_5_checked :
    (Witness.rising).check 21 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_17_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1] }

theorem case_21_17_6_checked :
    (Witness.linear .positive case_21_17_6).check 21 17 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_21_17_7_checked :
    (Witness.linear .positive case_21_17_7).check 21 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_17_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_21_17_8_checked :
    (Witness.linear .positive case_21_17_8).check 21 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_17_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 429, 429] }

theorem case_21_17_9_checked :
    (Witness.linear .negative case_21_17_9).check 21 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_17_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_21_17_10_checked :
    (Witness.linear .negative case_21_17_10).check 21 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_18_1_checked :
    (Witness.rising).check 21 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_18_2_checked :
    (Witness.rising).check 21 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_18_3_checked :
    (Witness.rising).check 21 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_18_4_checked :
    (Witness.rising).check 21 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_18_5_checked :
    (Witness.rising).check 21 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_18_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_21_18_6_checked :
    (Witness.linear .positive case_21_18_6).check 21 18 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_21_18_7_checked :
    (Witness.linear .positive case_21_18_7).check 21 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_18_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_21_18_8_checked :
    (Witness.linear .positive case_21_18_8).check 21 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_18_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_21_18_9_checked :
    (Witness.linear .positive case_21_18_9).check 21 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_18_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_21_18_10_checked :
    (Witness.linear .negative case_21_18_10).check 21 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_18_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_21_18_11_checked :
    (Witness.linear .negative case_21_18_11).check 21 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_19_1_checked :
    (Witness.rising).check 21 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_19_2_checked :
    (Witness.rising).check 21 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_19_3_checked :
    (Witness.rising).check 21 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_19_4_checked :
    (Witness.rising).check 21 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_19_5_checked :
    (Witness.rising).check 21 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_19_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_21_19_6_checked :
    (Witness.linear .positive case_21_19_6).check 21 19 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_19_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_21_19_7_checked :
    (Witness.linear .positive case_21_19_7).check 21 19 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_21_19_8_checked :
    (Witness.linear .positive case_21_19_8).check 21 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_19_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_21_19_9_checked :
    (Witness.linear .positive case_21_19_9).check 21 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_19_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_21_19_10_checked :
    (Witness.linear .negative case_21_19_10).check 21 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_19_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_21_19_11_checked :
    (Witness.linear .negative case_21_19_11).check 21 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_19_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_21_19_12_checked :
    (Witness.linear .negative case_21_19_12).check 21 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_20_1_checked :
    (Witness.rising).check 21 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_20_2_checked :
    (Witness.rising).check 21 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_20_3_checked :
    (Witness.rising).check 21 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_20_4_checked :
    (Witness.rising).check 21 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_21_20_5_checked :
    (Witness.rising).check 21 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_20_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_21_20_6_checked :
    (Witness.linear .positive case_21_20_6).check 21 20 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_20_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_21_20_7_checked :
    (Witness.linear .positive case_21_20_7).check 21 20 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_21_20_8_checked :
    (Witness.linear .positive case_21_20_8).check 21 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_21_20_9_checked :
    (Witness.linear .positive case_21_20_9).check 21 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_20_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_21_20_10_checked :
    (Witness.linear .positive case_21_20_10).check 21 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_20_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_21_20_11_checked :
    (Witness.linear .negative case_21_20_11).check 21 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_21_20_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_21_20_12_checked :
    (Witness.linear .negative case_21_20_12).check 21 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_21 (a k : ℕ) (h : Domain 21 a k) :
    ∃ w : Witness, w.check 21 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 11 ≤ a := by omega
  have haHi : a ≤ 20 := by omega
  interval_cases a

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_21_11_1_checked⟩

    · exact ⟨Witness.rising, case_21_11_2_checked⟩

    · exact ⟨Witness.rising, case_21_11_3_checked⟩

    · exact ⟨Witness.rising, case_21_11_4_checked⟩

    · exact ⟨Witness.rising, case_21_11_5_checked⟩

    · exact ⟨Witness.linear .positive case_21_11_6, case_21_11_6_checked⟩

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_21_12_1_checked⟩

    · exact ⟨Witness.rising, case_21_12_2_checked⟩

    · exact ⟨Witness.rising, case_21_12_3_checked⟩

    · exact ⟨Witness.rising, case_21_12_4_checked⟩

    · exact ⟨Witness.rising, case_21_12_5_checked⟩

    · exact ⟨Witness.linear .positive case_21_12_6, case_21_12_6_checked⟩

    · exact ⟨Witness.linear .conditional case_21_12_7, case_21_12_7_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_21_13_1_checked⟩

    · exact ⟨Witness.rising, case_21_13_2_checked⟩

    · exact ⟨Witness.rising, case_21_13_3_checked⟩

    · exact ⟨Witness.rising, case_21_13_4_checked⟩

    · exact ⟨Witness.rising, case_21_13_5_checked⟩

    · exact ⟨Witness.linear .conditional case_21_13_6, case_21_13_6_checked⟩

    · exact ⟨Witness.linear .conditional case_21_13_7, case_21_13_7_checked⟩

    · exact ⟨Witness.linear .negative case_21_13_8, case_21_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_21_14_1_checked⟩

    · exact ⟨Witness.rising, case_21_14_2_checked⟩

    · exact ⟨Witness.rising, case_21_14_3_checked⟩

    · exact ⟨Witness.rising, case_21_14_4_checked⟩

    · exact ⟨Witness.rising, case_21_14_5_checked⟩

    · exact ⟨Witness.linear .positive case_21_14_6, case_21_14_6_checked⟩

    · exact ⟨Witness.linear .conditional case_21_14_7, case_21_14_7_checked⟩

    · exact ⟨Witness.linear .conditional case_21_14_8, case_21_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_21_15_1_checked⟩

    · exact ⟨Witness.rising, case_21_15_2_checked⟩

    · exact ⟨Witness.rising, case_21_15_3_checked⟩

    · exact ⟨Witness.rising, case_21_15_4_checked⟩

    · exact ⟨Witness.rising, case_21_15_5_checked⟩

    · exact ⟨Witness.linear .positive case_21_15_6, case_21_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_21_15_7, case_21_15_7_checked⟩

    · exact ⟨Witness.linear .conditional case_21_15_8, case_21_15_8_checked⟩

    · exact ⟨Witness.linear .negative case_21_15_9, case_21_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_21_16_1_checked⟩

    · exact ⟨Witness.rising, case_21_16_2_checked⟩

    · exact ⟨Witness.rising, case_21_16_3_checked⟩

    · exact ⟨Witness.rising, case_21_16_4_checked⟩

    · exact ⟨Witness.rising, case_21_16_5_checked⟩

    · exact ⟨Witness.linear .positive case_21_16_6, case_21_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_21_16_7, case_21_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_21_16_8, case_21_16_8_checked⟩

    · exact ⟨Witness.linear .negative case_21_16_9, case_21_16_9_checked⟩

    · exact ⟨Witness.linear .negative case_21_16_10, case_21_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_21_17_1_checked⟩

    · exact ⟨Witness.rising, case_21_17_2_checked⟩

    · exact ⟨Witness.rising, case_21_17_3_checked⟩

    · exact ⟨Witness.rising, case_21_17_4_checked⟩

    · exact ⟨Witness.rising, case_21_17_5_checked⟩

    · exact ⟨Witness.linear .positive case_21_17_6, case_21_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_21_17_7, case_21_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_21_17_8, case_21_17_8_checked⟩

    · exact ⟨Witness.linear .negative case_21_17_9, case_21_17_9_checked⟩

    · exact ⟨Witness.linear .negative case_21_17_10, case_21_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_21_18_1_checked⟩

    · exact ⟨Witness.rising, case_21_18_2_checked⟩

    · exact ⟨Witness.rising, case_21_18_3_checked⟩

    · exact ⟨Witness.rising, case_21_18_4_checked⟩

    · exact ⟨Witness.rising, case_21_18_5_checked⟩

    · exact ⟨Witness.linear .positive case_21_18_6, case_21_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_21_18_7, case_21_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_21_18_8, case_21_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_21_18_9, case_21_18_9_checked⟩

    · exact ⟨Witness.linear .negative case_21_18_10, case_21_18_10_checked⟩

    · exact ⟨Witness.linear .negative case_21_18_11, case_21_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_21_19_1_checked⟩

    · exact ⟨Witness.rising, case_21_19_2_checked⟩

    · exact ⟨Witness.rising, case_21_19_3_checked⟩

    · exact ⟨Witness.rising, case_21_19_4_checked⟩

    · exact ⟨Witness.rising, case_21_19_5_checked⟩

    · exact ⟨Witness.linear .positive case_21_19_6, case_21_19_6_checked⟩

    · exact ⟨Witness.linear .positive case_21_19_7, case_21_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_21_19_8, case_21_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_21_19_9, case_21_19_9_checked⟩

    · exact ⟨Witness.linear .negative case_21_19_10, case_21_19_10_checked⟩

    · exact ⟨Witness.linear .negative case_21_19_11, case_21_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_21_19_12, case_21_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_21_20_1_checked⟩

    · exact ⟨Witness.rising, case_21_20_2_checked⟩

    · exact ⟨Witness.rising, case_21_20_3_checked⟩

    · exact ⟨Witness.rising, case_21_20_4_checked⟩

    · exact ⟨Witness.rising, case_21_20_5_checked⟩

    · exact ⟨Witness.linear .positive case_21_20_6, case_21_20_6_checked⟩

    · exact ⟨Witness.linear .positive case_21_20_7, case_21_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_21_20_8, case_21_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_21_20_9, case_21_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_21_20_10, case_21_20_10_checked⟩

    · exact ⟨Witness.linear .negative case_21_20_11, case_21_20_11_checked⟩

    · exact ⟨Witness.linear .negative case_21_20_12, case_21_20_12_checked⟩


#print axioms coverage_21
end ForestUnimodality.FiniteRows.FiniteData
