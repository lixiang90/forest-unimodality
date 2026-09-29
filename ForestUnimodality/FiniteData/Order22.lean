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

theorem case_22_11_1_checked :
    (Witness.rising).check 22 11 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_11_2_checked :
    (Witness.rising).check 22 11 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_11_3_checked :
    (Witness.rising).check 22 11 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_11_4_checked :
    (Witness.rising).check 22 11 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_11_5_checked :
    (Witness.rising).check 22 11 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_11_6 : Certificate := {
  objectiveScale := 255300000
  eta := 943588800
  rows := #[⟨.count 2, 3103120440⟩, ⟨.count 3, 716984520⟩, ⟨.count 4, 286650840⟩, ⟨.count 5, 255300000⟩, ⟨.path 6, 31482000⟩, ⟨.path 7, 80419500⟩, ⟨.privateRow 7 0, 16083900⟩, ⟨.hall 5 1, 11888470⟩, ⟨.hall 5 2, 3731635⟩, ⟨.hall 0 3, 119110215⟩, ⟨.hall 4 3, 4437114⟩, ⟨.hall 3 6, 8437665⟩, ⟨.hall 0 8, 5242160⟩, ⟨.hall 1 8, 15249920⟩]
  caps := #[0, 442260, 0, 0, 131160, 225300, 0, 0, 0, 0, 0, 0] }

theorem case_22_11_6_checked :
    (Witness.linear .positive case_22_11_6).check 22 11 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_12_1_checked :
    (Witness.rising).check 22 12 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_12_2_checked :
    (Witness.rising).check 22 12 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_12_3_checked :
    (Witness.rising).check 22 12 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_12_4_checked :
    (Witness.rising).check 22 12 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_12_5_checked :
    (Witness.rising).check 22 12 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_12_6 : Certificate := {
  objectiveScale := 53681250
  eta := 3558938040
  rows := #[⟨.count 2, 647954160⟩, ⟨.count 3, 154344330⟩, ⟨.count 4, 61546320⟩, ⟨.count 5, 53742600⟩, ⟨.path 6, 7824600⟩, ⟨.path 7, 15212755⟩, ⟨.privateRow 3 9, 343560⟩, ⟨.privateRow 4 5, 5429475⟩, ⟨.privateRow 5 2, 3803700⟩, ⟨.privateRow 5 3, 4908⟩, ⟨.privateRow 6 0, 2871180⟩, ⟨.privateRow 7 0, 2533755⟩, ⟨.hall 3 7, 71575⟩]
  caps := #[0, 0, 262080, 0, 38625, 0, 0, 10225, 0, 0, 0] }

theorem case_22_12_6_checked :
    (Witness.linear .positive case_22_12_6).check 22 12 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_12_7 : Certificate := {
  objectiveScale := 2454000000
  eta := 129605948640
  rows := #[⟨.count 2, 33014741760⟩, ⟨.count 3, 11788917840⟩, ⟨.count 4, 5206995360⟩, ⟨.count 5, 5198062800⟩, ⟨.count 6, 737966880⟩, ⟨.count 8, 2462638080⟩, ⟨.path 6, 981590400⟩, ⟨.privateRow 4 5, 350688870⟩, ⟨.privateRow 5 3, 385611744⟩, ⟨.privateRow 5 4, 604837380⟩, ⟨.privateRow 6 0, 371633760⟩, ⟨.privateRow 6 2, 70361088⟩, ⟨.privateRow 7 0, 207166680⟩, ⟨.hall 3 7, 378875105⟩, ⟨.hall 2 9, 2901295488⟩, ⟨.assumptionRow 7, 2358490320⟩]
  caps := #[0, 0, 7603680, 4163850, 756480, 1169616, 677520, 0, 0, 0, 0] }

theorem case_22_12_7_checked :
    (Witness.linear .conditional case_22_12_7).check 22 12 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_13_1_checked :
    (Witness.rising).check 22 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_13_2_checked :
    (Witness.rising).check 22 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_13_3_checked :
    (Witness.rising).check 22 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_13_4_checked :
    (Witness.rising).check 22 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_13_5_checked :
    (Witness.rising).check 22 13 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_13_6 : Certificate := {
  objectiveScale := 44000
  eta := 4355120
  rows := #[⟨.count 2, 924000⟩, ⟨.count 3, 220110⟩, ⟨.count 4, 66000⟩, ⟨.count 5, 44000⟩, ⟨.path 6, 22001⟩]
  caps := #[0, 1672, 126, 0, 3, 0, 0, 0, 0, 0] }

theorem case_22_13_6_checked :
    (Witness.linear .positive case_22_13_6).check 22 13 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_13_7 : Certificate := {
  objectiveScale := 5500000
  eta := 517116600
  rows := #[⟨.count 2, 128551500⟩, ⟨.count 3, 38530800⟩, ⟨.count 4, 16031400⟩, ⟨.count 5, 9424800⟩, ⟨.count 6, 7380450⟩, ⟨.path 6, 2690835⟩, ⟨.privateRow 3 8, 2926000⟩, ⟨.privateRow 3 9, 4787475⟩, ⟨.privateRow 4 5, 99330⟩, ⟨.privateRow 4 6, 3851925⟩, ⟨.privateRow 4 7, 1905750⟩, ⟨.privateRow 5 3, 625240⟩, ⟨.privateRow 5 4, 2447676⟩, ⟨.privateRow 6 1, 1014750⟩, ⟨.privateRow 6 2, 319550⟩, ⟨.privateRow 7 0, 739200⟩, ⟨.privateRow 8 0, 916300⟩, ⟨.assumptionRow 7, 6726720⟩]
  caps := #[0, 97680, 0, 62300, 0, 0, 21465, 0, 2200, 0] }

theorem case_22_13_7_checked :
    (Witness.linear .conditional case_22_13_7).check 22 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_13_8 : Certificate := {
  objectiveScale := 4724114500000
  eta := 1217982538264800
  rows := #[⟨.count 2, 225861803890800⟩, ⟨.count 3, 40461635768400⟩, ⟨.count 4, 4133465212800⟩, ⟨.count 9, 4489798420800⟩, ⟨.path 3, 23913171097200⟩, ⟨.path 4, 4133995034400⟩, ⟨.privateRow 2 11, 16649669143800⟩, ⟨.privateRow 3 7, 1897474332600⟩, ⟨.privateRow 3 8, 8857849662200⟩, ⟨.privateRow 3 9, 8658896954400⟩, ⟨.privateRow 4 4, 97991632200⟩, ⟨.privateRow 4 5, 2994980613240⟩, ⟨.privateRow 4 6, 5412924137775⟩, ⟨.privateRow 4 7, 3894425019100⟩, ⟨.privateRow 5 2, 59049503040⟩, ⟨.privateRow 5 3, 2142750357440⟩, ⟨.privateRow 5 4, 3571171410576⟩, ⟨.privateRow 5 5, 138079118100⟩, ⟨.privateRow 6 1, 1174626967800⟩, ⟨.privateRow 6 2, 1488433504250⟩, ⟨.privateRow 7 0, 1117359130800⟩, ⟨.privateRow 8 0, 462490809550⟩, ⟨.hall 2 10, 1388889663000⟩]
  caps := #[0, 0, 0, 0, 3423100705, 3652801024, 0, 20477590200, 0, 234316079200] }

theorem case_22_13_8_checked :
    (Witness.linear .negative case_22_13_8).check 22 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_14_1_checked :
    (Witness.rising).check 22 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_14_2_checked :
    (Witness.rising).check 22 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_14_3_checked :
    (Witness.rising).check 22 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_14_4_checked :
    (Witness.rising).check 22 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_14_5_checked :
    (Witness.rising).check 22 14 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_14_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0, 0] }

theorem case_22_14_6_checked :
    (Witness.linear .positive case_22_14_6).check 22 14 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_14_7 : Certificate := {
  objectiveScale := 5750000
  eta := 2277284625
  rows := #[⟨.count 2, 496765500⟩, ⟨.count 3, 111573000⟩, ⟨.count 4, 25274700⟩, ⟨.count 5, 5787375⟩, ⟨.count 6, 5692500⟩, ⟨.path 4, 13800864⟩]
  caps := #[0, 0, 65604, 0, 26164, 0, 57500, 0, 0] }

theorem case_22_14_7_checked :
    (Witness.linear .positive case_22_14_7).check 22 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_14_8 : Certificate := {
  objectiveScale := 78085000000
  eta := 23513860986000
  rows := #[⟨.count 2, 4666078494000⟩, ⟨.count 3, 971455485000⟩, ⟨.count 4, 199547779200⟩, ⟨.count 5, 11853303000⟩, ⟨.path 3, 79774695000⟩, ⟨.path 4, 171444740544⟩, ⟨.privateRow 2 12, 250465446000⟩, ⟨.privateRow 3 8, 56732656750⟩, ⟨.privateRow 3 9, 219371999000⟩, ⟨.privateRow 3 10, 113293526500⟩, ⟨.privateRow 4 6, 100783997160⟩, ⟨.privateRow 4 7, 138116748000⟩, ⟨.privateRow 5 3, 5433377400⟩, ⟨.privateRow 5 4, 89432312200⟩, ⟨.privateRow 5 5, 24737328000⟩, ⟨.privateRow 6 2, 52296871000⟩, ⟨.privateRow 7 0, 19519297875⟩, ⟨.privateRow 8 0, 7215054000⟩, ⟨.assumptionRow 8, 28176972250⟩]
  caps := #[0, 0, 0, 681241484, 76387694, 297615400, 165094000, 0, 8710381750] }

theorem case_22_14_8_checked :
    (Witness.linear .conditional case_22_14_8).check 22 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_15_1_checked :
    (Witness.rising).check 22 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_15_2_checked :
    (Witness.rising).check 22 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_15_3_checked :
    (Witness.rising).check 22 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_15_4_checked :
    (Witness.rising).check 22 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_15_5_checked :
    (Witness.rising).check 22 15 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_15_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0] }

theorem case_22_15_6_checked :
    (Witness.linear .positive case_22_15_6).check 22 15 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_15_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_22_15_7_checked :
    (Witness.linear .positive case_22_15_7).check 22 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_15_8 : Certificate := {
  objectiveScale := 11
  eta := 345
  rows := #[⟨.assumptionRow 8, 13⟩]
  caps := #[0, 0, 144, 62, 28, 15, 177, 129] }

theorem case_22_15_8_checked :
    (Witness.linear .conditional case_22_15_8).check 22 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_15_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 42, 42, 28] }

theorem case_22_15_9_checked :
    (Witness.linear .negative case_22_15_9).check 22 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_16_1_checked :
    (Witness.rising).check 22 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_16_2_checked :
    (Witness.rising).check 22 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_16_3_checked :
    (Witness.rising).check 22 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_16_4_checked :
    (Witness.rising).check 22 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_16_5_checked :
    (Witness.rising).check 22 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_16_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0] }

theorem case_22_16_6_checked :
    (Witness.linear .positive case_22_16_6).check 22 16 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_16_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_22_16_7_checked :
    (Witness.linear .positive case_22_16_7).check 22 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_16_8 : Certificate := {
  objectiveScale := 1
  eta := 105
  rows := #[⟨.assumptionRow 8, 2⟩]
  caps := #[0, 0, 36, 14, 6, 3, 5] }

theorem case_22_16_8_checked :
    (Witness.linear .conditional case_22_16_8).check 22 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_16_9 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 132, 132, 90] }

theorem case_22_16_9_checked :
    (Witness.linear .negative case_22_16_9).check 22 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_16_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 42] }

theorem case_22_16_10_checked :
    (Witness.linear .negative case_22_16_10).check 22 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_17_1_checked :
    (Witness.rising).check 22 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_17_2_checked :
    (Witness.rising).check 22 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_17_3_checked :
    (Witness.rising).check 22 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_17_4_checked :
    (Witness.rising).check 22 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_17_5_checked :
    (Witness.rising).check 22 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_17_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1] }

theorem case_22_17_6_checked :
    (Witness.linear .positive case_22_17_6).check 22 17 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_22_17_7_checked :
    (Witness.linear .positive case_22_17_7).check 22 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_17_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_22_17_8_checked :
    (Witness.linear .positive case_22_17_8).check 22 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_17_9 : Certificate := {
  objectiveScale := 288
  eta := 6045
  rows := #[⟨.assumptionRow 9, 215⟩]
  caps := #[0, 0, 2544, 1282, 572, 26411] }

theorem case_22_17_9_checked :
    (Witness.linear .conditional case_22_17_9).check 22 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_17_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 132] }

theorem case_22_17_10_checked :
    (Witness.linear .negative case_22_17_10).check 22 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_18_1_checked :
    (Witness.rising).check 22 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_18_2_checked :
    (Witness.rising).check 22 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_18_3_checked :
    (Witness.rising).check 22 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_18_4_checked :
    (Witness.rising).check 22 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_18_5_checked :
    (Witness.rising).check 22 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_18_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1] }

theorem case_22_18_6_checked :
    (Witness.linear .positive case_22_18_6).check 22 18 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_22_18_7_checked :
    (Witness.linear .positive case_22_18_7).check 22 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_18_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_22_18_8_checked :
    (Witness.linear .positive case_22_18_8).check 22 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_18_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_22_18_9_checked :
    (Witness.linear .positive case_22_18_9).check 22 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_18_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 429] }

theorem case_22_18_10_checked :
    (Witness.linear .negative case_22_18_10).check 22 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_18_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_22_18_11_checked :
    (Witness.linear .negative case_22_18_11).check 22 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_19_1_checked :
    (Witness.rising).check 22 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_19_2_checked :
    (Witness.rising).check 22 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_19_3_checked :
    (Witness.rising).check 22 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_19_4_checked :
    (Witness.rising).check 22 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_19_5_checked :
    (Witness.rising).check 22 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_19_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_22_19_6_checked :
    (Witness.linear .positive case_22_19_6).check 22 19 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_19_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_22_19_7_checked :
    (Witness.linear .positive case_22_19_7).check 22 19 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_22_19_8_checked :
    (Witness.linear .positive case_22_19_8).check 22 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_19_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_22_19_9_checked :
    (Witness.linear .positive case_22_19_9).check 22 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_19_10 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 1430] }

theorem case_22_19_10_checked :
    (Witness.linear .negative case_22_19_10).check 22 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_19_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_22_19_11_checked :
    (Witness.linear .negative case_22_19_11).check 22 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_19_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_22_19_12_checked :
    (Witness.linear .negative case_22_19_12).check 22 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_20_1_checked :
    (Witness.rising).check 22 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_20_2_checked :
    (Witness.rising).check 22 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_20_3_checked :
    (Witness.rising).check 22 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_20_4_checked :
    (Witness.rising).check 22 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_20_5_checked :
    (Witness.rising).check 22 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_20_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_22_20_6_checked :
    (Witness.linear .positive case_22_20_6).check 22 20 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_20_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_22_20_7_checked :
    (Witness.linear .positive case_22_20_7).check 22 20 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_22_20_8_checked :
    (Witness.linear .positive case_22_20_8).check 22 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_22_20_9_checked :
    (Witness.linear .positive case_22_20_9).check 22 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_20_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_22_20_10_checked :
    (Witness.linear .positive case_22_20_10).check 22 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_20_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_22_20_11_checked :
    (Witness.linear .negative case_22_20_11).check 22 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_20_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_22_20_12_checked :
    (Witness.linear .negative case_22_20_12).check 22 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_21_1_checked :
    (Witness.rising).check 22 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_21_2_checked :
    (Witness.rising).check 22 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_21_3_checked :
    (Witness.rising).check 22 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_21_4_checked :
    (Witness.rising).check 22 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_22_21_5_checked :
    (Witness.rising).check 22 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_21_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_22_21_6_checked :
    (Witness.linear .positive case_22_21_6).check 22 21 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_21_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_22_21_7_checked :
    (Witness.linear .positive case_22_21_7).check 22 21 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_22_21_8_checked :
    (Witness.linear .positive case_22_21_8).check 22 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_22_21_9_checked :
    (Witness.linear .positive case_22_21_9).check 22 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_21_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_22_21_10_checked :
    (Witness.linear .positive case_22_21_10).check 22 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_21_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_22_21_11_checked :
    (Witness.linear .negative case_22_21_11).check 22 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_21_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_22_21_12_checked :
    (Witness.linear .negative case_22_21_12).check 22 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_22_21_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_22_21_13_checked :
    (Witness.linear .negative case_22_21_13).check 22 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_22 (a k : ℕ) (h : Domain 22 a k) :
    ∃ w : Witness, w.check 22 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 11 ≤ a := by omega
  have haHi : a ≤ 21 := by omega
  interval_cases a

  · have hkHi : k ≤ 6 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_22_11_1_checked⟩

    · exact ⟨Witness.rising, case_22_11_2_checked⟩

    · exact ⟨Witness.rising, case_22_11_3_checked⟩

    · exact ⟨Witness.rising, case_22_11_4_checked⟩

    · exact ⟨Witness.rising, case_22_11_5_checked⟩

    · exact ⟨Witness.linear .positive case_22_11_6, case_22_11_6_checked⟩

  · have hkHi : k ≤ 7 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_22_12_1_checked⟩

    · exact ⟨Witness.rising, case_22_12_2_checked⟩

    · exact ⟨Witness.rising, case_22_12_3_checked⟩

    · exact ⟨Witness.rising, case_22_12_4_checked⟩

    · exact ⟨Witness.rising, case_22_12_5_checked⟩

    · exact ⟨Witness.linear .positive case_22_12_6, case_22_12_6_checked⟩

    · exact ⟨Witness.linear .conditional case_22_12_7, case_22_12_7_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_22_13_1_checked⟩

    · exact ⟨Witness.rising, case_22_13_2_checked⟩

    · exact ⟨Witness.rising, case_22_13_3_checked⟩

    · exact ⟨Witness.rising, case_22_13_4_checked⟩

    · exact ⟨Witness.rising, case_22_13_5_checked⟩

    · exact ⟨Witness.linear .positive case_22_13_6, case_22_13_6_checked⟩

    · exact ⟨Witness.linear .conditional case_22_13_7, case_22_13_7_checked⟩

    · exact ⟨Witness.linear .negative case_22_13_8, case_22_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_22_14_1_checked⟩

    · exact ⟨Witness.rising, case_22_14_2_checked⟩

    · exact ⟨Witness.rising, case_22_14_3_checked⟩

    · exact ⟨Witness.rising, case_22_14_4_checked⟩

    · exact ⟨Witness.rising, case_22_14_5_checked⟩

    · exact ⟨Witness.linear .positive case_22_14_6, case_22_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_22_14_7, case_22_14_7_checked⟩

    · exact ⟨Witness.linear .conditional case_22_14_8, case_22_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_22_15_1_checked⟩

    · exact ⟨Witness.rising, case_22_15_2_checked⟩

    · exact ⟨Witness.rising, case_22_15_3_checked⟩

    · exact ⟨Witness.rising, case_22_15_4_checked⟩

    · exact ⟨Witness.rising, case_22_15_5_checked⟩

    · exact ⟨Witness.linear .positive case_22_15_6, case_22_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_22_15_7, case_22_15_7_checked⟩

    · exact ⟨Witness.linear .conditional case_22_15_8, case_22_15_8_checked⟩

    · exact ⟨Witness.linear .negative case_22_15_9, case_22_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_22_16_1_checked⟩

    · exact ⟨Witness.rising, case_22_16_2_checked⟩

    · exact ⟨Witness.rising, case_22_16_3_checked⟩

    · exact ⟨Witness.rising, case_22_16_4_checked⟩

    · exact ⟨Witness.rising, case_22_16_5_checked⟩

    · exact ⟨Witness.linear .positive case_22_16_6, case_22_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_22_16_7, case_22_16_7_checked⟩

    · exact ⟨Witness.linear .conditional case_22_16_8, case_22_16_8_checked⟩

    · exact ⟨Witness.linear .negative case_22_16_9, case_22_16_9_checked⟩

    · exact ⟨Witness.linear .negative case_22_16_10, case_22_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_22_17_1_checked⟩

    · exact ⟨Witness.rising, case_22_17_2_checked⟩

    · exact ⟨Witness.rising, case_22_17_3_checked⟩

    · exact ⟨Witness.rising, case_22_17_4_checked⟩

    · exact ⟨Witness.rising, case_22_17_5_checked⟩

    · exact ⟨Witness.linear .positive case_22_17_6, case_22_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_22_17_7, case_22_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_22_17_8, case_22_17_8_checked⟩

    · exact ⟨Witness.linear .conditional case_22_17_9, case_22_17_9_checked⟩

    · exact ⟨Witness.linear .negative case_22_17_10, case_22_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_22_18_1_checked⟩

    · exact ⟨Witness.rising, case_22_18_2_checked⟩

    · exact ⟨Witness.rising, case_22_18_3_checked⟩

    · exact ⟨Witness.rising, case_22_18_4_checked⟩

    · exact ⟨Witness.rising, case_22_18_5_checked⟩

    · exact ⟨Witness.linear .positive case_22_18_6, case_22_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_22_18_7, case_22_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_22_18_8, case_22_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_22_18_9, case_22_18_9_checked⟩

    · exact ⟨Witness.linear .negative case_22_18_10, case_22_18_10_checked⟩

    · exact ⟨Witness.linear .negative case_22_18_11, case_22_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_22_19_1_checked⟩

    · exact ⟨Witness.rising, case_22_19_2_checked⟩

    · exact ⟨Witness.rising, case_22_19_3_checked⟩

    · exact ⟨Witness.rising, case_22_19_4_checked⟩

    · exact ⟨Witness.rising, case_22_19_5_checked⟩

    · exact ⟨Witness.linear .positive case_22_19_6, case_22_19_6_checked⟩

    · exact ⟨Witness.linear .positive case_22_19_7, case_22_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_22_19_8, case_22_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_22_19_9, case_22_19_9_checked⟩

    · exact ⟨Witness.linear .negative case_22_19_10, case_22_19_10_checked⟩

    · exact ⟨Witness.linear .negative case_22_19_11, case_22_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_22_19_12, case_22_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_22_20_1_checked⟩

    · exact ⟨Witness.rising, case_22_20_2_checked⟩

    · exact ⟨Witness.rising, case_22_20_3_checked⟩

    · exact ⟨Witness.rising, case_22_20_4_checked⟩

    · exact ⟨Witness.rising, case_22_20_5_checked⟩

    · exact ⟨Witness.linear .positive case_22_20_6, case_22_20_6_checked⟩

    · exact ⟨Witness.linear .positive case_22_20_7, case_22_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_22_20_8, case_22_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_22_20_9, case_22_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_22_20_10, case_22_20_10_checked⟩

    · exact ⟨Witness.linear .negative case_22_20_11, case_22_20_11_checked⟩

    · exact ⟨Witness.linear .negative case_22_20_12, case_22_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_22_21_1_checked⟩

    · exact ⟨Witness.rising, case_22_21_2_checked⟩

    · exact ⟨Witness.rising, case_22_21_3_checked⟩

    · exact ⟨Witness.rising, case_22_21_4_checked⟩

    · exact ⟨Witness.rising, case_22_21_5_checked⟩

    · exact ⟨Witness.linear .positive case_22_21_6, case_22_21_6_checked⟩

    · exact ⟨Witness.linear .positive case_22_21_7, case_22_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_22_21_8, case_22_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_22_21_9, case_22_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_22_21_10, case_22_21_10_checked⟩

    · exact ⟨Witness.linear .negative case_22_21_11, case_22_21_11_checked⟩

    · exact ⟨Witness.linear .negative case_22_21_12, case_22_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_22_21_13, case_22_21_13_checked⟩


#print axioms coverage_22
end ForestUnimodality.FiniteRows.FiniteData
