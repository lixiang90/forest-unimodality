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

theorem case_34_17_1_checked :
    (Witness.rising).check 34 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_17_2_checked :
    (Witness.rising).check 34 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_17_3_checked :
    (Witness.rising).check 34 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_17_4_checked :
    (Witness.rising).check 34 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_17_5_checked :
    (Witness.rising).check 34 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_17_6_checked :
    (Witness.rising).check 34 17 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_17_7_checked :
    (Witness.rising).check 34 17 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_17_8 : Certificate := {
  objectiveScale := 8388989280000
  eta := 50384269615680
  rows := #[⟨.count 2, 1801237638760560⟩, ⟨.count 3, 634841797157568⟩, ⟨.count 4, 116963483036400⟩, ⟨.count 5, 28514174562720⟩, ⟨.count 6, 10450583395560⟩, ⟨.count 7, 8368016806800⟩, ⟨.path 8, 2041309069632⟩, ⟨.path 9, 1633364072928⟩, ⟨.privateRow 9 0, 181388590432⟩, ⟨.hall 1 1, 1679475653856⟩, ⟨.hall 7 1, 231955553592⟩, ⟨.hall 0 2, 26031872634768⟩, ⟨.hall 7 2, 22021096860⟩, ⟨.hall 1 3, 1806359116716⟩, ⟨.hall 6 3, 41787652851⟩, ⟨.hall 0 4, 15641270512560⟩, ⟨.hall 6 4, 2546657460⟩, ⟨.hall 5 6, 18500717430⟩, ⟨.hall 5 7, 6047063106⟩, ⟨.hall 1 9, 43413019524⟩, ⟨.hall 4 9, 57884026032⟩, ⟨.hall 3 13, 2879101120896⟩, ⟨.hall 0 14, 8397378269280⟩]
  caps := #[0, 0, 2720134216800, 0, 0, 65736498240, 0, 20972473200, 2196516672, 866759040, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_34_17_8_checked :
    (Witness.linear .positive case_34_17_8).check 34 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_17_9 : Certificate := {
  objectiveScale := 4032000
  eta := 0
  rows := #[⟨.count 2, 1619457840⟩, ⟨.count 3, 554954400⟩, ⟨.count 4, 111855744⟩, ⟨.count 5, 28163520⟩, ⟨.count 6, 9369360⟩, ⟨.count 7, 4021920⟩, ⟨.count 8, 4036032⟩, ⟨.path 10, 1331540⟩, ⟨.privateRow 4 13, 1513512⟩, ⟨.privateRow 8 2, 54243⟩, ⟨.privateRow 10 0, 166257⟩, ⟨.privateRow 11 0, 213840⟩, ⟨.hall 8 1, 183848⟩, ⟨.hall 8 2, 16016⟩, ⟨.hall 0 3, 144144⟩, ⟨.hall 7 3, 38430⟩, ⟨.hall 0 4, 2483712⟩, ⟨.hall 1 4, 232848⟩, ⟨.hall 6 5, 28540⟩, ⟨.hall 0 6, 1789200⟩, ⟨.hall 5 8, 67760⟩, ⟨.hall 6 8, 2912⟩, ⟨.hall 1 10, 90720⟩, ⟨.hall 4 10, 156912⟩]
  caps := #[0, 110880, 2702700, 240240, 0, 0, 26180, 10080, 0, 0, 5453, 0, 0, 0, 0, 0, 0, 0] }

theorem case_34_17_9_checked :
    (Witness.linear .positive case_34_17_9).check 34 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_17_10 : Certificate := {
  objectiveScale := 9800000
  eta := 0
  rows := #[⟨.count 2, 4603599000⟩, ⟨.count 3, 1674953280⟩, ⟨.count 4, 440359920⟩, ⟨.count 5, 143312400⟩, ⟨.count 6, 52806600⟩, ⟨.count 7, 23725800⟩, ⟨.count 8, 15170400⟩, ⟨.count 9, 15170400⟩, ⟨.path 10, 3266550⟩, ⟨.privateRow 11 0, 1400400⟩, ⟨.hall 9 1, 1547280⟩, ⟨.hall 0 2, 22702680⟩, ⟨.hall 8 2, 377160⟩, ⟨.hall 1 3, 2605680⟩, ⟨.hall 8 3, 195160⟩, ⟨.hall 0 4, 23063040⟩, ⟨.hall 7 4, 321020⟩, ⟨.hall 9 4, 20664⟩, ⟨.hall 6 6, 381540⟩, ⟨.hall 7 7, 116865⟩, ⟨.hall 5 8, 707980⟩, ⟨.hall 4 11, 10676820⟩, ⟨.hall 3 13, 83423340⟩, ⟨.hall 1 15, 18918900⟩, ⟨.assumptionRow 10, 15146040⟩]
  caps := #[0, 0, 0, 1921920, 0, 212520, 115500, 32830, 42000, 0, 910, 0, 0, 0, 0, 0, 0, 0] }

theorem case_34_17_10_checked :
    (Witness.linear .conditional case_34_17_10).check 34 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_18_1_checked :
    (Witness.rising).check 34 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_18_2_checked :
    (Witness.rising).check 34 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_18_3_checked :
    (Witness.rising).check 34 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_18_4_checked :
    (Witness.rising).check 34 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_18_5_checked :
    (Witness.rising).check 34 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_18_6_checked :
    (Witness.rising).check 34 18 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_18_7_checked :
    (Witness.rising).check 34 18 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_18_8 : Certificate := {
  objectiveScale := 1473199200000
  eta := 3736116038655000
  rows := #[⟨.count 2, 836889992658720⟩, ⟨.count 3, 121995625752000⟩, ⟨.count 4, 22146898213440⟩, ⟨.count 5, 5356859207700⟩, ⟨.count 6, 1876855780800⟩, ⟨.count 7, 1478023927380⟩, ⟨.path 8, 404870065600⟩, ⟨.path 9, 258466103280⟩, ⟨.privateRow 5 8, 40404534170⟩, ⟨.privateRow 6 5, 64872382575⟩, ⟨.privateRow 6 6, 127459632300⟩, ⟨.privateRow 6 7, 101899998200⟩, ⟨.privateRow 7 2, 40523022540⟩, ⟨.privateRow 7 3, 74647673100⟩, ⟨.privateRow 8 0, 44185390340⟩, ⟨.privateRow 9 0, 25877860008⟩, ⟨.hall 4 10, 10429580700⟩, ⟨.hall 5 10, 1048166350⟩, ⟨.hall 5 12, 306793733400⟩, ⟨.hall 3 14, 1707938760528⟩]
  caps := #[0, 2643225470600, 0, 0, 43947075480, 0, 4692238375, 0, 7544081500, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_34_18_8_checked :
    (Witness.linear .positive case_34_18_8).check 34 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_18_9 : Certificate := {
  objectiveScale := 126000000
  eta := 377772595200
  rows := #[⟨.count 2, 89524234800⟩, ⟨.count 3, 15852957120⟩, ⟨.count 4, 3489726240⟩, ⟨.count 5, 891891000⟩, ⟨.count 6, 297788400⟩, ⟨.count 7, 127960560⟩, ⟨.count 8, 126584640⟩, ⟨.path 9, 1710720⟩, ⟨.path 10, 39034800⟩, ⟨.privateRow 6 6, 772200⟩, ⟨.privateRow 6 7, 28583100⟩, ⟨.privateRow 7 4, 8697780⟩, ⟨.privateRow 7 5, 16763760⟩, ⟨.privateRow 7 6, 22113000⟩, ⟨.privateRow 8 2, 11211200⟩, ⟨.privateRow 8 3, 4787055⟩, ⟨.privateRow 9 0, 6099912⟩, ⟨.privateRow 10 0, 4324320⟩, ⟨.hall 5 7, 332850⟩, ⟨.hall 5 8, 330120⟩, ⟨.hall 4 10, 2799360⟩, ⟨.hall 6 11, 23095800⟩, ⟨.hall 3 14, 559350792⟩]
  caps := #[0, 138996000, 0, 36396360, 4747680, 9266400, 89280, 2176920, 0, 0, 115920, 0, 0, 0, 0, 0, 0] }

theorem case_34_18_9_checked :
    (Witness.linear .positive case_34_18_9).check 34 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_18_10 : Certificate := {
  objectiveScale := 364000000
  eta := 1866727863000
  rows := #[⟨.count 2, 441521720640⟩, ⟨.count 3, 100486386000⟩, ⟨.count 4, 27351324000⟩, ⟨.count 5, 7749541800⟩, ⟨.count 6, 2702700000⟩, ⟨.count 7, 1150269120⟩, ⟨.count 8, 686125440⟩, ⟨.count 9, 650810160⟩, ⟨.path 10, 149564800⟩, ⟨.privateRow 3 15, 1030629600⟩, ⟨.privateRow 6 8, 27387360⟩, ⟨.privateRow 7 5, 32432400⟩, ⟨.privateRow 7 6, 187387200⟩, ⟨.privateRow 7 7, 84540456⟩, ⟨.privateRow 8 3, 34684650⟩, ⟨.privateRow 8 4, 119879760⟩, ⟨.privateRow 8 5, 205164960⟩, ⟨.privateRow 9 1, 31111080⟩, ⟨.privateRow 9 2, 92597505⟩, ⟨.privateRow 9 3, 2282280⟩, ⟨.privateRow 10 0, 51891840⟩, ⟨.privateRow 11 0, 45495450⟩, ⟨.hall 6 7, 9107280⟩, ⟨.hall 5 9, 33901560⟩, ⟨.hall 7 10, 185061240⟩, ⟨.hall 4 11, 124973640⟩, ⟨.hall 3 14, 7709109408⟩, ⟨.assumptionRow 10, 682916850⟩]
  caps := #[0, 0, 714974260, 10810800, 0, 0, 9075990, 1593620, 0, 6249600, 0, 36400, 0, 0, 0, 0, 0] }

theorem case_34_18_10_checked :
    (Witness.linear .conditional case_34_18_10).check 34 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_18_11 : Certificate := {
  objectiveScale := 286650000
  eta := 446391445500
  rows := #[⟨.count 2, 128416448160⟩, ⟨.count 3, 38725907220⟩, ⟨.count 4, 12462690240⟩, ⟨.count 5, 4330626300⟩, ⟨.count 6, 1654052400⟩, ⟨.count 7, 703783080⟩, ⟨.count 8, 346426080⟩, ⟨.count 9, 249729480⟩, ⟨.count 10, 210810600⟩, ⟨.count 12, 285405120⟩, ⟨.path 9, 59732640⟩, ⟨.privateRow 7 6, 63333270⟩, ⟨.privateRow 7 7, 208216008⟩, ⟨.privateRow 8 4, 22342320⟩, ⟨.privateRow 8 5, 145955810⟩, ⟨.privateRow 8 6, 225765540⟩, ⟨.privateRow 9 1, 2102100⟩, ⟨.privateRow 9 3, 81621540⟩, ⟨.privateRow 9 4, 156746590⟩, ⟨.privateRow 10 1, 43378335⟩, ⟨.privateRow 10 2, 31196880⟩, ⟨.privateRow 11 0, 19369350⟩, ⟨.hall 6 8, 10791690⟩, ⟨.hall 5 9, 37110150⟩, ⟨.hall 6 9, 40106430⟩, ⟨.hall 7 9, 87439716⟩, ⟨.hall 7 10, 126928620⟩, ⟨.hall 4 11, 139457340⟩, ⟨.hall 3 13, 827448336⟩, ⟨.hall 2 15, 8026028010⟩, ⟨.assumptionRow 11, 210064400⟩]
  caps := #[0, 0, 0, 27428940, 0, 7250100, 0, 0, 733130, 2317100, 0, 0, 1244880, 0, 0, 0, 0] }

theorem case_34_18_11_checked :
    (Witness.linear .conditional case_34_18_11).check 34 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_19_1_checked :
    (Witness.rising).check 34 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_19_2_checked :
    (Witness.rising).check 34 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_19_3_checked :
    (Witness.rising).check 34 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_19_4_checked :
    (Witness.rising).check 34 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_19_5_checked :
    (Witness.rising).check 34 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_19_6_checked :
    (Witness.rising).check 34 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_19_7_checked :
    (Witness.rising).check 34 19 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_19_8 : Certificate := {
  objectiveScale := 3193644960000
  eta := 8489350226316960
  rows := #[⟨.count 2, 1416780745380000⟩, ⟨.count 3, 221453728816320⟩, ⟨.count 4, 43883875395360⟩, ⟨.count 5, 10964363810400⟩, ⟨.count 6, 3963023064000⟩, ⟨.count 7, 3205645322880⟩, ⟨.path 8, 800799199200⟩, ⟨.path 9, 579307840320⟩, ⟨.privateRow 4 12, 1925368705260⟩, ⟨.privateRow 4 13, 532806434160⟩, ⟨.privateRow 5 8, 366107844960⟩, ⟨.privateRow 5 9, 462352690800⟩, ⟨.privateRow 5 10, 1680321779136⟩, ⟨.privateRow 5 11, 528403075200⟩, ⟨.privateRow 6 5, 217232375360⟩, ⟨.privateRow 6 6, 407861123670⟩, ⟨.privateRow 6 7, 375543614160⟩, ⟨.privateRow 7 2, 112886111520⟩, ⟨.privateRow 7 3, 159401594352⟩, ⟨.privateRow 8 0, 90544068615⟩, ⟨.privateRow 9 0, 52840307520⟩, ⟨.hall 9 2, 15558534992⟩, ⟨.hall 3 14, 457729163892⟩]
  caps := #[0, 0, 0, 0, 0, 0, 38774502910, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_34_19_8_checked :
    (Witness.linear .positive case_34_19_8).check 34 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_19_9 : Certificate := {
  objectiveScale := 72600000
  eta := 287854847280
  rows := #[⟨.count 2, 55963187280⟩, ⟨.count 3, 10131881760⟩, ⟨.count 4, 2152430280⟩, ⟨.count 5, 551350800⟩, ⟨.count 6, 178378200⟩, ⟨.count 7, 75675600⟩, ⟨.count 8, 73153080⟩, ⟨.path 9, 3199680⟩, ⟨.path 10, 20861280⟩, ⟨.privateRow 5 9, 1621620⟩, ⟨.privateRow 5 10, 53405352⟩, ⟨.privateRow 5 11, 61891830⟩, ⟨.privateRow 6 7, 17760600⟩, ⟨.privateRow 6 8, 27567540⟩, ⟨.privateRow 6 9, 35459424⟩, ⟨.privateRow 6 10, 14729715⟩, ⟨.privateRow 7 4, 4724720⟩, ⟨.privateRow 7 5, 12837825⟩, ⟨.privateRow 7 6, 13024440⟩, ⟨.privateRow 8 2, 7441434⟩, ⟨.privateRow 8 3, 980980⟩, ⟨.privateRow 9 0, 2915640⟩, ⟨.privateRow 10 0, 2108106⟩, ⟨.hall 10 2, 930930⟩, ⟨.hall 4 13, 18234216⟩, ⟨.hall 3 14, 42216174⟩]
  caps := #[0, 23783760, 0, 12080640, 11891880, 0, 1224795, 142032, 929698, 375600, 0, 0, 0, 0, 0, 0] }

theorem case_34_19_9_checked :
    (Witness.linear .positive case_34_19_9).check 34 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_19_10 : Certificate := {
  objectiveScale := 2700000000
  eta := 14585908116780
  rows := #[⟨.count 2, 3431996568000⟩, ⟨.count 3, 900899099100⟩, ⟨.count 4, 237599762400⟩, ⟨.count 5, 62999937000⟩, ⟨.count 6, 19799980200⟩, ⟨.count 7, 6900353460⟩, ⟨.count 8, 3000537540⟩, ⟨.count 9, 2699997300⟩, ⟨.path 10, 299999700⟩, ⟨.path 11, 299999700⟩, ⟨.privateRow 10 1, 1051050⟩, ⟨.privateRow 11 0, 33333300⟩, ⟨.hall 9 4, 2285712⟩, ⟨.hall 8 5, 89827010⟩, ⟨.hall 7 6, 52272675⟩, ⟨.hall 6 9, 52987284⟩]
  caps := #[0, 64169820, 0, 0, 0, 37800, 13500, 0, 61380, 2700, 447750, 0, 0, 0, 0, 0] }

theorem case_34_19_10_checked :
    (Witness.linear .positive case_34_19_10).check 34 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_19_11 : Certificate := {
  objectiveScale := 188451446400000
  eta := 814660262839463040
  rows := #[⟨.count 2, 203472383528494080⟩, ⟨.count 3, 51223816832348160⟩, ⟨.count 4, 14940279909434880⟩, ⟨.count 5, 4608203218819200⟩, ⟨.count 6, 1536067739606400⟩, ⟨.count 7, 565919693539200⟩, ⟨.count 8, 226367877415680⟩, ⟨.count 9, 145522206910080⟩, ⟨.count 10, 161691341011200⟩, ⟨.count 12, 177860475112320⟩, ⟨.path 8, 71209528790400⟩, ⟨.privateRow 2 17, 2504868357831840⟩, ⟨.privateRow 4 13, 2494987220325600⟩, ⟨.privateRow 5 10, 165464138968128⟩, ⟨.privateRow 5 11, 1027413729342000⟩, ⟨.privateRow 5 12, 2207985090030720⟩, ⟨.privateRow 6 8, 125086217976720⟩, ⟨.privateRow 6 9, 476450484846336⟩, ⟨.privateRow 6 10, 1006191740834280⟩, ⟨.privateRow 6 11, 1212235914970080⟩, ⟨.privateRow 7 6, 67628045010240⟩, ⟨.privateRow 7 7, 239542727424000⟩, ⟨.privateRow 7 8, 500883843043584⟩, ⟨.privateRow 7 9, 634413942162000⟩, ⟨.privateRow 7 10, 47309688666240⟩, ⟨.privateRow 8 4, 30948733240425⟩, ⟨.privateRow 8 5, 128679358888080⟩, ⟨.privateRow 8 6, 277850849536260⟩, ⟨.privateRow 8 7, 127960730705808⟩, ⟨.privateRow 9 2, 8883042808640⟩, ⟨.privateRow 9 3, 75905101752480⟩, ⟨.privateRow 9 4, 105997656885120⟩, ⟨.privateRow 10 1, 43267405140960⟩, ⟨.privateRow 10 2, 10610994253860⟩, ⟨.privateRow 11 0, 13174850008320⟩, ⟨.hall 5 13, 1378226192428800⟩, ⟨.hall 4 14, 5612486103544320⟩, ⟨.hall 3 15, 11677651819093260⟩, ⟨.hall 2 16, 14167807453800000⟩, ⟨.assumptionRow 11, 156966594033600⟩]
  caps := #[0, 771957249635520, 113741842705920, 30153779884800, 6856119573120, 11570097265056, 2517306552000, 10966276072224, 1808245408320, 4013317840000, 5592801452580, 0, 10590971287680, 0, 0, 0] }

theorem case_34_19_11_checked :
    (Witness.linear .conditional case_34_19_11).check 34 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_19_12 : Certificate := {
  objectiveScale := 156012484320000
  eta := 2535707882611743840
  rows := #[⟨.count 2, 369204636230670240⟩, ⟨.count 3, 50063158118413440⟩, ⟨.count 4, 5153560394542560⟩, ⟨.count 9, 182534606654400⟩, ⟨.count 10, 2078866353564000⟩, ⟨.count 11, 3123369936086400⟩, ⟨.count 12, 937010980825920⟩, ⟨.count 13, 290027208350880⟩, ⟨.path 4, 5148143262662400⟩, ⟨.privateRow 2 17, 28857707230912560⟩, ⟨.privateRow 3 14, 6469837724750400⟩, ⟨.privateRow 4 10, 26028082800720⟩, ⟨.privateRow 4 11, 974937615764112⟩, ⟨.privateRow 4 12, 2684146038824250⟩, ⟨.privateRow 4 13, 4400605142093160⟩, ⟨.privateRow 5 7, 14197136073120⟩, ⟨.privateRow 5 8, 92136515739840⟩, ⟨.privateRow 5 9, 461068895327040⟩, ⟨.privateRow 5 10, 1013269883161536⟩, ⟨.privateRow 5 11, 1764501197659200⟩, ⟨.privateRow 5 12, 3071989824583680⟩, ⟨.privateRow 6 5, 5633784156000⟩, ⟨.privateRow 6 6, 43225208936910⟩, ⟨.privateRow 6 7, 179347494474720⟩, ⟨.privateRow 6 8, 411885959645160⟩, ⟨.privateRow 6 9, 740887686787248⟩, ⟨.privateRow 6 10, 1361150421010380⟩, ⟨.privateRow 6 11, 1576896185264400⟩, ⟨.privateRow 7 4, 20056271595360⟩, ⟨.privateRow 7 5, 64309646140740⟩, ⟨.privateRow 7 6, 174904853254560⟩, ⟨.privateRow 7 7, 339153806191200⟩, ⟨.privateRow 7 8, 654285156741216⟩, ⟨.privateRow 7 9, 847602826270200⟩, ⟨.privateRow 7 10, 44619570515520⟩, ⟨.privateRow 8 2, 7512651172026⟩, ⟨.privateRow 8 3, 23596165973380⟩, ⟨.privateRow 8 4, 73499756545215⟩, ⟨.privateRow 8 5, 167830430007240⟩, ⟨.privateRow 8 6, 351872073923370⟩, ⟨.privateRow 8 7, 212365493760420⟩, ⟨.privateRow 9 0, 3257351566560⟩, ⟨.privateRow 9 1, 8112649184640⟩, ⟨.privateRow 9 2, 33276885081440⟩, ⟨.privateRow 9 3, 82394093281500⟩, ⟨.privateRow 9 4, 159452188140960⟩, ⟨.privateRow 10 0, 59425155277488⟩, ⟨.hall 5 13, 1720316233350000⟩, ⟨.hall 4 14, 7705799828030304⟩, ⟨.hall 3 15, 18602177820236010⟩, ⟨.hall 2 16, 32278322247050880⟩]
  caps := #[0, 459378870350400, 0, 14376093732000, 0, 0, 4766583809130, 590990148936, 5851804380037, 0, 2043763544592, 0, 0, 0, 0, 0] }

theorem case_34_19_12_checked :
    (Witness.linear .negative case_34_19_12).check 34 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_20_1_checked :
    (Witness.rising).check 34 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_20_2_checked :
    (Witness.rising).check 34 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_20_3_checked :
    (Witness.rising).check 34 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_20_4_checked :
    (Witness.rising).check 34 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_20_5_checked :
    (Witness.rising).check 34 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_20_6_checked :
    (Witness.rising).check 34 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_20_7_checked :
    (Witness.rising).check 34 20 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_34_20_8_checked :
    (Witness.linear .positive case_34_20_8).check 34 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_20_9 : Certificate := {
  objectiveScale := 10098000000
  eta := 63652714725600
  rows := #[⟨.count 2, 13472073014400⟩, ⟨.count 3, 2886872788800⟩, ⟨.count 4, 635523688800⟩, ⟨.count 5, 153091738800⟩, ⟨.count 6, 42025183200⟩, ⟨.count 7, 14258544300⟩, ⟨.count 8, 10291881600⟩, ⟨.path 9, 4207324275⟩, ⟨.privateRow 6 14, 677262986400⟩, ⟨.privateRow 7 12, 4449094650⟩, ⟨.privateRow 9 9, 1238837600⟩, ⟨.privateRow 10 0, 23390640⟩, ⟨.hall 7 3, 188924400⟩, ⟨.hall 9 3, 17153136⟩, ⟨.hall 10 3, 53603550⟩, ⟨.hall 9 7, 10720710⟩, ⟨.hall 4 12, 1097046720⟩]
  caps := #[0, 0, 3380691600, 853667100, 606028500, 311486175, 48059550, 178244550, 0, 193489635, 0, 0, 0, 0, 0] }

theorem case_34_20_9_checked :
    (Witness.linear .positive case_34_20_9).check 34 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_20_10 : Certificate := {
  objectiveScale := 3366000
  eta := 25755433704
  rows := #[⟨.count 2, 6186155976⟩, ⟨.count 3, 1650989340⟩, ⟨.count 4, 444756312⟩, ⟨.count 5, 121297176⟩, ⟨.count 6, 35939904⟩, ⟨.count 7, 12507495⟩, ⟨.count 8, 5309304⟩, ⟨.count 9, 4288284⟩, ⟨.path 9, 961587⟩, ⟨.hall 6 7, 76177⟩]
  caps := #[0, 0, 1656369, 0, 0, 0, 121836, 0, 0, 39303, 0, 0, 0, 0, 0] }

theorem case_34_20_10_checked :
    (Witness.linear .positive case_34_20_10).check 34 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_20_11 : Certificate := {
  objectiveScale := 2448000000
  eta := 19395418442400
  rows := #[⟨.count 2, 4318179465600⟩, ⟨.count 3, 1113912399600⟩, ⟨.count 4, 292583491200⟩, ⟨.count 5, 82702620000⟩, ⟨.count 6, 26464838400⟩, ⟨.count 7, 9219810600⟩, ⟨.count 8, 3430627200⟩, ⟨.count 9, 2205403200⟩, ⟨.count 10, 1470268800⟩, ⟨.path 8, 1165665600⟩, ⟨.privateRow 2 18, 133426893600⟩, ⟨.privateRow 4 13, 19710791100⟩, ⟨.privateRow 4 14, 61935073200⟩, ⟨.privateRow 5 11, 15055552512⟩, ⟨.privateRow 5 12, 28743755040⟩, ⟨.privateRow 5 13, 48812924160⟩, ⟨.privateRow 6 8, 309223200⟩, ⟨.privateRow 6 9, 8120512400⟩, ⟨.privateRow 6 10, 14890555680⟩, ⟨.privateRow 6 11, 23708084400⟩, ⟨.privateRow 6 12, 16649432800⟩, ⟨.privateRow 7 6, 478603125⟩, ⟨.privateRow 7 7, 3995105400⟩, ⟨.privateRow 7 8, 8055847800⟩, ⟨.privateRow 7 9, 12466654200⟩, ⟨.privateRow 8 4, 343743400⟩, ⟨.privateRow 8 5, 2220718500⟩, ⟨.privateRow 8 6, 4542080400⟩, ⟨.privateRow 8 7, 2072670600⟩, ⟨.privateRow 9 2, 126606480⟩, ⟨.privateRow 9 3, 1456655200⟩, ⟨.privateRow 9 4, 1317115800⟩, ⟨.privateRow 10 1, 764539776⟩, ⟨.privateRow 11 0, 165405240⟩, ⟨.hall 4 15, 66437771400⟩, ⟨.hall 3 16, 207275468400⟩, ⟨.hall 2 17, 345023078400⟩, ⟨.assumptionRow 11, 2364951600⟩]
  caps := #[0, 0, 0, 864606600, 383326020, 0, 108279600, 104900250, 99990000, 230743040, 130143024, 678524400, 2448000000, 0, 0] }

theorem case_34_20_11_checked :
    (Witness.linear .conditional case_34_20_11).check 34 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_20_12 : Certificate := {
  objectiveScale := 11502275400000
  eta := 89567979292471680
  rows := #[⟨.count 2, 20647164057680160⟩, ⟨.count 3, 4898947918344480⟩, ⟨.count 4, 1153052498838240⟩, ⟨.count 5, 293855531009040⟩, ⟨.count 6, 71853947605440⟩, ⟨.count 7, 14828350036500⟩, ⟨.count 8, 4067204581440⟩, ⟨.count 9, 5084005726800⟩, ⟨.count 11, 5592406299480⟩, ⟨.path 7, 10140282184032⟩, ⟨.privateRow 2 18, 2192223269396160⟩, ⟨.privateRow 3 15, 227424522845520⟩, ⟨.privateRow 4 13, 179084101726530⟩, ⟨.privateRow 4 14, 397399780978200⟩, ⟨.privateRow 5 11, 92325543998688⟩, ⟨.privateRow 5 12, 176465838777228⟩, ⟨.privateRow 5 13, 318462118726752⟩, ⟨.privateRow 6 8, 2501653611600⟩, ⟨.privateRow 6 9, 37885257490080⟩, ⟨.privateRow 6 10, 83332502757504⟩, ⟨.privateRow 6 11, 152068260183840⟩, ⟨.privateRow 6 12, 171274504040640⟩, ⟨.privateRow 7 6, 1461651646455⟩, ⟨.privateRow 7 7, 15796732079700⟩, ⟨.privateRow 7 8, 39076232905710⟩, ⟨.privateRow 7 9, 80106983568612⟩, ⟨.privateRow 7 10, 68273960239485⟩, ⟨.privateRow 8 4, 122392730460⟩, ⟨.privateRow 8 5, 6736307588010⟩, ⟨.privateRow 8 6, 19500793394940⟩, ⟨.privateRow 8 7, 44936961729660⟩, ⟨.privateRow 8 8, 11693213171640⟩, ⟨.privateRow 9 3, 1682115475040⟩, ⟨.privateRow 9 4, 10563434121240⟩, ⟨.privateRow 9 5, 19222383557520⟩, ⟨.privateRow 10 0, 221847522624⟩, ⟨.privateRow 10 2, 3863844352368⟩, ⟨.privateRow 10 3, 6863407731180⟩, ⟨.privateRow 11 1, 3276359246160⟩, ⟨.privateRow 12 0, 828504636960⟩, ⟨.hall 5 14, 43586875764432⟩, ⟨.hall 4 15, 550724920355610⟩, ⟨.hall 3 16, 1439551174501440⟩, ⟨.hall 2 17, 2393549896177440⟩, ⟨.assumptionRow 12, 4515504520320⟩]
  caps := #[0, 111146922529344, 3611854056096, 4502551173120, 0, 747700341102, 62992700352, 0, 231884267610, 611547785200, 78554067840, 0, 0, 11502275400000, 0] }

theorem case_34_20_12_checked :
    (Witness.linear .conditional case_34_20_12).check 34 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_21_1_checked :
    (Witness.rising).check 34 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_21_2_checked :
    (Witness.rising).check 34 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_21_3_checked :
    (Witness.rising).check 34 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_21_4_checked :
    (Witness.rising).check 34 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_21_5_checked :
    (Witness.rising).check 34 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_21_6_checked :
    (Witness.rising).check 34 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_21_7_checked :
    (Witness.rising).check 34 21 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_34_21_8_checked :
    (Witness.linear .positive case_34_21_8).check 34 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_34_21_9_checked :
    (Witness.linear .positive case_34_21_9).check 34 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_21_10 : Certificate := {
  objectiveScale := 533880000
  eta := 9775498692960
  rows := #[⟨.count 2, 2234918846160⟩, ⟨.count 3, 486462380040⟩, ⟨.count 4, 117940285008⟩, ⟨.count 5, 27713948080⟩, ⟨.count 6, 7433211240⟩, ⟨.count 7, 2064780900⟩, ⟨.count 8, 734144320⟩, ⟨.count 9, 660729888⟩, ⟨.path 7, 371872501⟩, ⟨.path 8, 171583100⟩]
  caps := #[0, 0, 9303008, 256839661, 41100657, 86442356, 41170266, 61184001, 0, 0, 0, 0, 0, 0] }

theorem case_34_21_10_checked :
    (Witness.linear .positive case_34_21_10).check 34 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_21_11 : Certificate := {
  objectiveScale := 70414323000000
  eta := 997653055167568800
  rows := #[⟨.count 2, 210934638762447600⟩, ⟨.count 3, 47631571633245600⟩, ⟨.count 4, 11005285500649440⟩, ⟨.count 5, 2827444891471200⟩, ⟨.count 6, 761235163088400⟩, ⟨.count 7, 217495760882400⟩, ⟨.count 8, 72498586960800⟩, ⟨.path 7, 80335490295060⟩, ⟨.privateRow 2 19, 21731451441499800⟩, ⟨.privateRow 3 16, 5111150380736400⟩, ⟨.privateRow 3 17, 8264838913531200⟩, ⟨.privateRow 4 13, 724260883738392⟩, ⟨.privateRow 4 14, 2936192771912400⟩, ⟨.privateRow 4 15, 3882299331750840⟩, ⟨.privateRow 4 16, 4795781527456920⟩, ⟨.privateRow 5 11, 702430753664640⟩, ⟨.privateRow 5 12, 1352340308775456⟩, ⟨.privateRow 5 13, 1860797065327200⟩, ⟨.privateRow 5 14, 2342509898688960⟩, ⟨.privateRow 5 15, 282744489147120⟩, ⟨.privateRow 6 8, 41535648779625⟩, ⟨.privateRow 6 9, 413414561359800⟩, ⟨.privateRow 6 10, 707868147686700⟩, ⟨.privateRow 6 11, 927377758206900⟩, ⟨.privateRow 6 12, 546760176662700⟩, ⟨.privateRow 7 6, 46030848864000⟩, ⟨.privateRow 7 7, 231089245937550⟩, ⟨.privateRow 7 8, 420565782522600⟩, ⟨.privateRow 7 9, 268848926646300⟩, ⟨.privateRow 8 4, 34436828806380⟩, ⟨.privateRow 8 5, 147346665165700⟩, ⟨.privateRow 8 6, 143486786693250⟩, ⟨.privateRow 9 2, 20651112649440⟩, ⟨.privateRow 9 3, 76365178265376⟩, ⟨.privateRow 10 1, 25704044467920⟩, ⟨.privateRow 11 0, 6590780632800⟩, ⟨.hall 3 17, 1891004809894200⟩, ⟨.hall 2 18, 7513143038200800⟩, ⟨.assumptionRow 11, 71141288754690⟩]
  caps := #[0, 0, 49590945484080, 255941806460340, 25834277589120, 5618461921800, 24988812954105, 5849272676730, 21759447900190, 9187950806370, 19733199818850, 0, 70414323000000, 0] }

theorem case_34_21_11_checked :
    (Witness.linear .conditional case_34_21_11).check 34 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_21_12 : Certificate := {
  objectiveScale := 6975482308200000
  eta := 143782770822144854400
  rows := #[⟨.count 2, 26992186830164556000⟩, ⟨.count 3, 5236843342881150000⟩, ⟨.count 4, 969564138910567200⟩, ⟨.count 5, 182208898533261600⟩, ⟨.count 6, 29924819102178000⟩, ⟨.count 7, 3989975880290400⟩, ⟨.count 8, 3989975880290400⟩, ⟨.path 5, 11980510351524000⟩, ⟨.path 6, 18196846976107800⟩, ⟨.privateRow 2 19, 2918667356432427600⟩, ⟨.privateRow 3 16, 643716108686851200⟩, ⟨.privateRow 3 17, 1070311029887899800⟩, ⟨.privateRow 4 13, 84507689144550672⟩, ⟨.privateRow 4 14, 338748952236654960⟩, ⟨.privateRow 4 15, 493959013979951520⟩, ⟨.privateRow 4 16, 674505422563092120⟩, ⟨.privateRow 5 11, 69469913382389520⟩, ⟨.privateRow 5 12, 147309909500321568⟩, ⟨.privateRow 5 13, 229224114322683480⟩, ⟨.privateRow 5 14, 336931296557856000⟩, ⟨.privateRow 5 15, 187129868785619760⟩, ⟨.privateRow 6 8, 2369048178922425⟩, ⟨.privateRow 6 9, 35387286081147000⟩, ⟨.privateRow 6 10, 72401437327769550⟩, ⟨.privateRow 6 11, 102542380123463280⟩, ⟨.privateRow 6 12, 192059151487728525⟩, ⟨.privateRow 7 6, 1298325484856400⟩, ⟨.privateRow 7 7, 17135521414461450⟩, ⟨.privateRow 7 8, 39451904367361200⟩, ⟨.privateRow 7 9, 62628371406701100⟩, ⟨.privateRow 7 10, 46312220039085000⟩, ⟨.privateRow 8 5, 8608003519515400⟩, ⟨.privateRow 8 6, 23815168535483325⟩, ⟨.privateRow 8 7, 30969812785111200⟩, ⟨.privateRow 9 3, 3378179578645872⟩, ⟨.privateRow 9 4, 16166791159398880⟩, ⟨.privateRow 9 5, 3025731709220220⟩, ⟨.privateRow 10 1, 761722668055440⟩, ⟨.privateRow 10 2, 6523610564274804⟩, ⟨.privateRow 11 0, 1994987940145200⟩, ⟨.hall 3 17, 341142937764829200⟩, ⟨.hall 2 18, 1060283590504538400⟩, ⟨.assumptionRow 12, 3657865417061100⟩]
  caps := #[0, 0, 3900838682520000, 2151878434391400, 68293379021868, 1895749620390912, 0, 748685950326600, 0, 0, 1609026753496596, 0, 52145993048538900, 6975482308200000] }

theorem case_34_21_12_checked :
    (Witness.linear .conditional case_34_21_12).check 34 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_21_13 : Certificate := {
  objectiveScale := 224071630246800000
  eta := 4439997503142391990800
  rows := #[⟨.count 2, 976679612702037644400⟩, ⟨.count 3, 205086377123434006200⟩, ⟨.count 4, 46845759449177488800⟩, ⟨.count 5, 10228596055440562800⟩, ⟨.count 6, 1997299821476559600⟩, ⟨.count 7, 317752244325816300⟩, ⟨.path 6, 126444008747756700⟩, ⟨.path 7, 301654450167095025⟩, ⟨.privateRow 2 19, 137314362726513472500⟩, ⟨.privateRow 3 16, 16613903060464109400⟩, ⟨.privateRow 4 14, 11806765535592117090⟩, ⟨.privateRow 4 15, 18983426939579482380⟩, ⟨.privateRow 5 11, 740413166143330680⟩, ⟨.privateRow 5 14, 20961560752668135600⟩, ⟨.privateRow 6 9, 585788151104055900⟩, ⟨.privateRow 6 11, 4398598925024514210⟩, ⟨.privateRow 6 13, 19191226819995730500⟩, ⟨.privateRow 7 7, 316131059405786625⟩, ⟨.privateRow 7 8, 699425494069945500⟩, ⟨.privateRow 7 9, 895974865803067050⟩, ⟨.privateRow 7 11, 10317220831068851700⟩, ⟨.privateRow 8 9, 5457773072777235210⟩, ⟨.hall 10 3, 14305728748867920⟩, ⟨.hall 11 3, 8322082589485665⟩, ⟨.hall 9 4, 13370354176826556⟩, ⟨.hall 8 5, 13045394986640240⟩, ⟨.hall 4 14, 211906034535267072⟩, ⟨.hall 3 15, 521799028672296375⟩, ⟨.hall 2 17, 6470784216947450400⟩]
  caps := #[0, 4018764220132725000, 140607679904218800, 501498823174631100, 22493578660608825, 0, 17193733178246625, 0, 0, 34999988644550160, 0, 0, 121708240495720200, 1568501411727600000] }

theorem case_34_21_13_checked :
    (Witness.linear .negative case_34_21_13).check 34 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_22_1_checked :
    (Witness.rising).check 34 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_22_2_checked :
    (Witness.rising).check 34 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_22_3_checked :
    (Witness.rising).check 34 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_22_4_checked :
    (Witness.rising).check 34 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_22_5_checked :
    (Witness.rising).check 34 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_22_6_checked :
    (Witness.rising).check 34 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_22_7_checked :
    (Witness.rising).check 34 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_34_22_8_checked :
    (Witness.linear .positive case_34_22_8).check 34 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_34_22_9_checked :
    (Witness.linear .positive case_34_22_9).check 34 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_34_22_10_checked :
    (Witness.linear .positive case_34_22_10).check 34 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_22_11 : Certificate := {
  objectiveScale := 312424235200000
  eta := 9658603666662350400
  rows := #[⟨.count 2, 1795258701215179200⟩, ⟨.count 3, 352340492761857600⟩, ⟨.count 4, 76806498951262080⟩, ⟨.count 5, 16778118702945600⟩, ⟨.count 6, 3994790167368000⟩, ⟨.count 7, 1165147132149000⟩, ⟨.count 8, 372847082287680⟩, ⟨.path 6, 518084498131200⟩, ⟨.path 7, 327359449667250⟩, ⟨.privateRow 2 20, 155197598002246800⟩, ⟨.privateRow 3 16, 5592706234315200⟩, ⟨.privateRow 3 17, 49588661944261440⟩, ⟨.privateRow 3 18, 59841956707172640⟩, ⟨.privateRow 4 14, 14149546772817456⟩, ⟨.privateRow 4 15, 25004057455917540⟩, ⟨.privateRow 4 16, 28181025302910480⟩, ⟨.privateRow 4 17, 28382984139149640⟩, ⟨.privateRow 5 11, 2190476608440120⟩, ⟨.privateRow 5 12, 8738603491117500⟩, ⟨.privateRow 5 13, 12033639580834872⟩, ⟨.privateRow 5 14, 13655524388786280⟩, ⟨.privateRow 5 15, 3883823773830000⟩, ⟨.privateRow 6 8, 110966393538000⟩, ⟨.privateRow 6 9, 2209618311325425⟩, ⟨.privateRow 6 10, 4841305226643600⟩, ⟨.privateRow 6 11, 6746756727110400⟩, ⟨.privateRow 6 12, 1544652198048960⟩, ⟨.privateRow 7 6, 199739508368400⟩, ⟨.privateRow 7 7, 1671893662639200⟩, ⟨.privateRow 7 8, 3158380976075325⟩, ⟨.privateRow 7 9, 394723314156600⟩, ⟨.privateRow 8 4, 207608034455640⟩, ⟨.privateRow 8 5, 1346910084764244⟩, ⟨.privateRow 8 6, 181245109445400⟩, ⟨.privateRow 9 2, 201958836239160⟩, ⟨.privateRow 9 3, 296582906365200⟩, ⟨.privateRow 10 0, 107552042967600⟩, ⟨.hall 2 19, 37191496458196080⟩, ⟨.assumptionRow 11, 346191046540416⟩]
  caps := #[0, 3717678652912224, 448872122306608, 0, 77887348166628, 138923504399680, 42946004699400, 0, 0, 0, 49009989775824, 2778051305459584, 312424235200000] }

theorem case_34_22_11_checked :
    (Witness.linear .conditional case_34_22_11).check 34 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_22_12 : Certificate := {
  objectiveScale := 11629020501000000
  eta := 510864205620483514800
  rows := #[⟨.count 2, 85488930085903344000⟩, ⟨.count 3, 14431345578787016880⟩, ⟨.count 4, 2514912440622341760⟩, ⟨.count 5, 395782083731034000⟩, ⟨.count 6, 67848357211034400⟩, ⟨.count 7, 16962089302758600⟩, ⟨.count 8, 9046447628137920⟩, ⟨.path 5, 91123266238804800⟩, ⟨.path 6, 27612307479556800⟩, ⟨.privateRow 2 20, 7938257793691024800⟩, ⟨.privateRow 3 16, 247646503820275560⟩, ⟨.privateRow 3 17, 2291012861825928240⟩, ⟨.privateRow 3 18, 3015859478030479080⟩, ⟨.privateRow 4 14, 559070463418923456⟩, ⟨.privateRow 4 15, 1124021117796136560⟩, ⟨.privateRow 4 16, 1425569372067400560⟩, ⟨.privateRow 4 17, 1683770064787170360⟩, ⟨.privateRow 5 11, 63002045981674800⟩, ⟨.privateRow 5 12, 328310661837838680⟩, ⟨.privateRow 5 13, 526277090766923496⟩, ⟨.privateRow 5 14, 691770542064171570⟩, ⟨.privateRow 5 15, 669814059800045160⟩, ⟨.privateRow 6 9, 56439332858583675⟩, ⟨.privateRow 6 10, 172505602092681000⟩, ⟨.privateRow 6 11, 285124643993989800⟩, ⟨.privateRow 6 12, 371227440168945360⟩, ⟨.privateRow 6 13, 46847675217142800⟩, ⟨.privateRow 7 7, 37334545766918400⟩, ⟨.privateRow 7 8, 103488937710283125⟩, ⟨.privateRow 7 9, 178967350398493800⟩, ⟨.privateRow 7 10, 43482181307865300⟩, ⟨.privateRow 8 5, 23973086214565488⟩, ⟨.privateRow 8 6, 75387063567816000⟩, ⟨.privateRow 8 7, 33924178605517200⟩, ⟨.privateRow 9 3, 17064889843987440⟩, ⟨.privateRow 9 4, 28043987647227552⟩, ⟨.privateRow 10 1, 13004268465448260⟩, ⟨.privateRow 11 0, 2827014883793100⟩, ⟨.hall 3 18, 223899578796413520⟩, ⟨.hall 2 19, 2096514237820962960⟩, ⟨.assumptionRow 12, 7723668081372320⟩]
  caps := #[0, 153392727313855120, 70928266188022880, 2493799455587440, 5291546735042568, 604464202653360, 2677831321025575, 2303562521730680, 368558977442656, 0, 0, 89544405407518600, 96937516427627680] }

theorem case_34_22_12_checked :
    (Witness.linear .conditional case_34_22_12).check 34 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_22_13 : Certificate := {
  objectiveScale := 76751535306600000
  eta := 4970197483315719454800
  rows := #[⟨.count 2, 816012192177110728800⟩, ⟨.count 3, 136002032029518454800⟩, ⟨.count 4, 20052958909039056000⟩, ⟨.count 5, 2936326125966433200⟩, ⟨.count 6, 245546435620886400⟩, ⟨.path 5, 984804549371042400⟩, ⟨.path 6, 252719528642380800⟩, ⟨.privateRow 2 20, 79710511663430247600⟩, ⟨.privateRow 3 16, 1965906150189721740⟩, ⟨.privateRow 3 17, 21728813332151605680⟩, ⟨.privateRow 3 18, 29993497111091273760⟩, ⟨.privateRow 4 6, 46276059020859360⟩, ⟨.privateRow 4 14, 4841357222325143520⟩, ⟨.privateRow 4 15, 10449023945817136680⟩, ⟨.privateRow 4 16, 14080041862560994320⟩, ⟨.privateRow 4 17, 17904427597356300000⟩, ⟨.privateRow 5 11, 601588767271171680⟩, ⟨.privateRow 5 12, 2762056364018831880⟩, ⟨.privateRow 5 13, 4729633594117640208⟩, ⟨.privateRow 5 14, 6696255921411256200⟩, ⟨.privateRow 5 15, 9085900191405077040⟩, ⟨.privateRow 6 8, 40924405936814400⟩, ⟨.privateRow 6 9, 477025106700992850⟩, ⟨.privateRow 6 10, 1401660903335893200⟩, ⟨.privateRow 6 11, 2451201397257112500⟩, ⟨.privateRow 6 12, 3474482064035542560⟩, ⟨.privateRow 6 13, 2571843135591679950⟩, ⟨.privateRow 7 6, 39901295788394040⟩, ⟨.privateRow 7 7, 309206622633708800⟩, ⟨.privateRow 7 8, 805059798038270775⟩, ⟨.privateRow 7 9, 1467432270020059200⟩, ⟨.privateRow 7 10, 1581557771099806500⟩, ⟨.privateRow 8 4, 31902434628016680⟩, ⟨.privateRow 8 5, 217001662479958356⟩, ⟨.privateRow 8 6, 568962921427100200⟩, ⟨.privateRow 8 7, 812861012919976020⟩, ⟨.privateRow 9 2, 32227969675241340⟩, ⟨.privateRow 9 3, 186206047012505520⟩, ⟨.privateRow 9 4, 379573865063953560⟩, ⟨.privateRow 10 0, 42970626233655120⟩, ⟨.privateRow 10 1, 157558962856735440⟩, ⟨.privateRow 11 0, 71617710389425200⟩, ⟨.hall 3 18, 3575608425021512880⟩, ⟨.hall 2 19, 22022445944748249000⟩]
  caps := #[0, 1854208182604932000, 0, 181524128632806960, 15601067823143880, 16657371266167632, 7173093021494400, 10066805047646490, 10363862320112392, 0, 137006607291301440, 0, 2686303735731000000] }

theorem case_34_22_13_checked :
    (Witness.linear .negative case_34_22_13).check 34 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_22_14 : Certificate := {
  objectiveScale := 113590400000
  eta := 10881642437265600
  rows := #[⟨.count 2, 1538253294177600⟩, ⟨.count 3, 202219815077280⟩, ⟨.count 4, 21960522904320⟩, ⟨.count 5, 1440312073200⟩, ⟨.path 4, 7285316328576⟩, ⟨.path 5, 1440548366400⟩, ⟨.hall 10 3, 2310661080⟩, ⟨.hall 8 6, 1783074240⟩, ⟨.hall 9 6, 5332294800⟩, ⟨.hall 7 7, 4763516688⟩, ⟨.hall 10 7, 9627754500⟩, ⟨.hall 6 9, 4373751330⟩, ⟨.hall 8 9, 7566780240⟩, ⟨.hall 5 11, 5256471825⟩]
  caps := #[0, 311108519040, 0, 0, 34921454656, 236293200, 18405701600, 31771589850, 0, 0, 732998851200, 0, 8519280000000] }

theorem case_34_22_14_checked :
    (Witness.linear .negative case_34_22_14).check 34 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_23_1_checked :
    (Witness.rising).check 34 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_23_2_checked :
    (Witness.rising).check 34 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_23_3_checked :
    (Witness.rising).check 34 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_23_4_checked :
    (Witness.rising).check 34 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_23_5_checked :
    (Witness.rising).check 34 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_23_6_checked :
    (Witness.rising).check 34 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_23_7_checked :
    (Witness.rising).check 34 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_34_23_8_checked :
    (Witness.linear .positive case_34_23_8).check 34 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_34_23_9_checked :
    (Witness.linear .positive case_34_23_9).check 34 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_34_23_10_checked :
    (Witness.linear .positive case_34_23_10).check 34 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_23_11 : Certificate := {
  objectiveScale := 5
  eta := 22984
  rows := #[⟨.assumptionRow 11, 12⟩]
  caps := #[0, 0, 7150, 2288, 759, 264, 98, 40, 350, 441, 181, 43] }

theorem case_34_23_11_checked :
    (Witness.linear .conditional case_34_23_11).check 34 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_23_12 : Certificate := {
  objectiveScale := 7543790100000
  eta := 864004794405152400
  rows := #[⟨.count 2, 108713317729816800⟩, ⟨.count 3, 13481465042485440⟩, ⟨.count 4, 1393760483715600⟩, ⟨.count 5, 99554320265400⟩, ⟨.count 6, 18100785502800⟩, ⟨.path 4, 747674520432840⟩, ⟨.path 5, 47936643955200⟩, ⟨.privateRow 2 20, 2603797994577780⟩, ⟨.privateRow 2 21, 8932737645631800⟩, ⟨.privateRow 3 17, 1938594127349880⟩, ⟨.privateRow 3 18, 3201425595928560⟩, ⟨.privateRow 3 19, 3180308012841960⟩, ⟨.privateRow 4 13, 61542670709520⟩, ⟨.privateRow 4 14, 398594380759575⟩, ⟨.privateRow 4 15, 1189764631099044⟩, ⟨.privateRow 4 16, 1415933945956530⟩, ⟨.privateRow 4 17, 1497236640839940⟩, ⟨.privateRow 4 18, 605018755431090⟩, ⟨.privateRow 5 10, 9251512590320⟩, ⟨.privateRow 5 11, 80322235668675⟩, ⟨.privateRow 5 12, 313143589198440⟩, ⟨.privateRow 5 13, 589783927632900⟩, ⟨.privateRow 5 14, 722583357271776⟩, ⟨.privateRow 5 15, 413602948738980⟩, ⟨.privateRow 6 8, 4676036254890⟩, ⟨.privateRow 6 9, 75419939595000⟩, ⟨.privateRow 6 10, 209290332376125⟩, ⟨.privateRow 6 11, 341544583594500⟩, ⟨.privateRow 6 12, 198857240732150⟩, ⟨.privateRow 7 6, 1974631145760⟩, ⟨.privateRow 7 7, 68239961345556⟩, ⟨.privateRow 7 8, 161901470330600⟩, ⟨.privateRow 7 9, 75118259836620⟩, ⟨.privateRow 8 5, 71415826438320⟩, ⟨.privateRow 8 6, 36111067078086⟩, ⟨.privateRow 9 3, 35195971811000⟩, ⟨.privateRow 10 1, 8771919128280⟩, ⟨.hall 2 20, 1292396084899920⟩, ⟨.assumptionRow 12, 5715175379760⟩]
  caps := #[0, 32309248411440, 7231276372320, 14012077423344, 6819330414897, 1043367009300, 23009508338245, 5715175379760, 5715175379760, 0, 136219726593720, 344497736222640] }

theorem case_34_23_12_checked :
    (Witness.linear .conditional case_34_23_12).check 34 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_23_13 : Certificate := {
  objectiveScale := 77593269600000
  eta := 12308932359185061600
  rows := #[⟨.count 2, 1488384150010037280⟩, ⟨.count 3, 169836050215671840⟩, ⟨.count 4, 14292380233010880⟩, ⟨.count 5, 162907069525200⟩, ⟨.path 4, 12791281530867840⟩, ⟨.path 5, 158559668467200⟩, ⟨.privateRow 2 20, 35921008830306600⟩, ⟨.privateRow 2 21, 130455981275780160⟩, ⟨.privateRow 3 17, 25163712005992560⟩, ⟨.privateRow 3 18, 44194877883636480⟩, ⟨.privateRow 3 19, 47083763249883360⟩, ⟨.privateRow 4 13, 1080616894517160⟩, ⟨.privateRow 4 14, 4608912508650450⟩, ⟨.privateRow 4 15, 15064016718995244⟩, ⟨.privateRow 4 16, 19371686904915345⟩, ⟨.privateRow 4 17, 22433208512895180⟩, ⟨.privateRow 4 18, 15299688946241700⟩, ⟨.privateRow 5 10, 336674610352080⟩, ⟨.privateRow 5 11, 920424942817380⟩, ⟨.privateRow 5 12, 3481556800138560⟩, ⟨.privateRow 5 13, 7272895615025040⟩, ⟨.privateRow 5 14, 9674507835536544⟩, ⟨.privateRow 5 15, 11026093489030620⟩, ⟨.privateRow 6 7, 51834067576200⟩, ⟨.privateRow 6 8, 205443915456780⟩, ⟨.privateRow 6 9, 792412165344800⟩, ⟨.privateRow 6 10, 2242234804159350⟩, ⟨.privateRow 6 11, 3794700389337000⟩, ⟨.privateRow 6 12, 6252312992425500⟩, ⟨.privateRow 7 4, 10025050432320⟩, ⟨.privateRow 7 5, 38011649555880⟩, ⟨.privateRow 7 6, 207336270304800⟩, ⟨.privateRow 7 7, 680951550615336⟩, ⟨.privateRow 7 8, 1672512580458720⟩, ⟨.privateRow 7 9, 2601082876752360⟩, ⟨.privateRow 8 1, 2534109970392⟩, ⟨.privateRow 8 2, 13575589127100⟩, ⟨.privateRow 8 3, 57017474333820⟩, ⟨.privateRow 8 4, 254994815770695⟩, ⟨.privateRow 8 5, 739499364087120⟩, ⟨.privateRow 8 6, 874267939785240⟩, ⟨.privateRow 9 0, 43924572820128⟩, ⟨.privateRow 9 1, 108604713016800⟩, ⟨.privateRow 9 2, 444443902499520⟩, ⟨.privateRow 9 3, 67576265877120⟩, ⟨.privateRow 10 0, 228069897335280⟩, ⟨.hall 2 20, 21177919038276000⟩, ⟨.assumptionRow 13, 17118368494920⟩]
  caps := #[0, 756560709550800, 451749436898760, 24469171638912, 21885603817077, 44750639378016, 0, 108695661734016, 5503334976909, 0, 0, 11024971619674320] }

theorem case_34_23_13_checked :
    (Witness.linear .conditional case_34_23_13).check 34 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_23_14 : Certificate := {
  objectiveScale := 382
  eta := 32260
  rows := #[⟨.assumptionRow 14, 159⟩]
  caps := #[0, 0, 13993, 8242, 3858, 2127, 1237, 572, 227942, 223223, 150293, 80564] }

theorem case_34_23_14_checked :
    (Witness.linear .conditional case_34_23_14).check 34 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_24_1_checked :
    (Witness.rising).check 34 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_24_2_checked :
    (Witness.rising).check 34 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_24_3_checked :
    (Witness.rising).check 34 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_24_4_checked :
    (Witness.rising).check 34 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_24_5_checked :
    (Witness.rising).check 34 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_24_6_checked :
    (Witness.rising).check 34 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_24_7_checked :
    (Witness.rising).check 34 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_34_24_8_checked :
    (Witness.linear .positive case_34_24_8).check 34 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_34_24_9_checked :
    (Witness.linear .positive case_34_24_9).check 34 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_34_24_10_checked :
    (Witness.linear .positive case_34_24_10).check 34 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_34_24_11_checked :
    (Witness.linear .positive case_34_24_11).check 34 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_24_12 : Certificate := {
  objectiveScale := 347
  eta := 2117622
  rows := #[⟨.assumptionRow 12, 563⟩]
  caps := #[0, 0, 669136, 216216, 71786, 24645, 8824, 3332, 174776, 118720, 51380] }

theorem case_34_24_12_checked :
    (Witness.linear .conditional case_34_24_12).check 34 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_24_13 : Certificate := {
  objectiveScale := 116483598000000
  eta := 29443604988953675520
  rows := #[⟨.count 2, 2872707162351586560⟩, ⟨.count 3, 231722946162227520⟩, ⟨.count 4, 9391000857638400⟩, ⟨.path 3, 121728769546784400⟩, ⟨.path 4, 8749056391891200⟩, ⟨.privateRow 2 21, 272534670722714400⟩, ⟨.privateRow 2 22, 274999808447844480⟩, ⟨.privateRow 3 17, 40428258692133312⟩, ⟨.privateRow 3 18, 69708616782845040⟩, ⟨.privateRow 3 19, 132523978075048560⟩, ⟨.privateRow 3 20, 96345799423833960⟩, ⟨.privateRow 4 13, 2024934559928280⟩, ⟨.privateRow 4 14, 12392767203204960⟩, ⟨.privateRow 4 15, 19535238242399880⟩, ⟨.privateRow 4 16, 43715108992306752⟩, ⟨.privateRow 4 17, 52384176659014200⟩, ⟨.privateRow 4 18, 35607544918545600⟩, ⟨.privateRow 5 10, 763018819683120⟩, ⟨.privateRow 5 11, 3152072047124000⟩, ⟨.privateRow 5 12, 6294905262385740⟩, ⟨.privateRow 5 13, 14494562633247840⟩, ⟨.privateRow 5 14, 22897086118866960⟩, ⟨.privateRow 5 15, 20065438499154048⟩, ⟨.privateRow 6 7, 270643427494440⟩, ⟨.privateRow 6 8, 942657283058400⟩, ⟨.privateRow 6 9, 2089497690824544⟩, ⟨.privateRow 6 10, 5756335710885760⟩, ⟨.privateRow 6 11, 10393685845042500⟩, ⟨.privateRow 6 12, 6976172065674240⟩, ⟨.privateRow 7 4, 134157155109120⟩, ⟨.privateRow 7 5, 428915904555600⟩, ⟨.privateRow 7 6, 924426646923780⟩, ⟨.privateRow 7 7, 2651890583094480⟩, ⟨.privateRow 7 8, 5593514885830872⟩, ⟨.privateRow 8 1, 94154565890385⟩, ⟨.privateRow 8 2, 100431536949744⟩, ⟨.privateRow 8 3, 714107356882920⟩, ⟨.privateRow 8 4, 2496742054939440⟩, ⟨.privateRow 9 0, 1129854790684620⟩, ⟨.privateRow 10 0, 328685030017344⟩, ⟨.hall 2 21, 14741025588656640⟩, ⟨.assumptionRow 13, 47284885837728⟩]
  caps := #[0, 647544917527200, 826858071261264, 0, 101230274742696, 47284885837728, 65475684245660, 402646239133128, 0, 0, 14946688859854752] }

theorem case_34_24_13_checked :
    (Witness.linear .conditional case_34_24_13).check 34 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_24_14 : Certificate := {
  objectiveScale := 11
  eta := 9384
  rows := #[⟨.assumptionRow 14, 7⟩]
  caps := #[0, 0, 3976, 1456, 715, 286, 140, 3978, 12272, 10556, 6552] }

theorem case_34_24_14_checked :
    (Witness.linear .conditional case_34_24_14).check 34 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_24_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 1430, 1430, 1001] }

theorem case_34_24_15_checked :
    (Witness.linear .negative case_34_24_15).check 34 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_25_1_checked :
    (Witness.rising).check 34 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_25_2_checked :
    (Witness.rising).check 34 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_25_3_checked :
    (Witness.rising).check 34 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_25_4_checked :
    (Witness.rising).check 34 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_25_5_checked :
    (Witness.rising).check 34 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_25_6_checked :
    (Witness.rising).check 34 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_25_7_checked :
    (Witness.rising).check 34 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_34_25_8_checked :
    (Witness.linear .positive case_34_25_8).check 34 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_34_25_9_checked :
    (Witness.linear .positive case_34_25_9).check 34 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_34_25_10_checked :
    (Witness.linear .positive case_34_25_10).check 34 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_34_25_11_checked :
    (Witness.linear .positive case_34_25_11).check 34 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_25_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_34_25_12_checked :
    (Witness.linear .positive case_34_25_12).check 34 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_25_13 : Certificate := {
  objectiveScale := 389
  eta := 1694016
  rows := #[⟨.assumptionRow 13, 421⟩]
  caps := #[0, 0, 570180, 205660, 73931, 26675, 9705, 949824, 803964, 460712] }

theorem case_34_25_13_checked :
    (Witness.linear .conditional case_34_25_13).check 34 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_25_14 : Certificate := {
  objectiveScale := 563
  eta := 647496
  rows := #[⟨.assumptionRow 14, 375⟩]
  caps := #[0, 0, 246120, 101920, 43771, 16478, 8420, 1746342, 1661036, 1093820] }

theorem case_34_25_14_checked :
    (Witness.linear .conditional case_34_25_14).check 34 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_25_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 4862, 4862, 3432] }

theorem case_34_25_15_checked :
    (Witness.linear .negative case_34_25_15).check 34 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1430] }

theorem case_34_25_16_checked :
    (Witness.linear .negative case_34_25_16).check 34 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_26_1_checked :
    (Witness.rising).check 34 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_26_2_checked :
    (Witness.rising).check 34 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_26_3_checked :
    (Witness.rising).check 34 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_26_4_checked :
    (Witness.rising).check 34 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_26_5_checked :
    (Witness.rising).check 34 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_26_6_checked :
    (Witness.rising).check 34 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_26_7_checked :
    (Witness.rising).check 34 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_34_26_8_checked :
    (Witness.linear .positive case_34_26_8).check 34 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_34_26_9_checked :
    (Witness.linear .positive case_34_26_9).check 34 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_34_26_10_checked :
    (Witness.linear .positive case_34_26_10).check 34 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_34_26_11_checked :
    (Witness.linear .positive case_34_26_11).check 34 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_34_26_12_checked :
    (Witness.linear .positive case_34_26_12).check 34 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_26_13 : Certificate := {
  objectiveScale := 704
  eta := 10207446
  rows := #[⟨.assumptionRow 13, 1055⟩]
  caps := #[0, 0, 3255330, 1058200, 351351, 119735, 42150, 15504, 1226244] }

theorem case_34_26_13_checked :
    (Witness.linear .conditional case_34_26_13).check 34 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_26_14 : Certificate := {
  objectiveScale := 985
  eta := 4565928
  rows := #[⟨.assumptionRow 14, 853⟩]
  caps := #[0, 0, 1527484, 595140, 226408, 82885, 32395, 4978722, 4534512] }

theorem case_34_26_14_checked :
    (Witness.linear .conditional case_34_26_14).check 34 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_26_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 16796, 16796, 11934] }

theorem case_34_26_15_checked :
    (Witness.linear .negative case_34_26_15).check 34 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_26_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 4862] }

theorem case_34_26_16_checked :
    (Witness.linear .negative case_34_26_16).check 34 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_27_1_checked :
    (Witness.rising).check 34 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_27_2_checked :
    (Witness.rising).check 34 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_27_3_checked :
    (Witness.rising).check 34 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_27_4_checked :
    (Witness.rising).check 34 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_27_5_checked :
    (Witness.rising).check 34 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_27_6_checked :
    (Witness.rising).check 34 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_27_7_checked :
    (Witness.rising).check 34 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_34_27_8_checked :
    (Witness.linear .positive case_34_27_8).check 34 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_34_27_9_checked :
    (Witness.linear .positive case_34_27_9).check 34 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_34_27_10_checked :
    (Witness.linear .positive case_34_27_10).check 34 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_34_27_11_checked :
    (Witness.linear .positive case_34_27_11).check 34 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_34_27_12_checked :
    (Witness.linear .positive case_34_27_12).check 34 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_27_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_34_27_13_checked :
    (Witness.linear .positive case_34_27_13).check 34 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_27_14 : Certificate := {
  objectiveScale := 13
  eta := 77520
  rows := #[⟨.assumptionRow 14, 12⟩]
  caps := #[0, 0, 29172, 10556, 3731, 1298, 129200, 164730] }

theorem case_34_27_14_checked :
    (Witness.linear .conditional case_34_27_14).check 34 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_27_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 58786, 58786, 41990] }

theorem case_34_27_15_checked :
    (Witness.linear .negative case_34_27_15).check 34 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_27_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 16796] }

theorem case_34_27_16_checked :
    (Witness.linear .negative case_34_27_16).check 34 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_34_27_17_checked :
    (Witness.linear .negative case_34_27_17).check 34 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_28_1_checked :
    (Witness.rising).check 34 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_28_2_checked :
    (Witness.rising).check 34 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_28_3_checked :
    (Witness.rising).check 34 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_28_4_checked :
    (Witness.rising).check 34 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_28_5_checked :
    (Witness.rising).check 34 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_28_6_checked :
    (Witness.rising).check 34 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_28_7_checked :
    (Witness.rising).check 34 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_28_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_34_28_8_checked :
    (Witness.linear .positive case_34_28_8).check 34 28 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_34_28_9_checked :
    (Witness.linear .positive case_34_28_9).check 34 28 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_34_28_10_checked :
    (Witness.linear .positive case_34_28_10).check 34 28 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_34_28_11_checked :
    (Witness.linear .positive case_34_28_11).check 34 28 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_34_28_12_checked :
    (Witness.linear .positive case_34_28_12).check 34 28 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_34_28_13_checked :
    (Witness.linear .positive case_34_28_13).check 34 28 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_28_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_34_28_14_checked :
    (Witness.linear .positive case_34_28_14).check 34 28 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_28_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 208012, 208012, 149226] }

theorem case_34_28_15_checked :
    (Witness.linear .negative case_34_28_15).check 34 28 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_28_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 58786] }

theorem case_34_28_16_checked :
    (Witness.linear .negative case_34_28_16).check 34 28 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_28_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_34_28_17_checked :
    (Witness.linear .negative case_34_28_17).check 34 28 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_34_28_18_checked :
    (Witness.linear .negative case_34_28_18).check 34 28 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_29_1_checked :
    (Witness.rising).check 34 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_29_2_checked :
    (Witness.rising).check 34 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_29_3_checked :
    (Witness.rising).check 34 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_29_4_checked :
    (Witness.rising).check 34 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_29_5_checked :
    (Witness.rising).check 34 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_29_6_checked :
    (Witness.rising).check 34 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_29_7_checked :
    (Witness.rising).check 34 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_29_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_34_29_8_checked :
    (Witness.linear .positive case_34_29_8).check 34 29 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_34_29_9_checked :
    (Witness.linear .positive case_34_29_9).check 34 29 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_34_29_10_checked :
    (Witness.linear .positive case_34_29_10).check 34 29 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_34_29_11_checked :
    (Witness.linear .positive case_34_29_11).check 34 29 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_34_29_12_checked :
    (Witness.linear .positive case_34_29_12).check 34 29 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_34_29_13_checked :
    (Witness.linear .positive case_34_29_13).check 34 29 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_29_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_34_29_14_checked :
    (Witness.linear .positive case_34_29_14).check 34 29 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_29_15 : Certificate := {
  objectiveScale := 5
  eta := 38760
  rows := #[⟨.assumptionRow 15, 4⟩]
  caps := #[0, 0, 15504, 5712, 2002, 59432] }

theorem case_34_29_15_checked :
    (Witness.linear .conditional case_34_29_15).check 34 29 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_29_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 208012] }

theorem case_34_29_16_checked :
    (Witness.linear .negative case_34_29_16).check 34 29 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_29_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_34_29_17_checked :
    (Witness.linear .negative case_34_29_17).check 34 29 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_34_29_18_checked :
    (Witness.linear .negative case_34_29_18).check 34 29 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_30_1_checked :
    (Witness.rising).check 34 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_30_2_checked :
    (Witness.rising).check 34 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_30_3_checked :
    (Witness.rising).check 34 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_30_4_checked :
    (Witness.rising).check 34 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_30_5_checked :
    (Witness.rising).check 34 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_30_6_checked :
    (Witness.rising).check 34 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_34_30_7_checked :
    (Witness.linear .positive case_34_30_7).check 34 30 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_34_30_8_checked :
    (Witness.linear .positive case_34_30_8).check 34 30 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_34_30_9_checked :
    (Witness.linear .positive case_34_30_9).check 34 30 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_34_30_10_checked :
    (Witness.linear .positive case_34_30_10).check 34 30 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_34_30_11_checked :
    (Witness.linear .positive case_34_30_11).check 34 30 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_34_30_12_checked :
    (Witness.linear .positive case_34_30_12).check 34 30 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_34_30_13_checked :
    (Witness.linear .positive case_34_30_13).check 34 30 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_34_30_14_checked :
    (Witness.linear .positive case_34_30_14).check 34 30 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_34_30_15_checked :
    (Witness.linear .positive case_34_30_15).check 34 30 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 742900] }

theorem case_34_30_16_checked :
    (Witness.linear .negative case_34_30_16).check 34 30 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_34_30_17_checked :
    (Witness.linear .negative case_34_30_17).check 34 30 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_34_30_18_checked :
    (Witness.linear .negative case_34_30_18).check 34 30 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_34_30_19_checked :
    (Witness.linear .negative case_34_30_19).check 34 30 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_31_1_checked :
    (Witness.rising).check 34 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_31_2_checked :
    (Witness.rising).check 34 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_31_3_checked :
    (Witness.rising).check 34 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_31_4_checked :
    (Witness.rising).check 34 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_31_5_checked :
    (Witness.rising).check 34 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_31_6_checked :
    (Witness.rising).check 34 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_34_31_7_checked :
    (Witness.linear .positive case_34_31_7).check 34 31 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_34_31_8_checked :
    (Witness.linear .positive case_34_31_8).check 34 31 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_34_31_9_checked :
    (Witness.linear .positive case_34_31_9).check 34 31 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_34_31_10_checked :
    (Witness.linear .positive case_34_31_10).check 34 31 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_34_31_11_checked :
    (Witness.linear .positive case_34_31_11).check 34 31 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_34_31_12_checked :
    (Witness.linear .positive case_34_31_12).check 34 31 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_34_31_13_checked :
    (Witness.linear .positive case_34_31_13).check 34 31 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_34_31_14_checked :
    (Witness.linear .positive case_34_31_14).check 34 31 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_34_31_15_checked :
    (Witness.linear .positive case_34_31_15).check 34 31 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 2674440] }

theorem case_34_31_16_checked :
    (Witness.linear .negative case_34_31_16).check 34 31 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_34_31_17_checked :
    (Witness.linear .negative case_34_31_17).check 34 31 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_34_31_18_checked :
    (Witness.linear .negative case_34_31_18).check 34 31 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_34_31_19_checked :
    (Witness.linear .negative case_34_31_19).check 34 31 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_34_31_20_checked :
    (Witness.linear .negative case_34_31_20).check 34 31 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_32_1_checked :
    (Witness.rising).check 34 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_32_2_checked :
    (Witness.rising).check 34 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_32_3_checked :
    (Witness.rising).check 34 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_32_4_checked :
    (Witness.rising).check 34 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_32_5_checked :
    (Witness.rising).check 34 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_32_6_checked :
    (Witness.rising).check 34 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_34_32_7_checked :
    (Witness.linear .positive case_34_32_7).check 34 32 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_34_32_8_checked :
    (Witness.linear .positive case_34_32_8).check 34 32 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_34_32_9_checked :
    (Witness.linear .positive case_34_32_9).check 34 32 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_34_32_10_checked :
    (Witness.linear .positive case_34_32_10).check 34 32 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_34_32_11_checked :
    (Witness.linear .positive case_34_32_11).check 34 32 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_34_32_12_checked :
    (Witness.linear .positive case_34_32_12).check 34 32 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_34_32_13_checked :
    (Witness.linear .positive case_34_32_13).check 34 32 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_34_32_14_checked :
    (Witness.linear .positive case_34_32_14).check 34 32 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_34_32_15_checked :
    (Witness.linear .positive case_34_32_15).check 34 32 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_34_32_16_checked :
    (Witness.linear .positive case_34_32_16).check 34 32 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_34_32_17_checked :
    (Witness.linear .negative case_34_32_17).check 34 32 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_34_32_18_checked :
    (Witness.linear .negative case_34_32_18).check 34 32 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_34_32_19_checked :
    (Witness.linear .negative case_34_32_19).check 34 32 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_34_32_20_checked :
    (Witness.linear .negative case_34_32_20).check 34 32 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_33_1_checked :
    (Witness.rising).check 34 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_33_2_checked :
    (Witness.rising).check 34 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_33_3_checked :
    (Witness.rising).check 34 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_33_4_checked :
    (Witness.rising).check 34 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_33_5_checked :
    (Witness.rising).check 34 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_34_33_6_checked :
    (Witness.rising).check 34 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_7_checked :
    (Witness.linear .positive case_34_33_7).check 34 33 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_8_checked :
    (Witness.linear .positive case_34_33_8).check 34 33 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_9_checked :
    (Witness.linear .positive case_34_33_9).check 34 33 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_10_checked :
    (Witness.linear .positive case_34_33_10).check 34 33 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_11_checked :
    (Witness.linear .positive case_34_33_11).check 34 33 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_12_checked :
    (Witness.linear .positive case_34_33_12).check 34 33 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_13_checked :
    (Witness.linear .positive case_34_33_13).check 34 33 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_14_checked :
    (Witness.linear .positive case_34_33_14).check 34 33 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_15_checked :
    (Witness.linear .positive case_34_33_15).check 34 33 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_16_checked :
    (Witness.linear .positive case_34_33_16).check 34 33 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_17_checked :
    (Witness.linear .negative case_34_33_17).check 34 33 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_18_checked :
    (Witness.linear .negative case_34_33_18).check 34 33 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_19_checked :
    (Witness.linear .negative case_34_33_19).check 34 33 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_20_checked :
    (Witness.linear .negative case_34_33_20).check 34 33 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_34_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_34_33_21_checked :
    (Witness.linear .negative case_34_33_21).check 34 33 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_34 (a k : ℕ) (h : Domain 34 a k) :
    ∃ w : Witness, w.check 34 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 17 ≤ a := by omega
  have haHi : a ≤ 33 := by omega
  interval_cases a

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_17_1_checked⟩

    · exact ⟨Witness.rising, case_34_17_2_checked⟩

    · exact ⟨Witness.rising, case_34_17_3_checked⟩

    · exact ⟨Witness.rising, case_34_17_4_checked⟩

    · exact ⟨Witness.rising, case_34_17_5_checked⟩

    · exact ⟨Witness.rising, case_34_17_6_checked⟩

    · exact ⟨Witness.rising, case_34_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_17_8, case_34_17_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_17_9, case_34_17_9_checked⟩

    · exact ⟨Witness.linear .conditional case_34_17_10, case_34_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_18_1_checked⟩

    · exact ⟨Witness.rising, case_34_18_2_checked⟩

    · exact ⟨Witness.rising, case_34_18_3_checked⟩

    · exact ⟨Witness.rising, case_34_18_4_checked⟩

    · exact ⟨Witness.rising, case_34_18_5_checked⟩

    · exact ⟨Witness.rising, case_34_18_6_checked⟩

    · exact ⟨Witness.rising, case_34_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_18_8, case_34_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_18_9, case_34_18_9_checked⟩

    · exact ⟨Witness.linear .conditional case_34_18_10, case_34_18_10_checked⟩

    · exact ⟨Witness.linear .conditional case_34_18_11, case_34_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_19_1_checked⟩

    · exact ⟨Witness.rising, case_34_19_2_checked⟩

    · exact ⟨Witness.rising, case_34_19_3_checked⟩

    · exact ⟨Witness.rising, case_34_19_4_checked⟩

    · exact ⟨Witness.rising, case_34_19_5_checked⟩

    · exact ⟨Witness.rising, case_34_19_6_checked⟩

    · exact ⟨Witness.rising, case_34_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_19_8, case_34_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_19_9, case_34_19_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_19_10, case_34_19_10_checked⟩

    · exact ⟨Witness.linear .conditional case_34_19_11, case_34_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_34_19_12, case_34_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_20_1_checked⟩

    · exact ⟨Witness.rising, case_34_20_2_checked⟩

    · exact ⟨Witness.rising, case_34_20_3_checked⟩

    · exact ⟨Witness.rising, case_34_20_4_checked⟩

    · exact ⟨Witness.rising, case_34_20_5_checked⟩

    · exact ⟨Witness.rising, case_34_20_6_checked⟩

    · exact ⟨Witness.rising, case_34_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_20_8, case_34_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_20_9, case_34_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_20_10, case_34_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_34_20_11, case_34_20_11_checked⟩

    · exact ⟨Witness.linear .conditional case_34_20_12, case_34_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_21_1_checked⟩

    · exact ⟨Witness.rising, case_34_21_2_checked⟩

    · exact ⟨Witness.rising, case_34_21_3_checked⟩

    · exact ⟨Witness.rising, case_34_21_4_checked⟩

    · exact ⟨Witness.rising, case_34_21_5_checked⟩

    · exact ⟨Witness.rising, case_34_21_6_checked⟩

    · exact ⟨Witness.rising, case_34_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_21_8, case_34_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_21_9, case_34_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_21_10, case_34_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_34_21_11, case_34_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_34_21_12, case_34_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_34_21_13, case_34_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_22_1_checked⟩

    · exact ⟨Witness.rising, case_34_22_2_checked⟩

    · exact ⟨Witness.rising, case_34_22_3_checked⟩

    · exact ⟨Witness.rising, case_34_22_4_checked⟩

    · exact ⟨Witness.rising, case_34_22_5_checked⟩

    · exact ⟨Witness.rising, case_34_22_6_checked⟩

    · exact ⟨Witness.rising, case_34_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_22_8, case_34_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_22_9, case_34_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_22_10, case_34_22_10_checked⟩

    · exact ⟨Witness.linear .conditional case_34_22_11, case_34_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_34_22_12, case_34_22_12_checked⟩

    · exact ⟨Witness.linear .negative case_34_22_13, case_34_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_34_22_14, case_34_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_23_1_checked⟩

    · exact ⟨Witness.rising, case_34_23_2_checked⟩

    · exact ⟨Witness.rising, case_34_23_3_checked⟩

    · exact ⟨Witness.rising, case_34_23_4_checked⟩

    · exact ⟨Witness.rising, case_34_23_5_checked⟩

    · exact ⟨Witness.rising, case_34_23_6_checked⟩

    · exact ⟨Witness.rising, case_34_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_23_8, case_34_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_23_9, case_34_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_23_10, case_34_23_10_checked⟩

    · exact ⟨Witness.linear .conditional case_34_23_11, case_34_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_34_23_12, case_34_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_34_23_13, case_34_23_13_checked⟩

    · exact ⟨Witness.linear .conditional case_34_23_14, case_34_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_24_1_checked⟩

    · exact ⟨Witness.rising, case_34_24_2_checked⟩

    · exact ⟨Witness.rising, case_34_24_3_checked⟩

    · exact ⟨Witness.rising, case_34_24_4_checked⟩

    · exact ⟨Witness.rising, case_34_24_5_checked⟩

    · exact ⟨Witness.rising, case_34_24_6_checked⟩

    · exact ⟨Witness.rising, case_34_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_24_8, case_34_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_24_9, case_34_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_24_10, case_34_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_34_24_11, case_34_24_11_checked⟩

    · exact ⟨Witness.linear .conditional case_34_24_12, case_34_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_34_24_13, case_34_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_34_24_14, case_34_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_34_24_15, case_34_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_25_1_checked⟩

    · exact ⟨Witness.rising, case_34_25_2_checked⟩

    · exact ⟨Witness.rising, case_34_25_3_checked⟩

    · exact ⟨Witness.rising, case_34_25_4_checked⟩

    · exact ⟨Witness.rising, case_34_25_5_checked⟩

    · exact ⟨Witness.rising, case_34_25_6_checked⟩

    · exact ⟨Witness.rising, case_34_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_25_8, case_34_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_25_9, case_34_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_25_10, case_34_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_34_25_11, case_34_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_34_25_12, case_34_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_34_25_13, case_34_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_34_25_14, case_34_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_34_25_15, case_34_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_34_25_16, case_34_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_26_1_checked⟩

    · exact ⟨Witness.rising, case_34_26_2_checked⟩

    · exact ⟨Witness.rising, case_34_26_3_checked⟩

    · exact ⟨Witness.rising, case_34_26_4_checked⟩

    · exact ⟨Witness.rising, case_34_26_5_checked⟩

    · exact ⟨Witness.rising, case_34_26_6_checked⟩

    · exact ⟨Witness.rising, case_34_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_26_8, case_34_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_26_9, case_34_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_26_10, case_34_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_34_26_11, case_34_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_34_26_12, case_34_26_12_checked⟩

    · exact ⟨Witness.linear .conditional case_34_26_13, case_34_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_34_26_14, case_34_26_14_checked⟩

    · exact ⟨Witness.linear .negative case_34_26_15, case_34_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_34_26_16, case_34_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_27_1_checked⟩

    · exact ⟨Witness.rising, case_34_27_2_checked⟩

    · exact ⟨Witness.rising, case_34_27_3_checked⟩

    · exact ⟨Witness.rising, case_34_27_4_checked⟩

    · exact ⟨Witness.rising, case_34_27_5_checked⟩

    · exact ⟨Witness.rising, case_34_27_6_checked⟩

    · exact ⟨Witness.rising, case_34_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_27_8, case_34_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_27_9, case_34_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_27_10, case_34_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_34_27_11, case_34_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_34_27_12, case_34_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_34_27_13, case_34_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_34_27_14, case_34_27_14_checked⟩

    · exact ⟨Witness.linear .negative case_34_27_15, case_34_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_34_27_16, case_34_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_34_27_17, case_34_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_28_1_checked⟩

    · exact ⟨Witness.rising, case_34_28_2_checked⟩

    · exact ⟨Witness.rising, case_34_28_3_checked⟩

    · exact ⟨Witness.rising, case_34_28_4_checked⟩

    · exact ⟨Witness.rising, case_34_28_5_checked⟩

    · exact ⟨Witness.rising, case_34_28_6_checked⟩

    · exact ⟨Witness.rising, case_34_28_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_28_8, case_34_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_28_9, case_34_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_28_10, case_34_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_34_28_11, case_34_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_34_28_12, case_34_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_34_28_13, case_34_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_34_28_14, case_34_28_14_checked⟩

    · exact ⟨Witness.linear .negative case_34_28_15, case_34_28_15_checked⟩

    · exact ⟨Witness.linear .negative case_34_28_16, case_34_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_34_28_17, case_34_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_34_28_18, case_34_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_29_1_checked⟩

    · exact ⟨Witness.rising, case_34_29_2_checked⟩

    · exact ⟨Witness.rising, case_34_29_3_checked⟩

    · exact ⟨Witness.rising, case_34_29_4_checked⟩

    · exact ⟨Witness.rising, case_34_29_5_checked⟩

    · exact ⟨Witness.rising, case_34_29_6_checked⟩

    · exact ⟨Witness.rising, case_34_29_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_29_8, case_34_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_29_9, case_34_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_29_10, case_34_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_34_29_11, case_34_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_34_29_12, case_34_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_34_29_13, case_34_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_34_29_14, case_34_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_34_29_15, case_34_29_15_checked⟩

    · exact ⟨Witness.linear .negative case_34_29_16, case_34_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_34_29_17, case_34_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_34_29_18, case_34_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_30_1_checked⟩

    · exact ⟨Witness.rising, case_34_30_2_checked⟩

    · exact ⟨Witness.rising, case_34_30_3_checked⟩

    · exact ⟨Witness.rising, case_34_30_4_checked⟩

    · exact ⟨Witness.rising, case_34_30_5_checked⟩

    · exact ⟨Witness.rising, case_34_30_6_checked⟩

    · exact ⟨Witness.linear .positive case_34_30_7, case_34_30_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_30_8, case_34_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_30_9, case_34_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_30_10, case_34_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_34_30_11, case_34_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_34_30_12, case_34_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_34_30_13, case_34_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_34_30_14, case_34_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_34_30_15, case_34_30_15_checked⟩

    · exact ⟨Witness.linear .negative case_34_30_16, case_34_30_16_checked⟩

    · exact ⟨Witness.linear .negative case_34_30_17, case_34_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_34_30_18, case_34_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_34_30_19, case_34_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_31_1_checked⟩

    · exact ⟨Witness.rising, case_34_31_2_checked⟩

    · exact ⟨Witness.rising, case_34_31_3_checked⟩

    · exact ⟨Witness.rising, case_34_31_4_checked⟩

    · exact ⟨Witness.rising, case_34_31_5_checked⟩

    · exact ⟨Witness.rising, case_34_31_6_checked⟩

    · exact ⟨Witness.linear .positive case_34_31_7, case_34_31_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_31_8, case_34_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_31_9, case_34_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_31_10, case_34_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_34_31_11, case_34_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_34_31_12, case_34_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_34_31_13, case_34_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_34_31_14, case_34_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_34_31_15, case_34_31_15_checked⟩

    · exact ⟨Witness.linear .negative case_34_31_16, case_34_31_16_checked⟩

    · exact ⟨Witness.linear .negative case_34_31_17, case_34_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_34_31_18, case_34_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_34_31_19, case_34_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_34_31_20, case_34_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_32_1_checked⟩

    · exact ⟨Witness.rising, case_34_32_2_checked⟩

    · exact ⟨Witness.rising, case_34_32_3_checked⟩

    · exact ⟨Witness.rising, case_34_32_4_checked⟩

    · exact ⟨Witness.rising, case_34_32_5_checked⟩

    · exact ⟨Witness.rising, case_34_32_6_checked⟩

    · exact ⟨Witness.linear .positive case_34_32_7, case_34_32_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_32_8, case_34_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_32_9, case_34_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_32_10, case_34_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_34_32_11, case_34_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_34_32_12, case_34_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_34_32_13, case_34_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_34_32_14, case_34_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_34_32_15, case_34_32_15_checked⟩

    · exact ⟨Witness.linear .positive case_34_32_16, case_34_32_16_checked⟩

    · exact ⟨Witness.linear .negative case_34_32_17, case_34_32_17_checked⟩

    · exact ⟨Witness.linear .negative case_34_32_18, case_34_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_34_32_19, case_34_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_34_32_20, case_34_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_34_33_1_checked⟩

    · exact ⟨Witness.rising, case_34_33_2_checked⟩

    · exact ⟨Witness.rising, case_34_33_3_checked⟩

    · exact ⟨Witness.rising, case_34_33_4_checked⟩

    · exact ⟨Witness.rising, case_34_33_5_checked⟩

    · exact ⟨Witness.rising, case_34_33_6_checked⟩

    · exact ⟨Witness.linear .positive case_34_33_7, case_34_33_7_checked⟩

    · exact ⟨Witness.linear .positive case_34_33_8, case_34_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_34_33_9, case_34_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_34_33_10, case_34_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_34_33_11, case_34_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_34_33_12, case_34_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_34_33_13, case_34_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_34_33_14, case_34_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_34_33_15, case_34_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_34_33_16, case_34_33_16_checked⟩

    · exact ⟨Witness.linear .negative case_34_33_17, case_34_33_17_checked⟩

    · exact ⟨Witness.linear .negative case_34_33_18, case_34_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_34_33_19, case_34_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_34_33_20, case_34_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_34_33_21, case_34_33_21_checked⟩


#print axioms coverage_34
end ForestUnimodality.FiniteRows.FiniteData
