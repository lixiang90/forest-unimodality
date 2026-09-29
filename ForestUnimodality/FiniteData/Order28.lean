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

theorem case_28_14_1_checked :
    (Witness.rising).check 28 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_14_2_checked :
    (Witness.rising).check 28 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_14_3_checked :
    (Witness.rising).check 28 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_14_4_checked :
    (Witness.rising).check 28 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_14_5_checked :
    (Witness.rising).check 28 14 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_14_6_checked :
    (Witness.rising).check 28 14 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_14_7 : Certificate := {
  objectiveScale := 141792000
  eta := 1824863040
  rows := #[⟨.count 2, 4573855440⟩, ⟨.count 3, 1965237120⟩, ⟨.count 4, 467913600⟩, ⟨.count 5, 172277280⟩, ⟨.count 6, 141792000⟩, ⟨.path 7, 30735250⟩, ⟨.path 8, 32131080⟩, ⟨.privateRow 8 0, 4589250⟩, ⟨.hall 6 1, 5779290⟩, ⟨.hall 1 2, 44575860⟩, ⟨.hall 0 3, 325146780⟩, ⟨.hall 5 3, 842945⟩, ⟨.hall 6 3, 226614⟩, ⟨.hall 1 5, 923125⟩, ⟨.hall 5 5, 341820⟩, ⟨.hall 4 6, 957096⟩, ⟨.hall 3 10, 34030080⟩]
  caps := #[0, 0, 0, 656460, 1283520, 249970, 227360, 28420, 6330, 0, 0, 0, 0, 0, 0] }

theorem case_28_14_7_checked :
    (Witness.linear .positive case_28_14_7).check 28 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_14_8 : Certificate := {
  objectiveScale := 7875000
  eta := 0
  rows := #[⟨.count 2, 675259200⟩, ⟨.count 3, 220581900⟩, ⟨.count 4, 55112400⟩, ⟨.count 5, 18370800⟩, ⟨.count 6, 7862400⟩, ⟨.count 7, 7871850⟩, ⟨.path 9, 2625000⟩, ⟨.privateRow 4 10, 4290300⟩, ⟨.privateRow 9 0, 437500⟩, ⟨.privateRow 10 0, 700056⟩, ⟨.hall 7 1, 246225⟩, ⟨.hall 0 2, 207900⟩, ⟨.hall 7 2, 109410⟩, ⟨.hall 1 3, 54810⟩, ⟨.hall 6 3, 42210⟩, ⟨.hall 0 4, 3356640⟩, ⟨.hall 1 4, 249480⟩, ⟨.hall 0 5, 2587200⟩, ⟨.hall 6 5, 78150⟩, ⟨.hall 8 5, 218400⟩, ⟨.hall 5 7, 136500⟩, ⟨.hall 4 8, 1185240⟩, ⟨.hall 1 11, 3846150⟩]
  caps := #[0, 0, 831600, 0, 18900, 4200, 33600, 6300, 0, 1120, 0, 0, 0, 0, 0] }

theorem case_28_14_8_checked :
    (Witness.linear .positive case_28_14_8).check 28 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_15_1_checked :
    (Witness.rising).check 28 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_15_2_checked :
    (Witness.rising).check 28 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_15_3_checked :
    (Witness.rising).check 28 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_15_4_checked :
    (Witness.rising).check 28 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_15_5_checked :
    (Witness.rising).check 28 15 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_15_6_checked :
    (Witness.rising).check 28 15 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_15_7 : Certificate := {
  objectiveScale := 300767040000
  eta := 107176830868800
  rows := #[⟨.count 2, 19621791050400⟩, ⟨.count 3, 3664094464800⟩, ⟨.count 4, 919745608320⟩, ⟨.count 5, 358414056000⟩, ⟨.count 6, 300516400800⟩, ⟨.path 7, 58017960000⟩, ⟨.path 8, 68173862400⟩, ⟨.privateRow 5 5, 26896371040⟩, ⟨.privateRow 5 6, 25658770368⟩, ⟨.privateRow 6 2, 14560571025⟩, ⟨.privateRow 6 3, 11618917200⟩, ⟨.privateRow 7 0, 12494165200⟩, ⟨.privateRow 8 0, 8529565275⟩, ⟨.hall 3 9, 5551658280⟩, ⟨.hall 4 9, 4992732864⟩]
  caps := #[0, 0, 0, 4160469600, 1453667040, 1170672832, 895882725, 0, 0, 0, 0, 0, 0, 0] }

theorem case_28_15_7_checked :
    (Witness.linear .positive case_28_15_7).check 28 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_15_8 : Certificate := {
  objectiveScale := 12096000
  eta := 6487477920
  rows := #[⟨.count 2, 1481911200⟩, ⟨.count 3, 326818800⟩, ⟨.count 4, 83825280⟩, ⟨.count 5, 28052640⟩, ⟨.count 6, 12058200⟩, ⟨.count 7, 12058200⟩, ⟨.path 9, 3888000⟩, ⟨.privateRow 8 0, 405405⟩, ⟨.privateRow 9 0, 554400⟩, ⟨.hall 6 3, 114675⟩, ⟨.hall 7 3, 47817⟩, ⟨.hall 5 5, 196504⟩, ⟨.hall 4 7, 214704⟩]
  caps := #[0, 0, 712800, 0, 0, 27360, 37800, 37800, 0, 7200, 0, 0, 0, 0] }

theorem case_28_15_8_checked :
    (Witness.linear .positive case_28_15_8).check 28 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_15_9 : Certificate := {
  objectiveScale := 1600062750000
  eta := 517164601753800
  rows := #[⟨.count 2, 141636274579800⟩, ⟨.count 3, 41047369763400⟩, ⟨.count 4, 13515794051760⟩, ⟨.count 5, 5214924514800⟩, ⟨.count 6, 2372253033150⟩, ⟨.count 7, 1740548259450⟩, ⟨.count 8, 1209647439000⟩, ⟨.count 10, 1612863252000⟩, ⟨.path 7, 533350818000⟩, ⟨.privateRow 5 6, 41217616440⟩, ⟨.privateRow 6 4, 36961449525⟩, ⟨.privateRow 6 5, 623192439870⟩, ⟨.privateRow 7 3, 407375976150⟩, ⟨.privateRow 7 4, 710043845940⟩, ⟨.privateRow 8 1, 266730460425⟩, ⟨.privateRow 8 2, 127311659475⟩, ⟨.privateRow 9 0, 123652849320⟩, ⟨.hall 5 6, 54007451355⟩, ⟨.hall 5 7, 45175104975⟩, ⟨.hall 4 8, 288621064368⟩, ⟨.hall 3 10, 1364213500650⟩, ⟨.hall 2 12, 10895098044600⟩, ⟨.assumptionRow 9, 1205864179520⟩]
  caps := #[0, 145241948280, 0, 0, 9844794960, 2710181760, 7190728545, 6368373440, 0, 0, 0, 0, 0, 0] }

theorem case_28_15_9_checked :
    (Witness.linear .conditional case_28_15_9).check 28 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_16_1_checked :
    (Witness.rising).check 28 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_16_2_checked :
    (Witness.rising).check 28 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_16_3_checked :
    (Witness.rising).check 28 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_16_4_checked :
    (Witness.rising).check 28 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_16_5_checked :
    (Witness.rising).check 28 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_16_6_checked :
    (Witness.rising).check 28 16 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_16_7 : Certificate := {
  objectiveScale := 1708560000
  eta := 903021799680
  rows := #[⟨.count 2, 151236605520⟩, ⟨.count 3, 27339864552⟩, ⟨.count 4, 6515308800⟩, ⟨.count 5, 2219277060⟩, ⟨.count 6, 1710268560⟩, ⟨.path 7, 515269755⟩, ⟨.path 8, 271205424⟩, ⟨.privateRow 3 13, 1539241704⟩, ⟨.privateRow 7 2, 24723270⟩, ⟨.privateRow 8 0, 30314284⟩, ⟨.hall 6 2, 5558696⟩, ⟨.hall 5 3, 370188⟩, ⟨.hall 4 6, 3972176⟩, ⟨.hall 5 6, 2132988⟩]
  caps := #[0, 573107535, 8532216, 0, 0, 4552695, 3097710, 11596211, 0, 0, 0, 0, 0] }

theorem case_28_16_7_checked :
    (Witness.linear .positive case_28_16_7).check 28 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_16_8 : Certificate := {
  objectiveScale := 20800
  eta := 14864850
  rows := #[⟨.count 2, 3659370⟩, ⟨.count 3, 873873⟩, ⟨.count 4, 242528⟩, ⟨.count 5, 69355⟩, ⟨.count 6, 27885⟩, ⟨.count 7, 20735⟩, ⟨.path 8, 6933⟩]
  caps := #[0, 6006, 1122, 0, 127, 0, 0, 65, 0, 0, 0, 0, 0] }

theorem case_28_16_8_checked :
    (Witness.linear .positive case_28_16_8).check 28 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_16_9 : Certificate := {
  objectiveScale := 53985750000
  eta := 32687507853000
  rows := #[⟨.count 2, 7798824633600⟩, ⟨.count 3, 2270381513400⟩, ⟨.count 4, 713752079040⟩, ⟨.count 5, 255115060200⟩, ⟨.count 6, 112999887000⟩, ⟨.count 7, 95489994600⟩, ⟨.count 10, 51308056800⟩, ⟨.path 7, 21595924350⟩, ⟨.privateRow 2 14, 162475513200⟩, ⟨.privateRow 4 9, 50381661330⟩, ⟨.privateRow 4 10, 149648499000⟩, ⟨.privateRow 5 7, 44096424372⟩, ⟨.privateRow 5 8, 82912394565⟩, ⟨.privateRow 5 9, 118483605240⟩, ⟨.privateRow 6 5, 29437658250⟩, ⟨.privateRow 6 6, 52224272100⟩, ⟨.privateRow 6 7, 33772713975⟩, ⟨.privateRow 7 3, 19298693700⟩, ⟨.privateRow 7 4, 25314689400⟩, ⟨.privateRow 8 0, 4576551980⟩, ⟨.privateRow 8 1, 9869674815⟩, ⟨.privateRow 9 0, 4275671400⟩, ⟨.hall 3 11, 8633567250⟩, ⟨.hall 4 11, 20048148120⟩, ⟨.hall 3 12, 276471490680⟩, ⟨.hall 2 13, 697545248400⟩, ⟨.assumptionRow 9, 50985581920⟩]
  caps := #[0, 0, 6672485820, 1128051540, 219367512, 0, 0, 370402110, 0, 0, 2677693200, 0, 0] }

theorem case_28_16_9_checked :
    (Witness.linear .conditional case_28_16_9).check 28 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_16_10 : Certificate := {
  objectiveScale := 86732704800000
  eta := 136703405739700800
  rows := #[⟨.count 2, 24557498037072000⟩, ⟨.count 3, 4450116310960320⟩, ⟨.count 4, 668096242894080⟩, ⟨.count 5, 23771988840600⟩, ⟨.count 11, 68215272325200⟩, ⟨.path 4, 548216476647840⟩, ⟨.path 5, 23954765234400⟩, ⟨.privateRow 2 14, 2567374794784800⟩, ⟨.privateRow 3 11, 696209203609920⟩, ⟨.privateRow 4 8, 110550083756112⟩, ⟨.privateRow 4 9, 344590481715480⟩, ⟨.privateRow 4 10, 475439776812000⟩, ⟨.privateRow 5 5, 7855091964720⟩, ⟨.privateRow 5 6, 71005897102140⟩, ⟨.privateRow 5 7, 154455913579968⟩, ⟨.privateRow 5 8, 237926601352440⟩, ⟨.privateRow 5 9, 330051671149200⟩, ⟨.privateRow 6 3, 3359085379650⟩, ⟨.privateRow 6 4, 33791238795600⟩, ⟨.privateRow 6 5, 79510658327100⟩, ⟨.privateRow 6 6, 128162026792800⟩, ⟨.privateRow 6 7, 123880115759400⟩, ⟨.privateRow 7 1, 1689796308200⟩, ⟨.privateRow 7 2, 12384320273325⟩, ⟨.privateRow 7 3, 44612028747000⟩, ⟨.privateRow 7 4, 81922309368900⟩, ⟨.privateRow 7 5, 8888656696920⟩, ⟨.privateRow 8 1, 33797566742940⟩, ⟨.privateRow 8 2, 24185414733480⟩, ⟨.privateRow 9 0, 21291433483320⟩, ⟨.privateRow 10 0, 7087301020800⟩, ⟨.hall 3 11, 18389501735220⟩, ⟨.hall 4 11, 73589808932640⟩, ⟨.hall 3 12, 910745440022880⟩, ⟨.hall 2 13, 2461065279472800⟩]
  caps := #[0, 35593413055200, 6346914235200, 5517026555040, 35842334976, 182776393800, 718236773550, 339966143670, 0, 439445704320, 1338161731200, 18517432474800, 0] }

theorem case_28_16_10_checked :
    (Witness.linear .negative case_28_16_10).check 28 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_17_1_checked :
    (Witness.rising).check 28 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_17_2_checked :
    (Witness.rising).check 28 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_17_3_checked :
    (Witness.rising).check 28 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_17_4_checked :
    (Witness.rising).check 28 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_17_5_checked :
    (Witness.rising).check 28 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_17_6_checked :
    (Witness.rising).check 28 17 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_28_17_7_checked :
    (Witness.linear .positive case_28_17_7).check 28 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_17_8 : Certificate := {
  objectiveScale := 10000
  eta := 15735720
  rows := #[⟨.count 2, 3432429⟩, ⟨.count 3, 839839⟩, ⟨.count 4, 210210⟩, ⟨.count 5, 60060⟩, ⟨.count 6, 22165⟩, ⟨.count 7, 16016⟩, ⟨.path 7, 6000⟩, ⟨.privateRow 7 10, 79222⟩]
  caps := #[0, 0, 0, 161, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_28_17_8_checked :
    (Witness.linear .positive case_28_17_8).check 28 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_17_9 : Certificate := {
  objectiveScale := 2231989200000
  eta := 3898077626242800
  rows := #[⟨.count 2, 803170600071840⟩, ⟨.count 3, 185759533159200⟩, ⟨.count 4, 49886967410280⟩, ⟨.count 5, 14157666923400⟩, ⟨.count 6, 4650827781600⟩, ⟨.count 7, 2298056080320⟩, ⟨.count 8, 766018693440⟩, ⟨.path 6, 2361013855200⟩, ⟨.privateRow 3 12, 8085752875200⟩, ⟨.privateRow 3 13, 23076313139880⟩, ⟨.privateRow 4 9, 1091576638152⟩, ⟨.privateRow 4 10, 10185654814335⟩, ⟨.privateRow 4 11, 11697743797740⟩, ⟨.privateRow 4 12, 9838552593870⟩, ⟨.privateRow 5 7, 2414326774860⟩, ⟨.privateRow 5 8, 5780705354424⟩, ⟨.privateRow 5 9, 7106191272180⟩, ⟨.privateRow 6 5, 2271675334500⟩, ⟨.privateRow 6 6, 3647708064000⟩, ⟨.privateRow 6 7, 465082778160⟩, ⟨.privateRow 7 3, 1802195765370⟩, ⟨.privateRow 7 4, 529569045720⟩, ⟨.privateRow 8 1, 739420822140⟩, ⟨.privateRow 9 0, 241154033120⟩, ⟨.privateRow 10 0, 287257010040⟩, ⟨.hall 2 14, 11337076662912⟩, ⟨.assumptionRow 9, 2253695294970⟩]
  caps := #[0, 302424922800, 574154560980, 85351466340, 0, 123054375906, 0, 0, 8834957250, 362096847910, 0, 0] }

theorem case_28_17_9_checked :
    (Witness.linear .conditional case_28_17_9).check 28 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_17_10 : Certificate := {
  objectiveScale := 549097920000
  eta := 928903460284800
  rows := #[⟨.count 2, 188214843136320⟩, ⟨.count 3, 40569184656000⟩, ⟨.count 4, 8336313105120⟩, ⟨.count 5, 1486290405600⟩, ⟨.count 6, 186954768000⟩, ⟨.path 5, 1291814924400⟩, ⟨.privateRow 2 15, 19748032143840⟩, ⟨.privateRow 3 12, 5929789785920⟩, ⟨.privateRow 3 13, 8345037660960⟩, ⟨.privateRow 4 9, 868965761664⟩, ⟨.privateRow 4 10, 3463103383740⟩, ⟨.privateRow 4 11, 4435346075160⟩, ⟨.privateRow 4 12, 4977904391460⟩, ⟨.privateRow 5 7, 791753442480⟩, ⟨.privateRow 5 8, 1716992589312⟩, ⟨.privateRow 5 9, 2457987812280⟩, ⟨.privateRow 5 10, 1595347353600⟩, ⟨.privateRow 6 5, 475621832400⟩, ⟨.privateRow 6 6, 1007738131400⟩, ⟨.privateRow 6 7, 1332364313280⟩, ⟨.privateRow 7 3, 225981575820⟩, ⟨.privateRow 7 4, 706421944800⟩, ⟨.privateRow 7 5, 221229808800⟩, ⟨.privateRow 8 1, 66524738280⟩, ⟨.privateRow 8 2, 366022381725⟩, ⟨.privateRow 9 0, 142501078720⟩, ⟨.privateRow 10 0, 44168063940⟩, ⟨.hall 3 13, 20565024480⟩, ⟨.hall 2 14, 6339262273344⟩, ⟨.assumptionRow 10, 185198526240⟩]
  caps := #[0, 9854644800, 6825939120, 26957218288, 7855041096, 0, 0, 0, 16485330435, 0, 0, 549097920000] }

theorem case_28_17_10_checked :
    (Witness.linear .conditional case_28_17_10).check 28 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_18_1_checked :
    (Witness.rising).check 28 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_18_2_checked :
    (Witness.rising).check 28 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_18_3_checked :
    (Witness.rising).check 28 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_18_4_checked :
    (Witness.rising).check 28 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_18_5_checked :
    (Witness.rising).check 28 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_18_6_checked :
    (Witness.rising).check 28 18 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_28_18_7_checked :
    (Witness.linear .positive case_28_18_7).check 28 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_18_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_28_18_8_checked :
    (Witness.linear .positive case_28_18_8).check 28 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_18_9 : Certificate := {
  objectiveScale := 2852805600000
  eta := 6164795366009280
  rows := #[⟨.count 2, 1263343278637440⟩, ⟨.count 3, 283352705295660⟩, ⟨.count 4, 75674947748400⟩, ⟨.count 5, 21179466508200⟩, ⟨.count 6, 6853580173440⟩, ⟨.count 7, 2998441325880⟩, ⟨.path 5, 406436530500⟩, ⟨.path 6, 3226173350400⟩, ⟨.privateRow 2 16, 92618520954960⟩, ⟨.privateRow 3 12, 7954198517265⟩, ⟨.privateRow 3 13, 44865566505760⟩, ⟨.privateRow 3 14, 43060949041110⟩, ⟨.privateRow 4 10, 17319568229964⟩, ⟨.privateRow 4 11, 25879404300750⟩, ⟨.privateRow 4 12, 18347605255980⟩, ⟨.privateRow 5 7, 2821662472200⟩, ⟨.privateRow 5 8, 12723544673840⟩, ⟨.privateRow 5 9, 11746274908368⟩, ⟨.privateRow 6 5, 3902733154320⟩, ⟨.privateRow 6 6, 6656403759720⟩, ⟨.privateRow 7 3, 3537843469160⟩, ⟨.privateRow 8 1, 1066112471424⟩, ⟨.privateRow 9 0, 199896088392⟩, ⟨.privateRow 9 6, 166580073660⟩, ⟨.hall 2 15, 10744414751070⟩, ⟨.assumptionRow 9, 3209370639930⟩]
  caps := #[0, 0, 423896341440, 136469313000, 0, 280008776762, 0, 210929314050, 11033225658, 0, 2852805600000] }

theorem case_28_18_9_checked :
    (Witness.linear .conditional case_28_18_9).check 28 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_18_10 : Certificate := {
  objectiveScale := 1162308000000
  eta := 3973204563007680
  rows := #[⟨.count 2, 715115390109120⟩, ⟨.count 3, 132146957582640⟩, ⟨.count 4, 25489972347840⟩, ⟨.count 5, 4288219135200⟩, ⟨.count 6, 598356158400⟩, ⟨.path 4, 3021480221760⟩, ⟨.path 5, 2955494341800⟩, ⟨.privateRow 2 16, 59476602144960⟩, ⟨.privateRow 3 12, 3952890371430⟩, ⟨.privateRow 3 13, 24642301123440⟩, ⟨.privateRow 3 14, 26980876442520⟩, ⟨.privateRow 4 10, 7679901293064⟩, ⟨.privateRow 4 11, 13810808081070⟩, ⟨.privateRow 4 12, 14849205330960⟩, ⟨.privateRow 4 13, 3575178046440⟩, ⟨.privateRow 5 7, 765041088240⟩, ⟨.privateRow 5 8, 5272182595680⟩, ⟨.privateRow 5 9, 7748712251280⟩, ⟨.privateRow 5 10, 4722027350040⟩, ⟨.privateRow 6 5, 766643827950⟩, ⟨.privateRow 6 6, 3424876678080⟩, ⟨.privateRow 6 7, 3590136950400⟩, ⟨.privateRow 7 3, 553479446520⟩, ⟨.privateRow 7 4, 2428952030505⟩, ⟨.privateRow 8 1, 345550681476⟩, ⟨.privateRow 8 2, 717473356600⟩, ⟨.privateRow 9 0, 335079448704⟩, ⟨.privateRow 10 0, 139616436960⟩, ⟨.hall 2 15, 10017479351880⟩, ⟨.assumptionRow 10, 623043580320⟩]
  caps := #[0, 0, 0, 0, 0, 88608525720, 24687421920, 0, 207195736132, 178000496352, 0] }

theorem case_28_18_10_checked :
    (Witness.linear .conditional case_28_18_10).check 28 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_18_11 : Certificate := {
  objectiveScale := 85136940000
  eta := 438723252087120
  rows := #[⟨.count 2, 74605841069760⟩, ⟨.count 3, 13343342332320⟩, ⟨.count 4, 2281864590720⟩, ⟨.count 5, 336250371600⟩, ⟨.path 3, 1115366452200⟩, ⟨.path 5, 337857577200⟩, ⟨.privateRow 3 13, 2551251382680⟩, ⟨.privateRow 4 11, 2247514876035⟩, ⟨.privateRow 5 11, 4581121442040⟩, ⟨.privateRow 6 5, 11594840400⟩, ⟨.privateRow 7 3, 193247340⟩, ⟨.hall 8 2, 360728368⟩, ⟨.hall 6 4, 8538018840⟩, ⟨.hall 7 4, 2717760318⟩, ⟨.hall 9 4, 2318968080⟩, ⟨.hall 8 5, 7729893600⟩, ⟨.hall 7 6, 4181169720⟩, ⟨.hall 5 7, 5819717970⟩, ⟨.hall 3 12, 52676251848⟩, ⟨.hall 2 14, 410553973830⟩]
  caps := #[0, 123051080880, 13274220960, 1057326270, 0, 6245141760, 140543520, 0, 721456736, 0, 418387248000] }

theorem case_28_18_11_checked :
    (Witness.linear .negative case_28_18_11).check 28 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_19_1_checked :
    (Witness.rising).check 28 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_19_2_checked :
    (Witness.rising).check 28 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_19_3_checked :
    (Witness.rising).check 28 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_19_4_checked :
    (Witness.rising).check 28 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_19_5_checked :
    (Witness.rising).check 28 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_19_6_checked :
    (Witness.rising).check 28 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_19_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_28_19_7_checked :
    (Witness.linear .positive case_28_19_7).check 28 19 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_28_19_8_checked :
    (Witness.linear .positive case_28_19_8).check 28 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_19_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_28_19_9_checked :
    (Witness.linear .positive case_28_19_9).check 28 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_19_10 : Certificate := {
  objectiveScale := 44220960000
  eta := 322339047750720
  rows := #[⟨.count 2, 47474406579600⟩, ⟨.count 3, 7161473919600⟩, ⟨.count 4, 967510383840⟩, ⟨.count 6, 28456187760⟩, ⟨.path 4, 771709498560⟩, ⟨.privateRow 2 16, 1576947071700⟩, ⟨.privateRow 2 17, 3142827848160⟩, ⟨.privateRow 3 13, 1277366650560⟩, ⟨.privateRow 3 14, 1912888177200⟩, ⟨.privateRow 3 15, 1225196973000⟩, ⟨.privateRow 4 9, 19648320120⟩, ⟨.privateRow 4 10, 309592783500⟩, ⟨.privateRow 4 11, 940635095400⟩, ⟨.privateRow 4 12, 964348585200⟩, ⟨.privateRow 4 13, 1053932880⟩, ⟨.privateRow 5 3, 1264719456⟩, ⟨.privateRow 5 6, 9696182496⟩, ⟨.privateRow 5 7, 42526191708⟩, ⟨.privateRow 5 8, 309494918304⟩, ⟨.privateRow 5 9, 582192522912⟩, ⟨.privateRow 5 10, 29088547488⟩, ⟨.privateRow 6 5, 60952451560⟩, ⟨.privateRow 6 6, 287526063825⟩, ⟨.privateRow 6 7, 37941583680⟩, ⟨.privateRow 7 3, 76515527088⟩, ⟨.privateRow 7 4, 66046460480⟩, ⟨.privateRow 8 1, 46277234640⟩, ⟨.privateRow 9 0, 16096429440⟩, ⟨.assumptionRow 10, 29346134580⟩]
  caps := #[0, 66465158760, 17035118100, 0, 4089172380, 5668653276, 1098031004, 0, 1680396480, 0] }

theorem case_28_19_10_checked :
    (Witness.linear .conditional case_28_19_10).check 28 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_19_11 : Certificate := {
  objectiveScale := 288
  eta := 32331
  rows := #[⟨.assumptionRow 11, 215⟩]
  caps := #[0, 0, 14773, 6045, 2544, 1282, 572, 26411, 23870, 14075] }

theorem case_28_19_11_checked :
    (Witness.linear .conditional case_28_19_11).check 28 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_19_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 132, 132, 90] }

theorem case_28_19_12_checked :
    (Witness.linear .negative case_28_19_12).check 28 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_20_1_checked :
    (Witness.rising).check 28 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_20_2_checked :
    (Witness.rising).check 28 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_20_3_checked :
    (Witness.rising).check 28 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_20_4_checked :
    (Witness.rising).check 28 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_20_5_checked :
    (Witness.rising).check 28 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_20_6_checked :
    (Witness.rising).check 28 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_20_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0] }

theorem case_28_20_7_checked :
    (Witness.linear .positive case_28_20_7).check 28 20 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_28_20_8_checked :
    (Witness.linear .positive case_28_20_8).check 28 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_28_20_9_checked :
    (Witness.linear .positive case_28_20_9).check 28 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_20_10 : Certificate := {
  objectiveScale := 214
  eta := 121121
  rows := #[⟨.assumptionRow 10, 335⟩]
  caps := #[0, 0, 40645, 14100, 5100, 1945, 819, 22126, 14866] }

theorem case_28_20_10_checked :
    (Witness.linear .conditional case_28_20_10).check 28 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_20_11 : Certificate := {
  objectiveScale := 504
  eta := 49179
  rows := #[⟨.assumptionRow 11, 359⟩]
  caps := #[0, 0, 21109, 9285, 3652, 2002, 145145, 134277, 83314] }

theorem case_28_20_11_checked :
    (Witness.linear .conditional case_28_20_11).check 28 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_20_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 429, 429, 297] }

theorem case_28_20_12_checked :
    (Witness.linear .negative case_28_20_12).check 28 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_21_1_checked :
    (Witness.rising).check 28 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_21_2_checked :
    (Witness.rising).check 28 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_21_3_checked :
    (Witness.rising).check 28 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_21_4_checked :
    (Witness.rising).check 28 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_21_5_checked :
    (Witness.rising).check 28 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_21_6_checked :
    (Witness.rising).check 28 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_21_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_28_21_7_checked :
    (Witness.linear .positive case_28_21_7).check 28 21 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_28_21_8_checked :
    (Witness.linear .positive case_28_21_8).check 28 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_28_21_9_checked :
    (Witness.linear .positive case_28_21_9).check 28 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_21_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_28_21_10_checked :
    (Witness.linear .positive case_28_21_10).check 28 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_21_11 : Certificate := {
  objectiveScale := 203
  eta := 61880
  rows := #[⟨.assumptionRow 11, 191⟩]
  caps := #[0, 0, 22165, 9185, 3687, 1456, 93548, 81536] }

theorem case_28_21_11_checked :
    (Witness.linear .conditional case_28_21_11).check 28 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_21_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 1430, 1430, 1001] }

theorem case_28_21_12_checked :
    (Witness.linear .negative case_28_21_12).check 28 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_21_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 429] }

theorem case_28_21_13_checked :
    (Witness.linear .negative case_28_21_13).check 28 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_22_1_checked :
    (Witness.rising).check 28 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_22_2_checked :
    (Witness.rising).check 28 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_22_3_checked :
    (Witness.rising).check 28 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_22_4_checked :
    (Witness.rising).check 28 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_22_5_checked :
    (Witness.rising).check 28 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_22_6_checked :
    (Witness.rising).check 28 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_22_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_28_22_7_checked :
    (Witness.linear .positive case_28_22_7).check 28 22 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_28_22_8_checked :
    (Witness.linear .positive case_28_22_8).check 28 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_28_22_9_checked :
    (Witness.linear .positive case_28_22_9).check 28 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_28_22_10_checked :
    (Witness.linear .positive case_28_22_10).check 28 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_22_11 : Certificate := {
  objectiveScale := 5
  eta := 22984
  rows := #[⟨.assumptionRow 11, 12⟩]
  caps := #[0, 0, 7150, 2288, 759, 264, 98] }

theorem case_28_22_11_checked :
    (Witness.linear .conditional case_28_22_11).check 28 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_22_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 4862, 4862, 3432] }

theorem case_28_22_12_checked :
    (Witness.linear .negative case_28_22_12).check 28 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_22_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 1430] }

theorem case_28_22_13_checked :
    (Witness.linear .negative case_28_22_13).check 28 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_22_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_28_22_14_checked :
    (Witness.linear .negative case_28_22_14).check 28 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_23_1_checked :
    (Witness.rising).check 28 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_23_2_checked :
    (Witness.rising).check 28 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_23_3_checked :
    (Witness.rising).check 28 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_23_4_checked :
    (Witness.rising).check 28 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_23_5_checked :
    (Witness.rising).check 28 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_23_6_checked :
    (Witness.rising).check 28 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_23_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_28_23_7_checked :
    (Witness.linear .positive case_28_23_7).check 28 23 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_28_23_8_checked :
    (Witness.linear .positive case_28_23_8).check 28 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_28_23_9_checked :
    (Witness.linear .positive case_28_23_9).check 28 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_28_23_10_checked :
    (Witness.linear .positive case_28_23_10).check 28 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_23_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_28_23_11_checked :
    (Witness.linear .positive case_28_23_11).check 28 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_23_12 : Certificate := {
  objectiveScale := 563
  eta := 101920
  rows := #[⟨.assumptionRow 12, 375⟩]
  caps := #[0, 0, 43771, 16478, 8420, 1746342] }

theorem case_28_23_12_checked :
    (Witness.linear .conditional case_28_23_12).check 28 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_23_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 4862] }

theorem case_28_23_13_checked :
    (Witness.linear .negative case_28_23_13).check 28 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_23_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_28_23_14_checked :
    (Witness.linear .negative case_28_23_14).check 28 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_24_1_checked :
    (Witness.rising).check 28 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_24_2_checked :
    (Witness.rising).check 28 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_24_3_checked :
    (Witness.rising).check 28 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_24_4_checked :
    (Witness.rising).check 28 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_24_5_checked :
    (Witness.rising).check 28 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_24_6_checked :
    (Witness.rising).check 28 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_24_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_28_24_7_checked :
    (Witness.linear .positive case_28_24_7).check 28 24 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_28_24_8_checked :
    (Witness.linear .positive case_28_24_8).check 28 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_28_24_9_checked :
    (Witness.linear .positive case_28_24_9).check 28 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_28_24_10_checked :
    (Witness.linear .positive case_28_24_10).check 28 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_28_24_11_checked :
    (Witness.linear .positive case_28_24_11).check 28 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_24_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_28_24_12_checked :
    (Witness.linear .positive case_28_24_12).check 28 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_24_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 16796] }

theorem case_28_24_13_checked :
    (Witness.linear .negative case_28_24_13).check 28 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_24_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_28_24_14_checked :
    (Witness.linear .negative case_28_24_14).check 28 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_24_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_28_24_15_checked :
    (Witness.linear .negative case_28_24_15).check 28 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_25_1_checked :
    (Witness.rising).check 28 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_25_2_checked :
    (Witness.rising).check 28 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_25_3_checked :
    (Witness.rising).check 28 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_25_4_checked :
    (Witness.rising).check 28 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_25_5_checked :
    (Witness.rising).check 28 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_25_6_checked :
    (Witness.rising).check 28 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_25_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_28_25_7_checked :
    (Witness.linear .positive case_28_25_7).check 28 25 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_28_25_8_checked :
    (Witness.linear .positive case_28_25_8).check 28 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_28_25_9_checked :
    (Witness.linear .positive case_28_25_9).check 28 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_28_25_10_checked :
    (Witness.linear .positive case_28_25_10).check 28 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_28_25_11_checked :
    (Witness.linear .positive case_28_25_11).check 28 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_25_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_28_25_12_checked :
    (Witness.linear .positive case_28_25_12).check 28 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_25_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 58786] }

theorem case_28_25_13_checked :
    (Witness.linear .negative case_28_25_13).check 28 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_25_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_28_25_14_checked :
    (Witness.linear .negative case_28_25_14).check 28 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_25_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_28_25_15_checked :
    (Witness.linear .negative case_28_25_15).check 28 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_28_25_16_checked :
    (Witness.linear .negative case_28_25_16).check 28 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_26_1_checked :
    (Witness.rising).check 28 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_26_2_checked :
    (Witness.rising).check 28 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_26_3_checked :
    (Witness.rising).check 28 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_26_4_checked :
    (Witness.rising).check 28 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_26_5_checked :
    (Witness.rising).check 28 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_26_6_checked :
    (Witness.rising).check 28 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_26_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_28_26_7_checked :
    (Witness.linear .positive case_28_26_7).check 28 26 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_28_26_8_checked :
    (Witness.linear .positive case_28_26_8).check 28 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_28_26_9_checked :
    (Witness.linear .positive case_28_26_9).check 28 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_28_26_10_checked :
    (Witness.linear .positive case_28_26_10).check 28 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_28_26_11_checked :
    (Witness.linear .positive case_28_26_11).check 28 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_28_26_12_checked :
    (Witness.linear .positive case_28_26_12).check 28 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_26_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_28_26_13_checked :
    (Witness.linear .positive case_28_26_13).check 28 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_26_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_28_26_14_checked :
    (Witness.linear .negative case_28_26_14).check 28 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_26_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_28_26_15_checked :
    (Witness.linear .negative case_28_26_15).check 28 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_26_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_28_26_16_checked :
    (Witness.linear .negative case_28_26_16).check 28 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_27_1_checked :
    (Witness.rising).check 28 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_27_2_checked :
    (Witness.rising).check 28 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_27_3_checked :
    (Witness.rising).check 28 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_27_4_checked :
    (Witness.rising).check 28 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_27_5_checked :
    (Witness.rising).check 28 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_28_27_6_checked :
    (Witness.rising).check 28 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_27_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_28_27_7_checked :
    (Witness.linear .positive case_28_27_7).check 28 27 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_28_27_8_checked :
    (Witness.linear .positive case_28_27_8).check 28 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_28_27_9_checked :
    (Witness.linear .positive case_28_27_9).check 28 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_28_27_10_checked :
    (Witness.linear .positive case_28_27_10).check 28 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_28_27_11_checked :
    (Witness.linear .positive case_28_27_11).check 28 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_28_27_12_checked :
    (Witness.linear .positive case_28_27_12).check 28 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_27_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_28_27_13_checked :
    (Witness.linear .positive case_28_27_13).check 28 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_27_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_28_27_14_checked :
    (Witness.linear .negative case_28_27_14).check 28 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_27_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_28_27_15_checked :
    (Witness.linear .negative case_28_27_15).check 28 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_27_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_28_27_16_checked :
    (Witness.linear .negative case_28_27_16).check 28 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_28_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_28_27_17_checked :
    (Witness.linear .negative case_28_27_17).check 28 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_28 (a k : ℕ) (h : Domain 28 a k) :
    ∃ w : Witness, w.check 28 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 14 ≤ a := by omega
  have haHi : a ≤ 27 := by omega
  interval_cases a

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_14_1_checked⟩

    · exact ⟨Witness.rising, case_28_14_2_checked⟩

    · exact ⟨Witness.rising, case_28_14_3_checked⟩

    · exact ⟨Witness.rising, case_28_14_4_checked⟩

    · exact ⟨Witness.rising, case_28_14_5_checked⟩

    · exact ⟨Witness.rising, case_28_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_14_7, case_28_14_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_14_8, case_28_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_15_1_checked⟩

    · exact ⟨Witness.rising, case_28_15_2_checked⟩

    · exact ⟨Witness.rising, case_28_15_3_checked⟩

    · exact ⟨Witness.rising, case_28_15_4_checked⟩

    · exact ⟨Witness.rising, case_28_15_5_checked⟩

    · exact ⟨Witness.rising, case_28_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_15_7, case_28_15_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_15_8, case_28_15_8_checked⟩

    · exact ⟨Witness.linear .conditional case_28_15_9, case_28_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_16_1_checked⟩

    · exact ⟨Witness.rising, case_28_16_2_checked⟩

    · exact ⟨Witness.rising, case_28_16_3_checked⟩

    · exact ⟨Witness.rising, case_28_16_4_checked⟩

    · exact ⟨Witness.rising, case_28_16_5_checked⟩

    · exact ⟨Witness.rising, case_28_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_16_7, case_28_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_16_8, case_28_16_8_checked⟩

    · exact ⟨Witness.linear .conditional case_28_16_9, case_28_16_9_checked⟩

    · exact ⟨Witness.linear .negative case_28_16_10, case_28_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_17_1_checked⟩

    · exact ⟨Witness.rising, case_28_17_2_checked⟩

    · exact ⟨Witness.rising, case_28_17_3_checked⟩

    · exact ⟨Witness.rising, case_28_17_4_checked⟩

    · exact ⟨Witness.rising, case_28_17_5_checked⟩

    · exact ⟨Witness.rising, case_28_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_17_7, case_28_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_17_8, case_28_17_8_checked⟩

    · exact ⟨Witness.linear .conditional case_28_17_9, case_28_17_9_checked⟩

    · exact ⟨Witness.linear .conditional case_28_17_10, case_28_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_18_1_checked⟩

    · exact ⟨Witness.rising, case_28_18_2_checked⟩

    · exact ⟨Witness.rising, case_28_18_3_checked⟩

    · exact ⟨Witness.rising, case_28_18_4_checked⟩

    · exact ⟨Witness.rising, case_28_18_5_checked⟩

    · exact ⟨Witness.rising, case_28_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_18_7, case_28_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_18_8, case_28_18_8_checked⟩

    · exact ⟨Witness.linear .conditional case_28_18_9, case_28_18_9_checked⟩

    · exact ⟨Witness.linear .conditional case_28_18_10, case_28_18_10_checked⟩

    · exact ⟨Witness.linear .negative case_28_18_11, case_28_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_19_1_checked⟩

    · exact ⟨Witness.rising, case_28_19_2_checked⟩

    · exact ⟨Witness.rising, case_28_19_3_checked⟩

    · exact ⟨Witness.rising, case_28_19_4_checked⟩

    · exact ⟨Witness.rising, case_28_19_5_checked⟩

    · exact ⟨Witness.rising, case_28_19_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_19_7, case_28_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_19_8, case_28_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_28_19_9, case_28_19_9_checked⟩

    · exact ⟨Witness.linear .conditional case_28_19_10, case_28_19_10_checked⟩

    · exact ⟨Witness.linear .conditional case_28_19_11, case_28_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_28_19_12, case_28_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_20_1_checked⟩

    · exact ⟨Witness.rising, case_28_20_2_checked⟩

    · exact ⟨Witness.rising, case_28_20_3_checked⟩

    · exact ⟨Witness.rising, case_28_20_4_checked⟩

    · exact ⟨Witness.rising, case_28_20_5_checked⟩

    · exact ⟨Witness.rising, case_28_20_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_20_7, case_28_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_20_8, case_28_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_28_20_9, case_28_20_9_checked⟩

    · exact ⟨Witness.linear .conditional case_28_20_10, case_28_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_28_20_11, case_28_20_11_checked⟩

    · exact ⟨Witness.linear .negative case_28_20_12, case_28_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_21_1_checked⟩

    · exact ⟨Witness.rising, case_28_21_2_checked⟩

    · exact ⟨Witness.rising, case_28_21_3_checked⟩

    · exact ⟨Witness.rising, case_28_21_4_checked⟩

    · exact ⟨Witness.rising, case_28_21_5_checked⟩

    · exact ⟨Witness.rising, case_28_21_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_21_7, case_28_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_21_8, case_28_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_28_21_9, case_28_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_28_21_10, case_28_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_28_21_11, case_28_21_11_checked⟩

    · exact ⟨Witness.linear .negative case_28_21_12, case_28_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_28_21_13, case_28_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_22_1_checked⟩

    · exact ⟨Witness.rising, case_28_22_2_checked⟩

    · exact ⟨Witness.rising, case_28_22_3_checked⟩

    · exact ⟨Witness.rising, case_28_22_4_checked⟩

    · exact ⟨Witness.rising, case_28_22_5_checked⟩

    · exact ⟨Witness.rising, case_28_22_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_22_7, case_28_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_22_8, case_28_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_28_22_9, case_28_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_28_22_10, case_28_22_10_checked⟩

    · exact ⟨Witness.linear .conditional case_28_22_11, case_28_22_11_checked⟩

    · exact ⟨Witness.linear .negative case_28_22_12, case_28_22_12_checked⟩

    · exact ⟨Witness.linear .negative case_28_22_13, case_28_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_28_22_14, case_28_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_23_1_checked⟩

    · exact ⟨Witness.rising, case_28_23_2_checked⟩

    · exact ⟨Witness.rising, case_28_23_3_checked⟩

    · exact ⟨Witness.rising, case_28_23_4_checked⟩

    · exact ⟨Witness.rising, case_28_23_5_checked⟩

    · exact ⟨Witness.rising, case_28_23_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_23_7, case_28_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_23_8, case_28_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_28_23_9, case_28_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_28_23_10, case_28_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_28_23_11, case_28_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_28_23_12, case_28_23_12_checked⟩

    · exact ⟨Witness.linear .negative case_28_23_13, case_28_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_28_23_14, case_28_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_24_1_checked⟩

    · exact ⟨Witness.rising, case_28_24_2_checked⟩

    · exact ⟨Witness.rising, case_28_24_3_checked⟩

    · exact ⟨Witness.rising, case_28_24_4_checked⟩

    · exact ⟨Witness.rising, case_28_24_5_checked⟩

    · exact ⟨Witness.rising, case_28_24_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_24_7, case_28_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_24_8, case_28_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_28_24_9, case_28_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_28_24_10, case_28_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_28_24_11, case_28_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_28_24_12, case_28_24_12_checked⟩

    · exact ⟨Witness.linear .negative case_28_24_13, case_28_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_28_24_14, case_28_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_28_24_15, case_28_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_25_1_checked⟩

    · exact ⟨Witness.rising, case_28_25_2_checked⟩

    · exact ⟨Witness.rising, case_28_25_3_checked⟩

    · exact ⟨Witness.rising, case_28_25_4_checked⟩

    · exact ⟨Witness.rising, case_28_25_5_checked⟩

    · exact ⟨Witness.rising, case_28_25_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_25_7, case_28_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_25_8, case_28_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_28_25_9, case_28_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_28_25_10, case_28_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_28_25_11, case_28_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_28_25_12, case_28_25_12_checked⟩

    · exact ⟨Witness.linear .negative case_28_25_13, case_28_25_13_checked⟩

    · exact ⟨Witness.linear .negative case_28_25_14, case_28_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_28_25_15, case_28_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_28_25_16, case_28_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_26_1_checked⟩

    · exact ⟨Witness.rising, case_28_26_2_checked⟩

    · exact ⟨Witness.rising, case_28_26_3_checked⟩

    · exact ⟨Witness.rising, case_28_26_4_checked⟩

    · exact ⟨Witness.rising, case_28_26_5_checked⟩

    · exact ⟨Witness.rising, case_28_26_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_26_7, case_28_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_26_8, case_28_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_28_26_9, case_28_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_28_26_10, case_28_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_28_26_11, case_28_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_28_26_12, case_28_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_28_26_13, case_28_26_13_checked⟩

    · exact ⟨Witness.linear .negative case_28_26_14, case_28_26_14_checked⟩

    · exact ⟨Witness.linear .negative case_28_26_15, case_28_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_28_26_16, case_28_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_28_27_1_checked⟩

    · exact ⟨Witness.rising, case_28_27_2_checked⟩

    · exact ⟨Witness.rising, case_28_27_3_checked⟩

    · exact ⟨Witness.rising, case_28_27_4_checked⟩

    · exact ⟨Witness.rising, case_28_27_5_checked⟩

    · exact ⟨Witness.rising, case_28_27_6_checked⟩

    · exact ⟨Witness.linear .positive case_28_27_7, case_28_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_28_27_8, case_28_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_28_27_9, case_28_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_28_27_10, case_28_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_28_27_11, case_28_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_28_27_12, case_28_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_28_27_13, case_28_27_13_checked⟩

    · exact ⟨Witness.linear .negative case_28_27_14, case_28_27_14_checked⟩

    · exact ⟨Witness.linear .negative case_28_27_15, case_28_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_28_27_16, case_28_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_28_27_17, case_28_27_17_checked⟩


#print axioms coverage_28
end ForestUnimodality.FiniteRows.FiniteData
