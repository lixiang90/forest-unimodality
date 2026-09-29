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

theorem case_26_13_1_checked :
    (Witness.rising).check 26 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_13_2_checked :
    (Witness.rising).check 26 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_13_3_checked :
    (Witness.rising).check 26 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_13_4_checked :
    (Witness.rising).check 26 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_13_5_checked :
    (Witness.rising).check 26 13 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_13_6_checked :
    (Witness.rising).check 26 13 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_13_7 : Certificate := {
  objectiveScale := 1326570000
  eta := 5253217200
  rows := #[⟨.count 2, 31577672280⟩, ⟨.count 3, 12798747360⟩, ⟨.count 4, 3540350016⟩, ⟨.count 5, 1443308160⟩, ⟨.count 6, 1326570000⟩, ⟨.path 7, 117897780⟩, ⟨.path 8, 412727512⟩, ⟨.privateRow 8 0, 68760545⟩, ⟨.hall 6 1, 60390520⟩, ⟨.hall 1 2, 230823180⟩, ⟨.hall 6 2, 11522208⟩, ⟨.hall 0 3, 2211126876⟩, ⟨.hall 5 3, 14112178⟩, ⟨.hall 1 4, 19810112⟩, ⟨.hall 4 5, 13240432⟩, ⟨.hall 5 5, 7833080⟩, ⟨.hall 3 9, 342255060⟩]
  caps := #[0, 0, 0, 0, 0, 1159620, 2280432, 0, 164242, 0, 0, 0, 0, 0] }

theorem case_26_13_7_checked :
    (Witness.linear .positive case_26_13_7).check 26 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_13_8 : Certificate := {
  objectiveScale := 2842650000
  eta := 200147575320
  rows := #[⟨.count 2, 80811991260⟩, ⟨.count 3, 26122816440⟩, ⟨.count 4, 9847394424⟩, ⟨.count 5, 4717282920⟩, ⟨.count 6, 3315098430⟩, ⟨.count 7, 3315098430⟩, ⟨.count 9, 2846288592⟩, ⟨.path 7, 927836910⟩, ⟨.hall 7 1, 93788499⟩, ⟨.hall 6 2, 35286762⟩, ⟨.hall 7 2, 65399901⟩, ⟨.hall 6 4, 136068180⟩, ⟨.hall 0 5, 161841540⟩, ⟨.hall 5 5, 218473445⟩, ⟨.hall 4 6, 220627542⟩, ⟨.hall 3 8, 649223358⟩, ⟨.hall 2 10, 2483339040⟩, ⟨.assumptionRow 8, 2388394530⟩]
  caps := #[0, 0, 0, 0, 4435452, 366870, 3951360, 1133010, 0, 0, 0, 0, 0, 0] }

theorem case_26_13_8_checked :
    (Witness.linear .conditional case_26_13_8).check 26 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_14_1_checked :
    (Witness.rising).check 26 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_14_2_checked :
    (Witness.rising).check 26 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_14_3_checked :
    (Witness.rising).check 26 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_14_4_checked :
    (Witness.rising).check 26 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_14_5_checked :
    (Witness.rising).check 26 14 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_14_6_checked :
    (Witness.rising).check 26 14 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_14_7 : Certificate := {
  objectiveScale := 26342400
  eta := 6780533760
  rows := #[⟨.count 2, 1391372640⟩, ⟨.count 3, 276496416⟩, ⟨.count 4, 75075840⟩, ⟨.count 5, 30252600⟩, ⟨.count 6, 26354160⟩, ⟨.path 7, 3950760⟩, ⟨.path 8, 6585600⟩, ⟨.privateRow 7 1, 604800⟩, ⟨.privateRow 8 0, 941976⟩, ⟨.hall 6 2, 219240⟩, ⟨.hall 5 3, 111475⟩, ⟨.hall 4 5, 153664⟩, ⟨.hall 5 6, 178360⟩]
  caps := #[0, 0, 0, 77784, 0, 40560, 65760, 0, 0, 0, 0, 0, 0] }

theorem case_26_14_7_checked :
    (Witness.linear .positive case_26_14_7).check 26 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_14_8 : Certificate := {
  objectiveScale := 808500000
  eta := 254147770800
  rows := #[⟨.count 2, 56192043600⟩, ⟨.count 3, 15451793280⟩, ⟨.count 4, 5117999040⟩, ⟨.count 5, 2180039400⟩, ⟨.count 6, 1318501800⟩, ⟨.count 7, 1229243400⟩, ⟨.count 9, 806818320⟩, ⟨.path 7, 350222400⟩, ⟨.privateRow 5 5, 67506516⟩, ⟨.privateRow 5 6, 82685295⟩, ⟨.privateRow 6 3, 90552000⟩, ⟨.privateRow 6 4, 255938760⟩, ⟨.privateRow 6 5, 118728225⟩, ⟨.privateRow 7 1, 91476000⟩, ⟨.privateRow 7 2, 80203200⟩, ⟨.privateRow 8 0, 62674920⟩, ⟨.hall 4 7, 62194132⟩, ⟨.hall 3 9, 283831128⟩, ⟨.hall 2 11, 1127372400⟩, ⟨.assumptionRow 8, 969449712⟩]
  caps := #[0, 0, 23204016, 0, 0, 1894277, 1196712, 0, 1979208, 1681680, 0, 0, 0] }

theorem case_26_14_8_checked :
    (Witness.linear .conditional case_26_14_8).check 26 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_15_1_checked :
    (Witness.rising).check 26 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_15_2_checked :
    (Witness.rising).check 26 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_15_3_checked :
    (Witness.rising).check 26 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_15_4_checked :
    (Witness.rising).check 26 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_15_5_checked :
    (Witness.rising).check 26 15 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_15_6_checked :
    (Witness.rising).check 26 15 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_15_7 : Certificate := {
  objectiveScale := 50400
  eta := 16819110
  rows := #[⟨.count 2, 3696462⟩, ⟨.count 3, 862092⟩, ⟨.count 4, 223839⟩, ⟨.count 5, 72765⟩, ⟨.count 6, 50490⟩, ⟨.path 7, 22400⟩]
  caps := #[0, 0, 0, 308, 161, 35, 0, 0, 0, 0, 0, 0] }

theorem case_26_15_7_checked :
    (Witness.linear .positive case_26_15_7).check 26 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_15_8 : Certificate := {
  objectiveScale := 191100000
  eta := 78097219200
  rows := #[⟨.count 2, 16815118320⟩, ⟨.count 3, 4712067360⟩, ⟨.count 4, 1465584120⟩, ⟨.count 5, 609008400⟩, ⟨.count 6, 354954600⟩, ⟨.count 7, 297657360⟩, ⟨.path 7, 91004368⟩, ⟨.privateRow 4 8, 159234075⟩, ⟨.privateRow 4 9, 270750480⟩, ⟨.privateRow 5 5, 6486480⟩, ⟨.privateRow 5 6, 146234088⟩, ⟨.privateRow 5 7, 170270100⟩, ⟨.privateRow 5 8, 24744720⟩, ⟨.privateRow 6 3, 20377500⟩, ⟨.privateRow 6 4, 99349250⟩, ⟨.privateRow 6 5, 30510480⟩, ⟨.privateRow 7 1, 28153125⟩, ⟨.privateRow 7 2, 27335880⟩, ⟨.privateRow 8 0, 25540515⟩, ⟨.privateRow 9 0, 27387360⟩, ⟨.hall 3 11, 351050700⟩, ⟨.hall 2 12, 993096720⟩, ⟨.assumptionRow 8, 263916744⟩]
  caps := #[0, 0, 3699696, 3841992, 0, 3096912, 0, 2127190, 2008461, 0, 0, 0] }

theorem case_26_15_8_checked :
    (Witness.linear .conditional case_26_15_8).check 26 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_15_9 : Certificate := {
  objectiveScale := 50149602720000
  eta := 30808305139772160
  rows := #[⟨.count 2, 6570430439725152⟩, ⟨.count 3, 1607826352964832⟩, ⟨.count 4, 394426625392800⟩, ⟨.count 5, 100399504645440⟩, ⟨.count 6, 36369208315440⟩, ⟨.count 8, 21514179566880⟩, ⟨.count 10, 53785448917200⟩, ⟨.path 5, 57574013777280⟩, ⟨.path 6, 7059947534640⟩, ⟨.privateRow 3 10, 18964350877472⟩, ⟨.privateRow 4 8, 57909000000852⟩, ⟨.privateRow 4 9, 113576939630154⟩, ⟨.privateRow 5 6, 43079583370824⟩, ⟨.privateRow 5 7, 66745180894392⟩, ⟨.privateRow 5 8, 71662707652536⟩, ⟨.privateRow 6 4, 23897529485830⟩, ⟨.privateRow 6 5, 45444435648612⟩, ⟨.privateRow 6 6, 14268084365535⟩, ⟨.privateRow 7 1, 1575145289718⟩, ⟨.privateRow 7 2, 8920334997288⟩, ⟨.privateRow 7 3, 24322975232556⟩, ⟨.privateRow 8 1, 13036568332788⟩, ⟨.privateRow 9 0, 4166237947872⟩, ⟨.hall 3 11, 222492473687484⟩, ⟨.hall 2 12, 466030228156416⟩, ⟨.assumptionRow 9, 21544060371834⟩]
  caps := #[0, 96331741506, 0, 0, 69557607336, 286091698788, 110526039624, 372804300084, 29880804954, 60866095206, 0, 0] }

theorem case_26_15_9_checked :
    (Witness.linear .conditional case_26_15_9).check 26 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_16_1_checked :
    (Witness.rising).check 26 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_16_2_checked :
    (Witness.rising).check 26 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_16_3_checked :
    (Witness.rising).check 26 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_16_4_checked :
    (Witness.rising).check 26 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_16_5_checked :
    (Witness.rising).check 26 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_16_6_checked :
    (Witness.rising).check 26 16 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_16_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_26_16_7_checked :
    (Witness.linear .positive case_26_16_7).check 26 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_16_8 : Certificate := {
  objectiveScale := 43365000
  eta := 33486453000
  rows := #[⟨.count 2, 8585761184⟩, ⟨.count 3, 2185301118⟩, ⟨.count 4, 606654048⟩, ⟨.count 5, 191351160⟩, ⟨.count 6, 69453384⟩, ⟨.count 7, 42168126⟩, ⟨.path 6, 26016705⟩]
  caps := #[0, 0, 0, 102102, 421527, 0, 0, 1196874, 0, 0, 0] }

theorem case_26_16_8_checked :
    (Witness.linear .positive case_26_16_8).check 26 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_16_9 : Certificate := {
  objectiveScale := 245287000000
  eta := 201369716634240
  rows := #[⟨.count 2, 40923055145280⟩, ⟨.count 3, 9444304983960⟩, ⟨.count 4, 2133054997920⟩, ⟨.count 5, 495381625200⟩, ⟨.count 6, 143757804960⟩, ⟨.path 4, 194963186880⟩, ⟨.path 5, 314765035200⟩, ⟨.privateRow 2 14, 3753244313280⟩, ⟨.privateRow 3 11, 1615224706480⟩, ⟨.privateRow 3 12, 1784830855500⟩, ⟨.privateRow 4 8, 309662082576⟩, ⟨.privateRow 4 9, 960166150020⟩, ⟨.privateRow 4 10, 1037387403360⟩, ⟨.privateRow 4 11, 327340407240⟩, ⟨.privateRow 5 6, 300358837240⟩, ⟨.privateRow 5 7, 534364597536⟩, ⟨.privateRow 5 8, 409256453760⟩, ⟨.privateRow 6 4, 210548754240⟩, ⟨.privateRow 6 5, 314497179920⟩, ⟨.privateRow 7 2, 131130430200⟩, ⟨.privateRow 7 3, 73405288440⟩, ⟨.privateRow 8 0, 40040649880⟩, ⟨.privateRow 8 1, 28613954985⟩, ⟨.privateRow 9 0, 20398066920⟩, ⟨.hall 2 13, 797791061760⟩, ⟨.assumptionRow 9, 141952492640⟩]
  caps := #[0, 42015967840, 5842525920, 0, 3489233748, 138343744, 0, 0, 4803945895, 24293224480, 245287000000] }

theorem case_26_16_9_checked :
    (Witness.linear .conditional case_26_16_9).check 26 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_16_10 : Certificate := {
  objectiveScale := 1734600000
  eta := 1042098417360
  rows := #[⟨.count 2, 267097871040⟩, ⟨.count 3, 69726236580⟩, ⟨.count 4, 19092593520⟩, ⟨.count 5, 5563357800⟩, ⟨.count 6, 1403241840⟩, ⟨.path 6, 1387643400⟩, ⟨.privateRow 3 11, 6523657140⟩, ⟨.privateRow 4 9, 826530705⟩, ⟨.privateRow 5 6, 24804780⟩, ⟨.privateRow 5 7, 2306135832⟩, ⟨.privateRow 5 10, 8575366800⟩, ⟨.privateRow 6 4, 78970320⟩, ⟨.privateRow 6 6, 6182768592⟩, ⟨.privateRow 7 7, 5471225760⟩, ⟨.privateRow 9 1, 70870800⟩, ⟨.privateRow 10 0, 127567440⟩, ⟨.hall 6 3, 39510471⟩, ⟨.hall 7 3, 128748620⟩, ⟨.hall 8 3, 72642570⟩, ⟨.hall 4 7, 40310452⟩, ⟨.hall 3 10, 626624250⟩, ⟨.hall 2 12, 2515368240⟩]
  caps := #[0, 0, 18450960, 17880720, 0, 0, 0, 0, 17577280, 9044700, 891386160] }

theorem case_26_16_10_checked :
    (Witness.linear .negative case_26_16_10).check 26 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_17_1_checked :
    (Witness.rising).check 26 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_17_2_checked :
    (Witness.rising).check 26 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_17_3_checked :
    (Witness.rising).check 26 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_17_4_checked :
    (Witness.rising).check 26 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_17_5_checked :
    (Witness.rising).check 26 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_17_6_checked :
    (Witness.rising).check 26 17 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_26_17_7_checked :
    (Witness.linear .positive case_26_17_7).check 26 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_17_8 : Certificate := {
  objectiveScale := 2
  eta := 594
  rows := #[⟨.assumptionRow 8, 7⟩]
  caps := #[0, 0, 198, 70, 27, 12, 7, 7, 9, 2] }

theorem case_26_17_8_checked :
    (Witness.linear .conditional case_26_17_8).check 26 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_17_9 : Certificate := {
  objectiveScale := 8944824000000
  eta := 18625629907684800
  rows := #[⟨.count 2, 3172320294343200⟩, ⟨.count 3, 568116631882800⟩, ⟨.count 4, 92863373803200⟩, ⟨.count 5, 13814386185600⟩, ⟨.count 6, 6331593668400⟩, ⟨.path 4, 58453521654528⟩, ⟨.path 5, 3530396469600⟩, ⟨.privateRow 2 15, 184671481995000⟩, ⟨.privateRow 3 11, 49069850930100⟩, ⟨.privateRow 3 12, 107701047854400⟩, ⟨.privateRow 3 13, 85764314235600⟩, ⟨.privateRow 4 8, 12247476641400⟩, ⟨.privateRow 4 9, 51688828311120⟩, ⟨.privateRow 4 10, 62524487475450⟩, ⟨.privateRow 4 11, 7962458704200⟩, ⟨.privateRow 5 6, 16292204660160⟩, ⟨.privateRow 5 7, 36070897262400⟩, ⟨.privateRow 5 8, 8334679665312⟩, ⟨.privateRow 6 4, 15697075969575⟩, ⟨.privateRow 6 5, 8675105610600⟩, ⟨.privateRow 7 2, 8761902349200⟩, ⟨.privateRow 8 0, 2686130647200⟩, ⟨.privateRow 9 0, 596917921600⟩, ⟨.assumptionRow 9, 6450048694800⟩]
  caps := #[0, 0, 649281853440, 214136701548, 98844922128, 121332368400, 677199048075, 0, 0, 12588711028400] }

theorem case_26_17_9_checked :
    (Witness.linear .conditional case_26_17_9).check 26 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_17_10 : Certificate := {
  objectiveScale := 4696032600000
  eta := 13059967206686400
  rows := #[⟨.count 2, 2198597934733200⟩, ⟨.count 3, 371261628738000⟩, ⟨.count 4, 53914479418800⟩, ⟨.count 5, 2302397697600⟩, ⟨.path 4, 42484837947552⟩, ⟨.path 5, 2293197706800⟩, ⟨.privateRow 2 15, 151430615235900⟩, ⟨.privateRow 3 11, 25925957407350⟩, ⟨.privateRow 3 12, 78889098888600⟩, ⟨.privateRow 3 13, 77705922294000⟩, ⟨.privateRow 4 8, 5516161150500⟩, ⟨.privateRow 4 9, 30171003162300⟩, ⟨.privateRow 4 10, 45640237693050⟩, ⟨.privateRow 4 11, 29099748678000⟩, ⟨.privateRow 5 5, 479666187000⟩, ⟨.privateRow 5 6, 7066168171920⟩, ⟨.privateRow 5 7, 20523317254440⟩, ⟨.privateRow 5 8, 23330963335680⟩, ⟨.privateRow 6 3, 479666187000⟩, ⟨.privateRow 6 4, 6475493524500⟩, ⟨.privateRow 6 5, 14842242300600⟩, ⟨.privateRow 7 2, 7919821709800⟩, ⟨.privateRow 7 3, 731490935175⟩, ⟨.privateRow 8 0, 3256933409730⟩, ⟨.privateRow 9 0, 1193835843200⟩, ⟨.hall 2 14, 6088562800320⟩]
  caps := #[0, 0, 767011305060, 0, 36347062752, 57988415760, 154441970100, 0, 0, 6770635446400] }

theorem case_26_17_10_checked :
    (Witness.linear .negative case_26_17_10).check 26 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_18_1_checked :
    (Witness.rising).check 26 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_18_2_checked :
    (Witness.rising).check 26 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_18_3_checked :
    (Witness.rising).check 26 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_18_4_checked :
    (Witness.rising).check 26 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_18_5_checked :
    (Witness.rising).check 26 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_18_6_checked :
    (Witness.rising).check 26 18 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0] }

theorem case_26_18_7_checked :
    (Witness.linear .positive case_26_18_7).check 26 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_18_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_26_18_8_checked :
    (Witness.linear .positive case_26_18_8).check 26 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_18_9 : Certificate := {
  objectiveScale := 13
  eta := 3256
  rows := #[⟨.assumptionRow 9, 23⟩]
  caps := #[0, 0, 1095, 384, 142, 63, 33, 418, 248] }

theorem case_26_18_9_checked :
    (Witness.linear .conditional case_26_18_9).check 26 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_18_10 : Certificate := {
  objectiveScale := 288
  eta := 14773
  rows := #[⟨.assumptionRow 10, 215⟩]
  caps := #[0, 0, 6045, 2544, 1282, 572, 26411, 23870, 14075] }

theorem case_26_18_10_checked :
    (Witness.linear .conditional case_26_18_10).check 26 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_18_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 132, 132, 90] }

theorem case_26_18_11_checked :
    (Witness.linear .negative case_26_18_11).check 26 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_19_1_checked :
    (Witness.rising).check 26 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_19_2_checked :
    (Witness.rising).check 26 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_19_3_checked :
    (Witness.rising).check 26 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_19_4_checked :
    (Witness.rising).check 26 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_19_5_checked :
    (Witness.rising).check 26 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_19_6_checked :
    (Witness.rising).check 26 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_19_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_26_19_7_checked :
    (Witness.linear .positive case_26_19_7).check 26 19 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_26_19_8_checked :
    (Witness.linear .positive case_26_19_8).check 26 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_19_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_26_19_9_checked :
    (Witness.linear .positive case_26_19_9).check 26 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_19_10 : Certificate := {
  objectiveScale := 505
  eta := 71071
  rows := #[⟨.assumptionRow 10, 503⟩]
  caps := #[0, 0, 27445, 10509, 4012, 2002, 73073, 61413] }

theorem case_26_19_10_checked :
    (Witness.linear .conditional case_26_19_10).check 26 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_19_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 429, 429, 297] }

theorem case_26_19_11_checked :
    (Witness.linear .negative case_26_19_11).check 26 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_19_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 132] }

theorem case_26_19_12_checked :
    (Witness.linear .negative case_26_19_12).check 26 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_20_1_checked :
    (Witness.rising).check 26 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_20_2_checked :
    (Witness.rising).check 26 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_20_3_checked :
    (Witness.rising).check 26 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_20_4_checked :
    (Witness.rising).check 26 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_20_5_checked :
    (Witness.rising).check 26 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_20_6_checked :
    (Witness.rising).check 26 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_20_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_26_20_7_checked :
    (Witness.linear .positive case_26_20_7).check 26 20 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_26_20_8_checked :
    (Witness.linear .positive case_26_20_8).check 26 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_26_20_9_checked :
    (Witness.linear .positive case_26_20_9).check 26 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_20_10 : Certificate := {
  objectiveScale := 3
  eta := 4004
  rows := #[⟨.assumptionRow 10, 7⟩]
  caps := #[0, 0, 1287, 429, 150, 56, 23] }

theorem case_26_20_10_checked :
    (Witness.linear .conditional case_26_20_10).check 26 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_20_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 1430, 1430, 1001] }

theorem case_26_20_11_checked :
    (Witness.linear .negative case_26_20_11).check 26 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_20_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 429] }

theorem case_26_20_12_checked :
    (Witness.linear .negative case_26_20_12).check 26 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_21_1_checked :
    (Witness.rising).check 26 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_21_2_checked :
    (Witness.rising).check 26 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_21_3_checked :
    (Witness.rising).check 26 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_21_4_checked :
    (Witness.rising).check 26 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_21_5_checked :
    (Witness.rising).check 26 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_21_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1] }

theorem case_26_21_6_checked :
    (Witness.linear .positive case_26_21_6).check 26 21 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_21_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_26_21_7_checked :
    (Witness.linear .positive case_26_21_7).check 26 21 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_26_21_8_checked :
    (Witness.linear .positive case_26_21_8).check 26 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_26_21_9_checked :
    (Witness.linear .positive case_26_21_9).check 26 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_21_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_26_21_10_checked :
    (Witness.linear .positive case_26_21_10).check 26 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_21_11 : Certificate := {
  objectiveScale := 922
  eta := 79781
  rows := #[⟨.assumptionRow 11, 633⟩]
  caps := #[0, 0, 32087, 15205, 6206, 860184] }

theorem case_26_21_11_checked :
    (Witness.linear .conditional case_26_21_11).check 26 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_21_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 1430] }

theorem case_26_21_12_checked :
    (Witness.linear .negative case_26_21_12).check 26 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_21_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_26_21_13_checked :
    (Witness.linear .negative case_26_21_13).check 26 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_22_1_checked :
    (Witness.rising).check 26 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_22_2_checked :
    (Witness.rising).check 26 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_22_3_checked :
    (Witness.rising).check 26 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_22_4_checked :
    (Witness.rising).check 26 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_22_5_checked :
    (Witness.rising).check 26 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_22_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1] }

theorem case_26_22_6_checked :
    (Witness.linear .positive case_26_22_6).check 26 22 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_22_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_26_22_7_checked :
    (Witness.linear .positive case_26_22_7).check 26 22 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_26_22_8_checked :
    (Witness.linear .positive case_26_22_8).check 26 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_26_22_9_checked :
    (Witness.linear .positive case_26_22_9).check 26 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_26_22_10_checked :
    (Witness.linear .positive case_26_22_10).check 26 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_22_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_26_22_11_checked :
    (Witness.linear .positive case_26_22_11).check 26 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_22_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 4862] }

theorem case_26_22_12_checked :
    (Witness.linear .negative case_26_22_12).check 26 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_22_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_26_22_13_checked :
    (Witness.linear .negative case_26_22_13).check 26 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_22_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_26_22_14_checked :
    (Witness.linear .negative case_26_22_14).check 26 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_23_1_checked :
    (Witness.rising).check 26 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_23_2_checked :
    (Witness.rising).check 26 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_23_3_checked :
    (Witness.rising).check 26 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_23_4_checked :
    (Witness.rising).check 26 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_23_5_checked :
    (Witness.rising).check 26 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_23_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_26_23_6_checked :
    (Witness.linear .positive case_26_23_6).check 26 23 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_23_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_26_23_7_checked :
    (Witness.linear .positive case_26_23_7).check 26 23 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_26_23_8_checked :
    (Witness.linear .positive case_26_23_8).check 26 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_26_23_9_checked :
    (Witness.linear .positive case_26_23_9).check 26 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_26_23_10_checked :
    (Witness.linear .positive case_26_23_10).check 26 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_23_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_26_23_11_checked :
    (Witness.linear .positive case_26_23_11).check 26 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_23_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 16796] }

theorem case_26_23_12_checked :
    (Witness.linear .negative case_26_23_12).check 26 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_23_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_26_23_13_checked :
    (Witness.linear .negative case_26_23_13).check 26 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_23_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_26_23_14_checked :
    (Witness.linear .negative case_26_23_14).check 26 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_24_1_checked :
    (Witness.rising).check 26 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_24_2_checked :
    (Witness.rising).check 26 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_24_3_checked :
    (Witness.rising).check 26 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_24_4_checked :
    (Witness.rising).check 26 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_24_5_checked :
    (Witness.rising).check 26 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_24_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_26_24_6_checked :
    (Witness.linear .positive case_26_24_6).check 26 24 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_24_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_26_24_7_checked :
    (Witness.linear .positive case_26_24_7).check 26 24 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_26_24_8_checked :
    (Witness.linear .positive case_26_24_8).check 26 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_26_24_9_checked :
    (Witness.linear .positive case_26_24_9).check 26 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_26_24_10_checked :
    (Witness.linear .positive case_26_24_10).check 26 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_26_24_11_checked :
    (Witness.linear .positive case_26_24_11).check 26 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_24_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_26_24_12_checked :
    (Witness.linear .positive case_26_24_12).check 26 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_24_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_26_24_13_checked :
    (Witness.linear .negative case_26_24_13).check 26 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_24_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_26_24_14_checked :
    (Witness.linear .negative case_26_24_14).check 26 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_24_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_26_24_15_checked :
    (Witness.linear .negative case_26_24_15).check 26 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_25_1_checked :
    (Witness.rising).check 26 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_25_2_checked :
    (Witness.rising).check 26 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_25_3_checked :
    (Witness.rising).check 26 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_25_4_checked :
    (Witness.rising).check 26 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_26_25_5_checked :
    (Witness.rising).check 26 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_25_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_26_25_6_checked :
    (Witness.linear .positive case_26_25_6).check 26 25 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_25_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_26_25_7_checked :
    (Witness.linear .positive case_26_25_7).check 26 25 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_26_25_8_checked :
    (Witness.linear .positive case_26_25_8).check 26 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_26_25_9_checked :
    (Witness.linear .positive case_26_25_9).check 26 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_26_25_10_checked :
    (Witness.linear .positive case_26_25_10).check 26 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_26_25_11_checked :
    (Witness.linear .positive case_26_25_11).check 26 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_25_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_26_25_12_checked :
    (Witness.linear .positive case_26_25_12).check 26 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_25_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_26_25_13_checked :
    (Witness.linear .negative case_26_25_13).check 26 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_25_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_26_25_14_checked :
    (Witness.linear .negative case_26_25_14).check 26 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_25_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_26_25_15_checked :
    (Witness.linear .negative case_26_25_15).check 26 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_26_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_26_25_16_checked :
    (Witness.linear .negative case_26_25_16).check 26 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_26 (a k : ℕ) (h : Domain 26 a k) :
    ∃ w : Witness, w.check 26 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 13 ≤ a := by omega
  have haHi : a ≤ 25 := by omega
  interval_cases a

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_13_1_checked⟩

    · exact ⟨Witness.rising, case_26_13_2_checked⟩

    · exact ⟨Witness.rising, case_26_13_3_checked⟩

    · exact ⟨Witness.rising, case_26_13_4_checked⟩

    · exact ⟨Witness.rising, case_26_13_5_checked⟩

    · exact ⟨Witness.rising, case_26_13_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_13_7, case_26_13_7_checked⟩

    · exact ⟨Witness.linear .conditional case_26_13_8, case_26_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_14_1_checked⟩

    · exact ⟨Witness.rising, case_26_14_2_checked⟩

    · exact ⟨Witness.rising, case_26_14_3_checked⟩

    · exact ⟨Witness.rising, case_26_14_4_checked⟩

    · exact ⟨Witness.rising, case_26_14_5_checked⟩

    · exact ⟨Witness.rising, case_26_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_14_7, case_26_14_7_checked⟩

    · exact ⟨Witness.linear .conditional case_26_14_8, case_26_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_15_1_checked⟩

    · exact ⟨Witness.rising, case_26_15_2_checked⟩

    · exact ⟨Witness.rising, case_26_15_3_checked⟩

    · exact ⟨Witness.rising, case_26_15_4_checked⟩

    · exact ⟨Witness.rising, case_26_15_5_checked⟩

    · exact ⟨Witness.rising, case_26_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_15_7, case_26_15_7_checked⟩

    · exact ⟨Witness.linear .conditional case_26_15_8, case_26_15_8_checked⟩

    · exact ⟨Witness.linear .conditional case_26_15_9, case_26_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_16_1_checked⟩

    · exact ⟨Witness.rising, case_26_16_2_checked⟩

    · exact ⟨Witness.rising, case_26_16_3_checked⟩

    · exact ⟨Witness.rising, case_26_16_4_checked⟩

    · exact ⟨Witness.rising, case_26_16_5_checked⟩

    · exact ⟨Witness.rising, case_26_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_16_7, case_26_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_26_16_8, case_26_16_8_checked⟩

    · exact ⟨Witness.linear .conditional case_26_16_9, case_26_16_9_checked⟩

    · exact ⟨Witness.linear .negative case_26_16_10, case_26_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_17_1_checked⟩

    · exact ⟨Witness.rising, case_26_17_2_checked⟩

    · exact ⟨Witness.rising, case_26_17_3_checked⟩

    · exact ⟨Witness.rising, case_26_17_4_checked⟩

    · exact ⟨Witness.rising, case_26_17_5_checked⟩

    · exact ⟨Witness.rising, case_26_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_17_7, case_26_17_7_checked⟩

    · exact ⟨Witness.linear .conditional case_26_17_8, case_26_17_8_checked⟩

    · exact ⟨Witness.linear .conditional case_26_17_9, case_26_17_9_checked⟩

    · exact ⟨Witness.linear .negative case_26_17_10, case_26_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_18_1_checked⟩

    · exact ⟨Witness.rising, case_26_18_2_checked⟩

    · exact ⟨Witness.rising, case_26_18_3_checked⟩

    · exact ⟨Witness.rising, case_26_18_4_checked⟩

    · exact ⟨Witness.rising, case_26_18_5_checked⟩

    · exact ⟨Witness.rising, case_26_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_18_7, case_26_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_26_18_8, case_26_18_8_checked⟩

    · exact ⟨Witness.linear .conditional case_26_18_9, case_26_18_9_checked⟩

    · exact ⟨Witness.linear .conditional case_26_18_10, case_26_18_10_checked⟩

    · exact ⟨Witness.linear .negative case_26_18_11, case_26_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_19_1_checked⟩

    · exact ⟨Witness.rising, case_26_19_2_checked⟩

    · exact ⟨Witness.rising, case_26_19_3_checked⟩

    · exact ⟨Witness.rising, case_26_19_4_checked⟩

    · exact ⟨Witness.rising, case_26_19_5_checked⟩

    · exact ⟨Witness.rising, case_26_19_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_19_7, case_26_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_26_19_8, case_26_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_26_19_9, case_26_19_9_checked⟩

    · exact ⟨Witness.linear .conditional case_26_19_10, case_26_19_10_checked⟩

    · exact ⟨Witness.linear .negative case_26_19_11, case_26_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_26_19_12, case_26_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_20_1_checked⟩

    · exact ⟨Witness.rising, case_26_20_2_checked⟩

    · exact ⟨Witness.rising, case_26_20_3_checked⟩

    · exact ⟨Witness.rising, case_26_20_4_checked⟩

    · exact ⟨Witness.rising, case_26_20_5_checked⟩

    · exact ⟨Witness.rising, case_26_20_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_20_7, case_26_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_26_20_8, case_26_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_26_20_9, case_26_20_9_checked⟩

    · exact ⟨Witness.linear .conditional case_26_20_10, case_26_20_10_checked⟩

    · exact ⟨Witness.linear .negative case_26_20_11, case_26_20_11_checked⟩

    · exact ⟨Witness.linear .negative case_26_20_12, case_26_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_21_1_checked⟩

    · exact ⟨Witness.rising, case_26_21_2_checked⟩

    · exact ⟨Witness.rising, case_26_21_3_checked⟩

    · exact ⟨Witness.rising, case_26_21_4_checked⟩

    · exact ⟨Witness.rising, case_26_21_5_checked⟩

    · exact ⟨Witness.linear .positive case_26_21_6, case_26_21_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_21_7, case_26_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_26_21_8, case_26_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_26_21_9, case_26_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_26_21_10, case_26_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_26_21_11, case_26_21_11_checked⟩

    · exact ⟨Witness.linear .negative case_26_21_12, case_26_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_26_21_13, case_26_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_22_1_checked⟩

    · exact ⟨Witness.rising, case_26_22_2_checked⟩

    · exact ⟨Witness.rising, case_26_22_3_checked⟩

    · exact ⟨Witness.rising, case_26_22_4_checked⟩

    · exact ⟨Witness.rising, case_26_22_5_checked⟩

    · exact ⟨Witness.linear .positive case_26_22_6, case_26_22_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_22_7, case_26_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_26_22_8, case_26_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_26_22_9, case_26_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_26_22_10, case_26_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_26_22_11, case_26_22_11_checked⟩

    · exact ⟨Witness.linear .negative case_26_22_12, case_26_22_12_checked⟩

    · exact ⟨Witness.linear .negative case_26_22_13, case_26_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_26_22_14, case_26_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_23_1_checked⟩

    · exact ⟨Witness.rising, case_26_23_2_checked⟩

    · exact ⟨Witness.rising, case_26_23_3_checked⟩

    · exact ⟨Witness.rising, case_26_23_4_checked⟩

    · exact ⟨Witness.rising, case_26_23_5_checked⟩

    · exact ⟨Witness.linear .positive case_26_23_6, case_26_23_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_23_7, case_26_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_26_23_8, case_26_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_26_23_9, case_26_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_26_23_10, case_26_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_26_23_11, case_26_23_11_checked⟩

    · exact ⟨Witness.linear .negative case_26_23_12, case_26_23_12_checked⟩

    · exact ⟨Witness.linear .negative case_26_23_13, case_26_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_26_23_14, case_26_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_24_1_checked⟩

    · exact ⟨Witness.rising, case_26_24_2_checked⟩

    · exact ⟨Witness.rising, case_26_24_3_checked⟩

    · exact ⟨Witness.rising, case_26_24_4_checked⟩

    · exact ⟨Witness.rising, case_26_24_5_checked⟩

    · exact ⟨Witness.linear .positive case_26_24_6, case_26_24_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_24_7, case_26_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_26_24_8, case_26_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_26_24_9, case_26_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_26_24_10, case_26_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_26_24_11, case_26_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_26_24_12, case_26_24_12_checked⟩

    · exact ⟨Witness.linear .negative case_26_24_13, case_26_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_26_24_14, case_26_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_26_24_15, case_26_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_26_25_1_checked⟩

    · exact ⟨Witness.rising, case_26_25_2_checked⟩

    · exact ⟨Witness.rising, case_26_25_3_checked⟩

    · exact ⟨Witness.rising, case_26_25_4_checked⟩

    · exact ⟨Witness.rising, case_26_25_5_checked⟩

    · exact ⟨Witness.linear .positive case_26_25_6, case_26_25_6_checked⟩

    · exact ⟨Witness.linear .positive case_26_25_7, case_26_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_26_25_8, case_26_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_26_25_9, case_26_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_26_25_10, case_26_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_26_25_11, case_26_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_26_25_12, case_26_25_12_checked⟩

    · exact ⟨Witness.linear .negative case_26_25_13, case_26_25_13_checked⟩

    · exact ⟨Witness.linear .negative case_26_25_14, case_26_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_26_25_15, case_26_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_26_25_16, case_26_25_16_checked⟩


#print axioms coverage_26
end ForestUnimodality.FiniteRows.FiniteData
