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

theorem case_29_15_1_checked :
    (Witness.rising).check 29 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_15_2_checked :
    (Witness.rising).check 29 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_15_3_checked :
    (Witness.rising).check 29 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_15_4_checked :
    (Witness.rising).check 29 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_15_5_checked :
    (Witness.rising).check 29 15 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_15_6_checked :
    (Witness.rising).check 29 15 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_15_7 : Certificate := {
  objectiveScale := 18229680000
  eta := 7957392042600
  rows := #[⟨.count 2, 1689636120480⟩, ⟨.count 3, 269106536160⟩, ⟨.count 4, 64168473600⟩, ⟨.count 5, 22860018720⟩, ⟨.count 6, 18247909680⟩, ⟨.path 7, 4607803200⟩, ⟨.path 8, 3605223048⟩, ⟨.privateRow 7 0, 710197950⟩, ⟨.privateRow 8 0, 451184580⟩, ⟨.hall 5 3, 102650460⟩, ⟨.hall 5 5, 8753140⟩, ⟨.hall 4 6, 72658296⟩, ⟨.hall 3 10, 1107073275⟩]
  caps := #[0, 5056787736, 0, 116658528, 0, 43223040, 0, 4960914, 0, 0, 0, 0, 0, 0, 0] }

theorem case_29_15_7_checked :
    (Witness.linear .positive case_29_15_7).check 29 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_15_8 : Certificate := {
  objectiveScale := 40320000
  eta := 23070247200
  rows := #[⟨.count 2, 5766647040⟩, ⟨.count 3, 1128813840⟩, ⟨.count 4, 282078720⟩, ⟨.count 5, 94137120⟩, ⟨.count 6, 40360320⟩, ⟨.count 7, 40360320⟩, ⟨.path 9, 13439520⟩, ⟨.privateRow 8 0, 696465⟩, ⟨.privateRow 8 3, 2866248⟩, ⟨.privateRow 9 0, 1921920⟩, ⟨.privateRow 9 5, 1404480⟩, ⟨.privateRow 10 2, 5305608⟩, ⟨.hall 6 3, 354200⟩, ⟨.hall 5 5, 428208⟩, ⟨.hall 6 5, 288200⟩, ⟨.hall 7 6, 1046430⟩, ⟨.hall 4 8, 1084608⟩]
  caps := #[0, 0, 0, 105840, 158400, 0, 0, 0, 215982, 0, 0, 0, 0, 0, 0] }

theorem case_29_15_8_checked :
    (Witness.linear .positive case_29_15_8).check 29 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_15_9 : Certificate := {
  objectiveScale := 343200000
  eta := 127695007440
  rows := #[⟨.count 2, 31584833280⟩, ⟨.count 3, 9584855280⟩, ⟨.count 4, 3212969760⟩, ⟨.count 5, 1251890640⟩, ⟨.count 6, 611170560⟩, ⟨.count 7, 428828400⟩, ⟨.count 8, 429549120⟩, ⟨.count 10, 341621280⟩, ⟨.path 8, 95593680⟩, ⟨.privateRow 9 0, 25122240⟩, ⟨.hall 7 3, 12441429⟩, ⟨.hall 6 4, 6985264⟩, ⟨.hall 5 6, 19755450⟩, ⟨.hall 6 6, 17194320⟩, ⟨.hall 7 7, 5045040⟩, ⟨.hall 4 8, 49725312⟩, ⟨.hall 3 10, 201891690⟩, ⟨.hall 2 12, 1137961440⟩, ⟨.assumptionRow 9, 333789456⟩]
  caps := #[0, 34978944, 14620320, 5505552, 3531528, 193440, 0, 826280, 0, 487344, 1578720, 0, 0, 0, 0] }

theorem case_29_15_9_checked :
    (Witness.linear .conditional case_29_15_9).check 29 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_16_1_checked :
    (Witness.rising).check 29 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_16_2_checked :
    (Witness.rising).check 29 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_16_3_checked :
    (Witness.rising).check 29 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_16_4_checked :
    (Witness.rising).check 29 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_16_5_checked :
    (Witness.rising).check 29 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_16_6_checked :
    (Witness.rising).check 29 16 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_16_7 : Certificate := {
  objectiveScale := 11243912400000
  eta := 5995782555562800
  rows := #[⟨.count 2, 1024058436481080⟩, ⟨.count 3, 171721527737760⟩, ⟨.count 4, 40904453798208⟩, ⟨.count 5, 14363723293920⟩, ⟨.count 6, 11255156312400⟩, ⟨.path 7, 3066450987600⟩, ⟨.path 8, 2044518071400⟩, ⟨.privateRow 5 6, 1118369500248⟩, ⟨.privateRow 6 5, 140689453905⟩, ⟨.privateRow 6 8, 1715071438080⟩, ⟨.privateRow 7 3, 523381175460⟩, ⟨.privateRow 8 0, 227782925370⟩, ⟨.hall 5 5, 6071117780⟩, ⟨.hall 4 6, 14129849916⟩, ⟨.hall 3 10, 200141640720⟩]
  caps := #[0, 0, 0, 168794425800, 79147014408, 0, 26300924685, 18088655400, 0, 0, 0, 0, 0, 0] }

theorem case_29_16_7_checked :
    (Witness.linear .positive case_29_16_7).check 29 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_16_8 : Certificate := {
  objectiveScale := 471744000
  eta := 337491554400
  rows := #[⟨.count 2, 67426959600⟩, ⟨.count 3, 13264851600⟩, ⟨.count 4, 3321077760⟩, ⟨.count 5, 1102701600⟩, ⟨.count 6, 475675200⟩, ⟨.count 7, 470269800⟩, ⟨.path 8, 1663200⟩, ⟨.path 9, 155577240⟩, ⟨.privateRow 3 13, 64864800⟩, ⟨.privateRow 5 7, 122234112⟩, ⟨.privateRow 5 8, 125044920⟩, ⟨.privateRow 6 4, 29729700⟩, ⟨.privateRow 6 5, 92942850⟩, ⟨.privateRow 6 6, 30270240⟩, ⟨.privateRow 7 2, 53185275⟩, ⟨.privateRow 8 0, 23923900⟩, ⟨.privateRow 9 0, 19459440⟩, ⟨.hall 9 1, 38918880⟩, ⟨.hall 4 10, 25257960⟩, ⟨.hall 3 11, 90228600⟩]
  caps := #[0, 0, 19459440, 19459440, 4256280, 3016440, 0, 4154490, 0, 0, 0, 0, 0, 0] }

theorem case_29_16_8_checked :
    (Witness.linear .positive case_29_16_8).check 29 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_16_9 : Certificate := {
  objectiveScale := 1274000000
  eta := 910680170400
  rows := #[⟨.count 2, 217819602000⟩, ⟨.count 3, 57210753600⟩, ⟨.count 4, 18646467840⟩, ⟨.count 5, 6861254400⟩, ⟨.count 6, 3090087000⟩, ⟨.count 7, 1967565600⟩, ⟨.count 8, 1782580800⟩, ⟨.count 10, 1286485200⟩, ⟨.path 8, 424653600⟩, ⟨.privateRow 5 7, 330281952⟩, ⟨.privateRow 5 8, 1367205840⟩, ⟨.privateRow 6 5, 306556250⟩, ⟨.privateRow 6 6, 823182360⟩, ⟨.privateRow 6 7, 1305404100⟩, ⟨.privateRow 7 3, 225739800⟩, ⟨.privateRow 7 4, 555555000⟩, ⟨.privateRow 7 5, 211891680⟩, ⟨.privateRow 8 1, 179204025⟩, ⟨.privateRow 8 2, 141141000⟩, ⟨.privateRow 9 0, 95435340⟩, ⟨.hall 4 9, 128419200⟩, ⟨.hall 4 10, 98148960⟩, ⟨.hall 5 10, 310346400⟩, ⟨.hall 3 11, 1315106100⟩, ⟨.hall 2 13, 10801791000⟩, ⟨.assumptionRow 9, 1543476480⟩]
  caps := #[0, 145745600, 0, 0, 0, 6664000, 0, 10516920, 6345255, 0, 0, 0, 0, 0] }

theorem case_29_16_9_checked :
    (Witness.linear .conditional case_29_16_9).check 29 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_16_10 : Certificate := {
  objectiveScale := 1467062856000000
  eta := 953998993286539200
  rows := #[⟨.count 2, 245307433445474400⟩, ⟨.count 3, 65328602390251200⟩, ⟨.count 4, 20114664088559040⟩, ⟨.count 5, 6545447638329600⟩, ⟨.count 6, 2160836880602400⟩, ⟨.count 7, 1426571921174400⟩, ⟨.count 9, 553845569397120⟩, ⟨.count 11, 1384613923492800⟩, ⟨.path 6, 254384033389200⟩, ⟨.path 7, 452161753243200⟩, ⟨.privateRow 2 14, 5884609174844400⟩, ⟨.privateRow 5 7, 167272550757312⟩, ⟨.privateRow 5 8, 1902095894899200⟩, ⟨.privateRow 6 5, 93531369831900⟩, ⟨.privateRow 6 6, 923075948995200⟩, ⟨.privateRow 6 7, 2157777443271450⟩, ⟨.privateRow 7 4, 472526973890400⟩, ⟨.privateRow 7 5, 1236861831656880⟩, ⟨.privateRow 7 6, 834289828901100⟩, ⟨.privateRow 8 1, 69274402422225⟩, ⟨.privateRow 8 2, 82916995418400⟩, ⟨.privateRow 8 3, 809439705274200⟩, ⟨.privateRow 8 4, 41608347700920⟩, ⟨.privateRow 9 1, 359639980128000⟩, ⟨.privateRow 10 0, 111488393839680⟩, ⟨.hall 5 9, 564525786988800⟩, ⟨.hall 4 10, 1574187785745120⟩, ⟨.hall 3 11, 2356909831306800⟩, ⟨.hall 2 13, 22994481229434000⟩, ⟨.assumptionRow 10, 554248196647600⟩]
  caps := #[0, 0, 0, 45409499506800, 13924524804576, 0, 4344529870500, 0, 8518235587015, 1021355188320, 0, 82448932507200, 0, 0] }

theorem case_29_16_10_checked :
    (Witness.linear .conditional case_29_16_10).check 29 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_17_1_checked :
    (Witness.rising).check 29 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_17_2_checked :
    (Witness.rising).check 29 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_17_3_checked :
    (Witness.rising).check 29 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_17_4_checked :
    (Witness.rising).check 29 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_17_5_checked :
    (Witness.rising).check 29 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_17_6_checked :
    (Witness.rising).check 29 17 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_29_17_7_checked :
    (Witness.linear .positive case_29_17_7).check 29 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_17_8 : Certificate := {
  objectiveScale := 1440000
  eta := 1646364720
  rows := #[⟨.count 2, 370450080⟩, ⟨.count 3, 84612528⟩, ⟨.count 4, 20180160⟩, ⟨.count 5, 5765760⟩, ⟨.count 6, 2024880⟩, ⟨.count 7, 1441440⟩, ⟨.path 8, 576000⟩, ⟨.privateRow 7 8, 51480⟩, ⟨.privateRow 8 2, 235235⟩]
  caps := #[0, 995280, 205920, 59472, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_29_17_8_checked :
    (Witness.linear .positive case_29_17_8).check 29 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_17_9 : Certificate := {
  objectiveScale := 1274000000
  eta := 1428452625600
  rows := #[⟨.count 2, 321469948800⟩, ⟨.count 3, 86769642960⟩, ⟨.count 4, 24579434880⟩, ⟨.count 5, 8778369600⟩, ⟨.count 6, 3762158400⟩, ⟨.count 7, 2270268000⟩, ⟨.count 8, 1755673920⟩, ⟨.path 8, 504924840⟩, ⟨.privateRow 3 12, 151351200⟩, ⟨.privateRow 4 10, 2429186760⟩, ⟨.privateRow 4 11, 5009724720⟩, ⟨.privateRow 5 7, 20180160⟩, ⟨.privateRow 5 8, 2070484416⟩, ⟨.privateRow 5 9, 2796213420⟩, ⟨.privateRow 5 10, 2969006040⟩, ⟨.privateRow 6 5, 194594400⟩, ⟨.privateRow 6 6, 1203602400⟩, ⟨.privateRow 6 7, 1816214400⟩, ⟨.privateRow 6 8, 109459350⟩, ⟨.privateRow 7 3, 237161925⟩, ⟨.privateRow 7 4, 803088000⟩, ⟨.privateRow 7 5, 196396200⟩, ⟨.privateRow 8 1, 248888640⟩, ⟨.privateRow 8 2, 144729585⟩, ⟨.privateRow 9 0, 149669520⟩, ⟨.privateRow 10 0, 158918760⟩, ⟨.hall 3 13, 10002152160⟩, ⟨.hall 2 14, 21128627520⟩, ⟨.assumptionRow 9, 1767104640⟩]
  caps := #[0, 0, 189189000, 63848400, 51411360, 44773344, 24174150, 8346750, 18578280, 39070640, 2649920, 0, 0] }

theorem case_29_17_9_checked :
    (Witness.linear .conditional case_29_17_9).check 29 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_17_10 : Certificate := {
  objectiveScale := 238329000000
  eta := 382735401048000
  rows := #[⟨.count 2, 83858251276800⟩, ⟨.count 3, 20585791306080⟩, ⟨.count 4, 5085521400960⟩, ⟨.count 5, 1394701308000⟩, ⟨.count 6, 352345593600⟩, ⟨.count 7, 117448531200⟩, ⟨.count 8, 70469118720⟩, ⟨.count 9, 118916637840⟩, ⟨.count 11, 242237595600⟩, ⟨.path 6, 226873286640⟩, ⟨.privateRow 2 15, 2840786348400⟩, ⟨.privateRow 3 12, 438963885360⟩, ⟨.privateRow 4 10, 714967933680⟩, ⟨.privateRow 4 11, 1491596346240⟩, ⟨.privateRow 5 8, 478015521984⟩, ⟨.privateRow 5 9, 785987592390⟩, ⟨.privateRow 5 10, 1186719534000⟩, ⟨.privateRow 6 5, 14531259600⟩, ⟨.privateRow 6 6, 238567329000⟩, ⟨.privateRow 6 7, 464341157280⟩, ⟨.privateRow 6 8, 542806213950⟩, ⟨.privateRow 7 3, 2949321375⟩, ⟨.privateRow 7 4, 126511842600⟩, ⟨.privateRow 7 5, 280076296500⟩, ⟨.privateRow 7 6, 119650691160⟩, ⟨.privateRow 8 2, 51475489065⟩, ⟨.privateRow 8 3, 146181475440⟩, ⟨.privateRow 9 1, 65697772140⟩, ⟨.privateRow 10 0, 18167819670⟩, ⟨.hall 4 12, 441335442240⟩, ⟨.hall 3 13, 3701516298480⟩, ⟨.hall 2 14, 6976442753280⟩, ⟨.assumptionRow 10, 124887926800⟩]
  caps := #[0, 140372151920, 0, 7123116000, 0, 3146380776, 0, 1540752850, 2943319015, 5971288960, 15170876630, 0, 0] }

theorem case_29_17_10_checked :
    (Witness.linear .conditional case_29_17_10).check 29 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_18_1_checked :
    (Witness.rising).check 29 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_18_2_checked :
    (Witness.rising).check 29 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_18_3_checked :
    (Witness.rising).check 29 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_18_4_checked :
    (Witness.rising).check 29 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_18_5_checked :
    (Witness.rising).check 29 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_18_6_checked :
    (Witness.rising).check 29 18 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_29_18_7_checked :
    (Witness.linear .positive case_29_18_7).check 29 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_18_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_29_18_8_checked :
    (Witness.linear .positive case_29_18_8).check 29 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_18_9 : Certificate := {
  objectiveScale := 21983920000
  eta := 77372758182720
  rows := #[⟨.count 2, 17547507785808⟩, ⟨.count 3, 3798219016592⟩, ⟨.count 4, 922047374248⟩, ⟨.count 5, 224774590040⟩, ⟨.count 6, 59730310640⟩, ⟨.count 7, 22005903920⟩, ⟨.count 8, 22005903920⟩, ⟨.path 5, 22619236640⟩, ⟨.path 6, 15496228605⟩]
  caps := #[0, 44773448720, 1397345807, 2716718433, 575799812, 741618230, 0, 0, 0, 0, 0, 0] }

theorem case_29_18_9_checked :
    (Witness.linear .positive case_29_18_9).check 29 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_18_10 : Certificate := {
  objectiveScale := 6595176000000
  eta := 19524078075902400
  rows := #[⟨.count 2, 3759840720155520⟩, ⟨.count 3, 796965816366720⟩, ⟨.count 4, 164780208552960⟩, ⟨.count 5, 33951966048000⟩, ⟨.count 6, 5658661008000⟩, ⟨.count 7, 3564956435040⟩, ⟨.path 5, 16297583702400⟩, ⟨.path 6, 1476898233525⟩, ⟨.privateRow 2 16, 366002193997440⟩, ⟨.privateRow 3 13, 126225864885120⟩, ⟨.privateRow 3 14, 154085339247840⟩, ⟨.privateRow 4 10, 23310854022456⟩, ⟨.privateRow 4 11, 68724437942160⟩, ⟨.privateRow 4 12, 81498865167720⟩, ⟨.privateRow 4 13, 73428199905060⟩, ⟨.privateRow 5 7, 929637165600⟩, ⟨.privateRow 5 8, 19644984799440⟩, ⟨.privateRow 5 9, 34585736080896⟩, ⟨.privateRow 5 10, 44802448530840⟩, ⟨.privateRow 5 11, 12449054217600⟩, ⟨.privateRow 6 5, 1090471131750⟩, ⟨.privateRow 6 6, 12199803673200⟩, ⟨.privateRow 6 7, 21330008299600⟩, ⟨.privateRow 6 8, 12505640827680⟩, ⟨.privateRow 7 3, 282933050400⟩, ⟨.privateRow 7 4, 7950418716240⟩, ⟨.privateRow 7 5, 9991578579840⟩, ⟨.privateRow 8 2, 4995340189840⟩, ⟨.privateRow 8 3, 1373993626005⟩, ⟨.privateRow 9 0, 1874903013984⟩, ⟨.privateRow 10 0, 528141694080⟩, ⟨.hall 2 15, 100561479438420⟩, ⟨.assumptionRow 10, 4228958754720⟩]
  caps := #[0, 1382733752400, 864174331020, 0, 634538347443, 50767840905, 53189346435, 0, 0, 2585308992, 0, 6595176000000] }

theorem case_29_18_10_checked :
    (Witness.linear .conditional case_29_18_10).check 29 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_18_11 : Certificate := {
  objectiveScale := 15664320000
  eta := 36019163980800
  rows := #[⟨.count 2, 8399991600000⟩, ⟨.count 3, 1962238037760⟩, ⟨.count 4, 508479491520⟩, ⟨.count 5, 130399869600⟩, ⟨.count 6, 31199968800⟩, ⟨.count 7, 4479995520⟩, ⟨.path 6, 12935604825⟩, ⟨.path 7, 4563072360⟩, ⟨.privateRow 2 16, 1028158971840⟩, ⟨.privateRow 3 13, 222008666880⟩, ⟨.privateRow 3 14, 450612882720⟩, ⟨.privateRow 4 10, 5655994344⟩, ⟨.privateRow 4 11, 162119837880⟩, ⟨.privateRow 4 12, 237066429600⟩, ⟨.privateRow 4 13, 308979691020⟩, ⟨.privateRow 5 8, 13333320000⟩, ⟨.privateRow 5 9, 79551920448⟩, ⟨.privateRow 5 10, 132599867400⟩, ⟨.privateRow 5 11, 160799839200⟩, ⟨.privateRow 6 6, 10780941600⟩, ⟨.privateRow 6 7, 40444404000⟩, ⟨.privateRow 6 8, 75573257760⟩, ⟨.privateRow 6 9, 55766610900⟩, ⟨.privateRow 7 4, 6539993460⟩, ⟨.privateRow 7 5, 23954261760⟩, ⟨.privateRow 7 6, 46586620080⟩, ⟨.privateRow 8 2, 3266663400⟩, ⟨.privateRow 8 3, 16449983550⟩, ⟨.privateRow 8 4, 11519988480⟩, ⟨.privateRow 9 0, 2165331168⟩, ⟨.privateRow 9 1, 8877028160⟩, ⟨.privateRow 10 0, 4106662560⟩, ⟨.hall 3 14, 40618626048⟩, ⟨.hall 2 15, 350699649300⟩]
  caps := #[0, 6516553680, 2664321660, 123391917, 0, 424363797, 211832445, 181098720, 0, 227074624, 0, 93985920000] }

theorem case_29_18_11_checked :
    (Witness.linear .negative case_29_18_11).check 29 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_19_1_checked :
    (Witness.rising).check 29 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_19_2_checked :
    (Witness.rising).check 29 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_19_3_checked :
    (Witness.rising).check 29 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_19_4_checked :
    (Witness.rising).check 29 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_19_5_checked :
    (Witness.rising).check 29 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_19_6_checked :
    (Witness.rising).check 29 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_19_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_29_19_7_checked :
    (Witness.linear .positive case_29_19_7).check 29 19 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_29_19_8_checked :
    (Witness.linear .positive case_29_19_8).check 29 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_19_9 : Certificate := {
  objectiveScale := 5
  eta := 3146
  rows := #[⟨.assumptionRow 9, 14⟩]
  caps := #[0, 0, 1023, 348, 126, 50, 23, 14, 80, 31, 5] }

theorem case_29_19_9_checked :
    (Witness.linear .conditional case_29_19_9).check 29 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_19_10 : Certificate := {
  objectiveScale := 592648560000
  eta := 3543429738728880
  rows := #[⟨.count 2, 632395128324960⟩, ⟨.count 3, 118796552014140⟩, ⟨.count 4, 22712663413440⟩, ⟨.count 5, 3954941390400⟩, ⟨.count 6, 762738696720⟩, ⟨.count 7, 444930906420⟩, ⟨.path 5, 2699474778000⟩, ⟨.privateRow 2 17, 46866055476240⟩, ⟨.privateRow 3 13, 5462762795490⟩, ⟨.privateRow 3 14, 20516258462700⟩, ⟨.privateRow 3 15, 20862315834360⟩, ⟨.privateRow 4 10, 978141754590⟩, ⟨.privateRow 4 11, 7517213599896⟩, ⟨.privateRow 4 12, 11303363741670⟩, ⟨.privateRow 4 13, 10487657079900⟩, ⟨.privateRow 5 8, 1721206635720⟩, ⟨.privateRow 5 9, 4971926319360⟩, ⟨.privateRow 5 10, 6387230345496⟩, ⟨.privateRow 5 11, 473180487780⟩, ⟨.privateRow 6 5, 9416527120⟩, ⟨.privateRow 6 6, 1624350928200⟩, ⟨.privateRow 6 7, 3389949763200⟩, ⟨.privateRow 6 8, 437868511080⟩, ⟨.privateRow 7 4, 1443082781140⟩, ⟨.privateRow 7 5, 577350819045⟩, ⟨.privateRow 8 2, 667396359630⟩, ⟨.privateRow 9 0, 179770063200⟩, ⟨.hall 2 16, 5909147724480⟩, ⟨.assumptionRow 10, 464424810840⟩]
  caps := #[0, 0, 0, 223180772100, 75445618248, 9584070960, 109635280040, 19493904420, 0, 203800551240, 4276763669160] }

theorem case_29_19_10_checked :
    (Witness.linear .conditional case_29_19_10).check 29 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_19_11 : Certificate := {
  objectiveScale := 115012800000
  eta := 840717563605920
  rows := #[⟨.count 2, 102723613312320⟩, ⟨.count 3, 9792853990920⟩, ⟨.path 3, 9800444253600⟩, ⟨.privateRow 2 15, 9254631466080⟩, ⟨.privateRow 2 16, 17181181377360⟩, ⟨.privateRow 2 17, 17195161183200⟩, ⟨.privateRow 3 11, 356485048920⟩, ⟨.privateRow 3 12, 3528502994016⟩, ⟨.privateRow 3 13, 4269083208390⟩, ⟨.privateRow 3 14, 8315654507160⟩, ⟨.privateRow 3 15, 6025296317040⟩, ⟨.privateRow 4 8, 233288009955⟩, ⟨.privateRow 4 9, 816106828680⟩, ⟨.privateRow 4 10, 1292632761420⟩, ⟨.privateRow 4 11, 2698501950144⟩, ⟨.privateRow 4 12, 3356651237940⟩, ⟨.privateRow 4 13, 2318650654320⟩, ⟨.privateRow 5 5, 77687778168⟩, ⟨.privateRow 5 6, 194163970000⟩, ⟨.privateRow 5 7, 367968460860⟩, ⟨.privateRow 5 8, 914678724960⟩, ⟨.privateRow 5 9, 1436258623800⟩, ⟨.privateRow 5 10, 1392388661664⟩, ⟨.privateRow 6 2, 5991345360⟩, ⟨.privateRow 6 4, 331720821432⟩, ⟨.privateRow 6 5, 197048691840⟩, ⟨.privateRow 6 6, 640824314130⟩, ⟨.privateRow 6 7, 540932895360⟩, ⟨.privateRow 7 0, 8987018040⟩, ⟨.privateRow 7 2, 413130495960⟩, ⟨.privateRow 7 3, 197115262344⟩, ⟨.privateRow 8 0, 237656699280⟩, ⟨.privateRow 9 0, 99129532320⟩, ⟨.privateRow 10 0, 25163650512⟩, ⟨.hall 2 16, 1144699395840⟩]
  caps := #[0, 80417020320, 21626922240, 7590262680, 9917816337, 776655880, 84726096, 2904237504, 6515475120, 0, 815453403408] }

theorem case_29_19_11_checked :
    (Witness.linear .negative case_29_19_11).check 29 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_19_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 132, 132, 90, 48] }

theorem case_29_19_12_checked :
    (Witness.linear .negative case_29_19_12).check 29 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_20_1_checked :
    (Witness.rising).check 29 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_20_2_checked :
    (Witness.rising).check 29 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_20_3_checked :
    (Witness.rising).check 29 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_20_4_checked :
    (Witness.rising).check 29 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_20_5_checked :
    (Witness.rising).check 29 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_20_6_checked :
    (Witness.rising).check 29 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_20_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_29_20_7_checked :
    (Witness.linear .positive case_29_20_7).check 29 20 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_29_20_8_checked :
    (Witness.linear .positive case_29_20_8).check 29 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_29_20_9_checked :
    (Witness.linear .positive case_29_20_9).check 29 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_20_10 : Certificate := {
  objectiveScale := 214
  eta := 121121
  rows := #[⟨.assumptionRow 10, 335⟩]
  caps := #[0, 0, 40645, 14100, 5100, 1945, 819, 22126, 14866, 6066] }

theorem case_29_20_10_checked :
    (Witness.linear .conditional case_29_20_10).check 29 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_20_11 : Certificate := {
  objectiveScale := 505
  eta := 181818
  rows := #[⟨.assumptionRow 11, 503⟩]
  caps := #[0, 0, 71071, 27445, 10509, 4012, 2002, 73073, 61413, 33418] }

theorem case_29_20_11_checked :
    (Witness.linear .conditional case_29_20_11).check 29 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_20_12 : Certificate := {
  objectiveScale := 503
  eta := 12025
  rows := #[⟨.assumptionRow 12, 215⟩]
  caps := #[0, 0, 5948, 2998, 1781, 787, 572, 92807, 90266, 59345] }

theorem case_29_20_12_checked :
    (Witness.linear .conditional case_29_20_12).check 29 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_21_1_checked :
    (Witness.rising).check 29 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_21_2_checked :
    (Witness.rising).check 29 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_21_3_checked :
    (Witness.rising).check 29 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_21_4_checked :
    (Witness.rising).check 29 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_21_5_checked :
    (Witness.rising).check 29 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_21_6_checked :
    (Witness.rising).check 29 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_21_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0] }

theorem case_29_21_7_checked :
    (Witness.linear .positive case_29_21_7).check 29 21 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_29_21_8_checked :
    (Witness.linear .positive case_29_21_8).check 29 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_29_21_9_checked :
    (Witness.linear .positive case_29_21_9).check 29 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_21_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_29_21_10_checked :
    (Witness.linear .positive case_29_21_10).check 29 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_21_11 : Certificate := {
  objectiveScale := 183
  eta := 146692
  rows := #[⟨.assumptionRow 11, 223⟩]
  caps := #[0, 0, 49049, 16665, 6345, 2584, 1092, 41132, 32123] }

theorem case_29_21_11_checked :
    (Witness.linear .conditional case_29_21_11).check 29 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_21_12 : Certificate := {
  objectiveScale := 579
  eta := 12493
  rows := #[⟨.assumptionRow 12, 241⟩]
  caps := #[0, 0, 5848, 3224, 1875, 867, 345488, 338338, 227799] }

theorem case_29_21_12_checked :
    (Witness.linear .conditional case_29_21_12).check 29 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_21_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 429, 429] }

theorem case_29_21_13_checked :
    (Witness.linear .negative case_29_21_13).check 29 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_22_1_checked :
    (Witness.rising).check 29 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_22_2_checked :
    (Witness.rising).check 29 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_22_3_checked :
    (Witness.rising).check 29 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_22_4_checked :
    (Witness.rising).check 29 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_22_5_checked :
    (Witness.rising).check 29 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_22_6_checked :
    (Witness.rising).check 29 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_22_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_29_22_7_checked :
    (Witness.linear .positive case_29_22_7).check 29 22 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_29_22_8_checked :
    (Witness.linear .positive case_29_22_8).check 29 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_29_22_9_checked :
    (Witness.linear .positive case_29_22_9).check 29 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_29_22_10_checked :
    (Witness.linear .positive case_29_22_10).check 29 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_22_11 : Certificate := {
  objectiveScale := 915
  eta := 2304744
  rows := #[⟨.assumptionRow 11, 1642⟩]
  caps := #[0, 0, 727727, 236049, 79155, 27676, 10203, 4550] }

theorem case_29_22_11_checked :
    (Witness.linear .conditional case_29_22_11).check 29 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_22_12 : Certificate := {
  objectiveScale := 855
  eta := 183456
  rows := #[⟨.assumptionRow 12, 587⟩]
  caps := #[0, 0, 73983, 29755, 14100, 5755, 797680, 750204] }

theorem case_29_22_12_checked :
    (Witness.linear .conditional case_29_22_12).check 29 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_22_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 1430, 1430] }

theorem case_29_22_13_checked :
    (Witness.linear .negative case_29_22_13).check 29 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_22_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_29_22_14_checked :
    (Witness.linear .negative case_29_22_14).check 29 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_23_1_checked :
    (Witness.rising).check 29 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_23_2_checked :
    (Witness.rising).check 29 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_23_3_checked :
    (Witness.rising).check 29 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_23_4_checked :
    (Witness.rising).check 29 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_23_5_checked :
    (Witness.rising).check 29 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_23_6_checked :
    (Witness.rising).check 29 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_23_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_29_23_7_checked :
    (Witness.linear .positive case_29_23_7).check 29 23 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_29_23_8_checked :
    (Witness.linear .positive case_29_23_8).check 29 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_29_23_9_checked :
    (Witness.linear .positive case_29_23_9).check 29 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_29_23_10_checked :
    (Witness.linear .positive case_29_23_10).check 29 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_23_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_29_23_11_checked :
    (Witness.linear .positive case_29_23_11).check 29 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_23_12 : Certificate := {
  objectiveScale := 247
  eta := 178724
  rows := #[⟨.assumptionRow 12, 222⟩]
  caps := #[0, 0, 64883, 23012, 9460, 3987, 373048] }

theorem case_29_23_12_checked :
    (Witness.linear .conditional case_29_23_12).check 29 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_23_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 4862, 4862] }

theorem case_29_23_13_checked :
    (Witness.linear .negative case_29_23_13).check 29 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_23_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_29_23_14_checked :
    (Witness.linear .negative case_29_23_14).check 29 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_24_1_checked :
    (Witness.rising).check 29 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_24_2_checked :
    (Witness.rising).check 29 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_24_3_checked :
    (Witness.rising).check 29 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_24_4_checked :
    (Witness.rising).check 29 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_24_5_checked :
    (Witness.rising).check 29 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_24_6_checked :
    (Witness.rising).check 29 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_24_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_29_24_7_checked :
    (Witness.linear .positive case_29_24_7).check 29 24 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_29_24_8_checked :
    (Witness.linear .positive case_29_24_8).check 29 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_29_24_9_checked :
    (Witness.linear .positive case_29_24_9).check 29 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_29_24_10_checked :
    (Witness.linear .positive case_29_24_10).check 29 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_29_24_11_checked :
    (Witness.linear .positive case_29_24_11).check 29 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_24_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_29_24_12_checked :
    (Witness.linear .positive case_29_24_12).check 29 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_24_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 16796, 16796] }

theorem case_29_24_13_checked :
    (Witness.linear .negative case_29_24_13).check 29 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_24_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_29_24_14_checked :
    (Witness.linear .negative case_29_24_14).check 29 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_24_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_29_24_15_checked :
    (Witness.linear .negative case_29_24_15).check 29 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_25_1_checked :
    (Witness.rising).check 29 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_25_2_checked :
    (Witness.rising).check 29 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_25_3_checked :
    (Witness.rising).check 29 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_25_4_checked :
    (Witness.rising).check 29 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_25_5_checked :
    (Witness.rising).check 29 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_25_6_checked :
    (Witness.rising).check 29 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_25_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_29_25_7_checked :
    (Witness.linear .positive case_29_25_7).check 29 25 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_29_25_8_checked :
    (Witness.linear .positive case_29_25_8).check 29 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_29_25_9_checked :
    (Witness.linear .positive case_29_25_9).check 29 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_29_25_10_checked :
    (Witness.linear .positive case_29_25_10).check 29 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_29_25_11_checked :
    (Witness.linear .positive case_29_25_11).check 29 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_25_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_29_25_12_checked :
    (Witness.linear .positive case_29_25_12).check 29 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_25_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 58786, 58786] }

theorem case_29_25_13_checked :
    (Witness.linear .negative case_29_25_13).check 29 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_25_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_29_25_14_checked :
    (Witness.linear .negative case_29_25_14).check 29 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_25_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_29_25_15_checked :
    (Witness.linear .negative case_29_25_15).check 29 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_29_25_16_checked :
    (Witness.linear .negative case_29_25_16).check 29 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_26_1_checked :
    (Witness.rising).check 29 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_26_2_checked :
    (Witness.rising).check 29 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_26_3_checked :
    (Witness.rising).check 29 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_26_4_checked :
    (Witness.rising).check 29 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_26_5_checked :
    (Witness.rising).check 29 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_26_6_checked :
    (Witness.rising).check 29 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_26_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_29_26_7_checked :
    (Witness.linear .positive case_29_26_7).check 29 26 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_29_26_8_checked :
    (Witness.linear .positive case_29_26_8).check 29 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_29_26_9_checked :
    (Witness.linear .positive case_29_26_9).check 29 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_29_26_10_checked :
    (Witness.linear .positive case_29_26_10).check 29 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_29_26_11_checked :
    (Witness.linear .positive case_29_26_11).check 29 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_29_26_12_checked :
    (Witness.linear .positive case_29_26_12).check 29 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_26_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_29_26_13_checked :
    (Witness.linear .positive case_29_26_13).check 29 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_26_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_29_26_14_checked :
    (Witness.linear .negative case_29_26_14).check 29 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_26_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_29_26_15_checked :
    (Witness.linear .negative case_29_26_15).check 29 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_26_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_29_26_16_checked :
    (Witness.linear .negative case_29_26_16).check 29 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_27_1_checked :
    (Witness.rising).check 29 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_27_2_checked :
    (Witness.rising).check 29 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_27_3_checked :
    (Witness.rising).check 29 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_27_4_checked :
    (Witness.rising).check 29 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_27_5_checked :
    (Witness.rising).check 29 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_27_6_checked :
    (Witness.rising).check 29 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_27_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_29_27_7_checked :
    (Witness.linear .positive case_29_27_7).check 29 27 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_29_27_8_checked :
    (Witness.linear .positive case_29_27_8).check 29 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_29_27_9_checked :
    (Witness.linear .positive case_29_27_9).check 29 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_29_27_10_checked :
    (Witness.linear .positive case_29_27_10).check 29 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_29_27_11_checked :
    (Witness.linear .positive case_29_27_11).check 29 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_29_27_12_checked :
    (Witness.linear .positive case_29_27_12).check 29 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_27_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_29_27_13_checked :
    (Witness.linear .positive case_29_27_13).check 29 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_27_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_29_27_14_checked :
    (Witness.linear .negative case_29_27_14).check 29 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_27_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_29_27_15_checked :
    (Witness.linear .negative case_29_27_15).check 29 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_27_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_29_27_16_checked :
    (Witness.linear .negative case_29_27_16).check 29 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_29_27_17_checked :
    (Witness.linear .negative case_29_27_17).check 29 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_28_1_checked :
    (Witness.rising).check 29 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_28_2_checked :
    (Witness.rising).check 29 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_28_3_checked :
    (Witness.rising).check 29 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_28_4_checked :
    (Witness.rising).check 29 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_28_5_checked :
    (Witness.rising).check 29 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_29_28_6_checked :
    (Witness.rising).check 29 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_7_checked :
    (Witness.linear .positive case_29_28_7).check 29 28 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_8_checked :
    (Witness.linear .positive case_29_28_8).check 29 28 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_9_checked :
    (Witness.linear .positive case_29_28_9).check 29 28 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_10_checked :
    (Witness.linear .positive case_29_28_10).check 29 28 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_11_checked :
    (Witness.linear .positive case_29_28_11).check 29 28 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_12_checked :
    (Witness.linear .positive case_29_28_12).check 29 28 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_13_checked :
    (Witness.linear .positive case_29_28_13).check 29 28 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_14_checked :
    (Witness.linear .positive case_29_28_14).check 29 28 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_15_checked :
    (Witness.linear .negative case_29_28_15).check 29 28 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_16_checked :
    (Witness.linear .negative case_29_28_16).check 29 28 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_17_checked :
    (Witness.linear .negative case_29_28_17).check 29 28 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_29_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_29_28_18_checked :
    (Witness.linear .negative case_29_28_18).check 29 28 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_29 (a k : ℕ) (h : Domain 29 a k) :
    ∃ w : Witness, w.check 29 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 15 ≤ a := by omega
  have haHi : a ≤ 28 := by omega
  interval_cases a

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_15_1_checked⟩

    · exact ⟨Witness.rising, case_29_15_2_checked⟩

    · exact ⟨Witness.rising, case_29_15_3_checked⟩

    · exact ⟨Witness.rising, case_29_15_4_checked⟩

    · exact ⟨Witness.rising, case_29_15_5_checked⟩

    · exact ⟨Witness.rising, case_29_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_15_7, case_29_15_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_15_8, case_29_15_8_checked⟩

    · exact ⟨Witness.linear .conditional case_29_15_9, case_29_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_16_1_checked⟩

    · exact ⟨Witness.rising, case_29_16_2_checked⟩

    · exact ⟨Witness.rising, case_29_16_3_checked⟩

    · exact ⟨Witness.rising, case_29_16_4_checked⟩

    · exact ⟨Witness.rising, case_29_16_5_checked⟩

    · exact ⟨Witness.rising, case_29_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_16_7, case_29_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_16_8, case_29_16_8_checked⟩

    · exact ⟨Witness.linear .conditional case_29_16_9, case_29_16_9_checked⟩

    · exact ⟨Witness.linear .conditional case_29_16_10, case_29_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_17_1_checked⟩

    · exact ⟨Witness.rising, case_29_17_2_checked⟩

    · exact ⟨Witness.rising, case_29_17_3_checked⟩

    · exact ⟨Witness.rising, case_29_17_4_checked⟩

    · exact ⟨Witness.rising, case_29_17_5_checked⟩

    · exact ⟨Witness.rising, case_29_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_17_7, case_29_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_17_8, case_29_17_8_checked⟩

    · exact ⟨Witness.linear .conditional case_29_17_9, case_29_17_9_checked⟩

    · exact ⟨Witness.linear .conditional case_29_17_10, case_29_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_18_1_checked⟩

    · exact ⟨Witness.rising, case_29_18_2_checked⟩

    · exact ⟨Witness.rising, case_29_18_3_checked⟩

    · exact ⟨Witness.rising, case_29_18_4_checked⟩

    · exact ⟨Witness.rising, case_29_18_5_checked⟩

    · exact ⟨Witness.rising, case_29_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_18_7, case_29_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_18_8, case_29_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_29_18_9, case_29_18_9_checked⟩

    · exact ⟨Witness.linear .conditional case_29_18_10, case_29_18_10_checked⟩

    · exact ⟨Witness.linear .negative case_29_18_11, case_29_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_19_1_checked⟩

    · exact ⟨Witness.rising, case_29_19_2_checked⟩

    · exact ⟨Witness.rising, case_29_19_3_checked⟩

    · exact ⟨Witness.rising, case_29_19_4_checked⟩

    · exact ⟨Witness.rising, case_29_19_5_checked⟩

    · exact ⟨Witness.rising, case_29_19_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_19_7, case_29_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_19_8, case_29_19_8_checked⟩

    · exact ⟨Witness.linear .conditional case_29_19_9, case_29_19_9_checked⟩

    · exact ⟨Witness.linear .conditional case_29_19_10, case_29_19_10_checked⟩

    · exact ⟨Witness.linear .negative case_29_19_11, case_29_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_29_19_12, case_29_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_20_1_checked⟩

    · exact ⟨Witness.rising, case_29_20_2_checked⟩

    · exact ⟨Witness.rising, case_29_20_3_checked⟩

    · exact ⟨Witness.rising, case_29_20_4_checked⟩

    · exact ⟨Witness.rising, case_29_20_5_checked⟩

    · exact ⟨Witness.rising, case_29_20_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_20_7, case_29_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_20_8, case_29_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_29_20_9, case_29_20_9_checked⟩

    · exact ⟨Witness.linear .conditional case_29_20_10, case_29_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_29_20_11, case_29_20_11_checked⟩

    · exact ⟨Witness.linear .conditional case_29_20_12, case_29_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_21_1_checked⟩

    · exact ⟨Witness.rising, case_29_21_2_checked⟩

    · exact ⟨Witness.rising, case_29_21_3_checked⟩

    · exact ⟨Witness.rising, case_29_21_4_checked⟩

    · exact ⟨Witness.rising, case_29_21_5_checked⟩

    · exact ⟨Witness.rising, case_29_21_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_21_7, case_29_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_21_8, case_29_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_29_21_9, case_29_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_29_21_10, case_29_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_29_21_11, case_29_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_29_21_12, case_29_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_29_21_13, case_29_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_22_1_checked⟩

    · exact ⟨Witness.rising, case_29_22_2_checked⟩

    · exact ⟨Witness.rising, case_29_22_3_checked⟩

    · exact ⟨Witness.rising, case_29_22_4_checked⟩

    · exact ⟨Witness.rising, case_29_22_5_checked⟩

    · exact ⟨Witness.rising, case_29_22_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_22_7, case_29_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_22_8, case_29_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_29_22_9, case_29_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_29_22_10, case_29_22_10_checked⟩

    · exact ⟨Witness.linear .conditional case_29_22_11, case_29_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_29_22_12, case_29_22_12_checked⟩

    · exact ⟨Witness.linear .negative case_29_22_13, case_29_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_29_22_14, case_29_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_23_1_checked⟩

    · exact ⟨Witness.rising, case_29_23_2_checked⟩

    · exact ⟨Witness.rising, case_29_23_3_checked⟩

    · exact ⟨Witness.rising, case_29_23_4_checked⟩

    · exact ⟨Witness.rising, case_29_23_5_checked⟩

    · exact ⟨Witness.rising, case_29_23_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_23_7, case_29_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_23_8, case_29_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_29_23_9, case_29_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_29_23_10, case_29_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_29_23_11, case_29_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_29_23_12, case_29_23_12_checked⟩

    · exact ⟨Witness.linear .negative case_29_23_13, case_29_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_29_23_14, case_29_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_24_1_checked⟩

    · exact ⟨Witness.rising, case_29_24_2_checked⟩

    · exact ⟨Witness.rising, case_29_24_3_checked⟩

    · exact ⟨Witness.rising, case_29_24_4_checked⟩

    · exact ⟨Witness.rising, case_29_24_5_checked⟩

    · exact ⟨Witness.rising, case_29_24_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_24_7, case_29_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_24_8, case_29_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_29_24_9, case_29_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_29_24_10, case_29_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_29_24_11, case_29_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_29_24_12, case_29_24_12_checked⟩

    · exact ⟨Witness.linear .negative case_29_24_13, case_29_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_29_24_14, case_29_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_29_24_15, case_29_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_25_1_checked⟩

    · exact ⟨Witness.rising, case_29_25_2_checked⟩

    · exact ⟨Witness.rising, case_29_25_3_checked⟩

    · exact ⟨Witness.rising, case_29_25_4_checked⟩

    · exact ⟨Witness.rising, case_29_25_5_checked⟩

    · exact ⟨Witness.rising, case_29_25_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_25_7, case_29_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_25_8, case_29_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_29_25_9, case_29_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_29_25_10, case_29_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_29_25_11, case_29_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_29_25_12, case_29_25_12_checked⟩

    · exact ⟨Witness.linear .negative case_29_25_13, case_29_25_13_checked⟩

    · exact ⟨Witness.linear .negative case_29_25_14, case_29_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_29_25_15, case_29_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_29_25_16, case_29_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_26_1_checked⟩

    · exact ⟨Witness.rising, case_29_26_2_checked⟩

    · exact ⟨Witness.rising, case_29_26_3_checked⟩

    · exact ⟨Witness.rising, case_29_26_4_checked⟩

    · exact ⟨Witness.rising, case_29_26_5_checked⟩

    · exact ⟨Witness.rising, case_29_26_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_26_7, case_29_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_26_8, case_29_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_29_26_9, case_29_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_29_26_10, case_29_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_29_26_11, case_29_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_29_26_12, case_29_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_29_26_13, case_29_26_13_checked⟩

    · exact ⟨Witness.linear .negative case_29_26_14, case_29_26_14_checked⟩

    · exact ⟨Witness.linear .negative case_29_26_15, case_29_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_29_26_16, case_29_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_27_1_checked⟩

    · exact ⟨Witness.rising, case_29_27_2_checked⟩

    · exact ⟨Witness.rising, case_29_27_3_checked⟩

    · exact ⟨Witness.rising, case_29_27_4_checked⟩

    · exact ⟨Witness.rising, case_29_27_5_checked⟩

    · exact ⟨Witness.rising, case_29_27_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_27_7, case_29_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_27_8, case_29_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_29_27_9, case_29_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_29_27_10, case_29_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_29_27_11, case_29_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_29_27_12, case_29_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_29_27_13, case_29_27_13_checked⟩

    · exact ⟨Witness.linear .negative case_29_27_14, case_29_27_14_checked⟩

    · exact ⟨Witness.linear .negative case_29_27_15, case_29_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_29_27_16, case_29_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_29_27_17, case_29_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_29_28_1_checked⟩

    · exact ⟨Witness.rising, case_29_28_2_checked⟩

    · exact ⟨Witness.rising, case_29_28_3_checked⟩

    · exact ⟨Witness.rising, case_29_28_4_checked⟩

    · exact ⟨Witness.rising, case_29_28_5_checked⟩

    · exact ⟨Witness.rising, case_29_28_6_checked⟩

    · exact ⟨Witness.linear .positive case_29_28_7, case_29_28_7_checked⟩

    · exact ⟨Witness.linear .positive case_29_28_8, case_29_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_29_28_9, case_29_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_29_28_10, case_29_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_29_28_11, case_29_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_29_28_12, case_29_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_29_28_13, case_29_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_29_28_14, case_29_28_14_checked⟩

    · exact ⟨Witness.linear .negative case_29_28_15, case_29_28_15_checked⟩

    · exact ⟨Witness.linear .negative case_29_28_16, case_29_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_29_28_17, case_29_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_29_28_18, case_29_28_18_checked⟩


#print axioms coverage_29
end ForestUnimodality.FiniteRows.FiniteData
