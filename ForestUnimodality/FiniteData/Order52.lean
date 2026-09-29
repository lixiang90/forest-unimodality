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

theorem case_52_26_1_checked :
    (Witness.rising).check 52 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_26_2_checked :
    (Witness.rising).check 52 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_26_3_checked :
    (Witness.rising).check 52 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_26_4_checked :
    (Witness.rising).check 52 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_26_5_checked :
    (Witness.rising).check 52 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_26_6_checked :
    (Witness.rising).check 52 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_26_7_checked :
    (Witness.rising).check 52 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_26_8_checked :
    (Witness.rising).check 52 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_26_9_checked :
    (Witness.rising).check 52 26 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_26_10_checked :
    (Witness.rising).check 52 26 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_26_11 : Certificate := {
  objectiveScale := 198428880000000
  eta := 161254951982400276000
  rows := #[⟨.count 2, 45323691497956872000⟩, ⟨.count 4, 537109358822356320⟩, ⟨.count 5, 81725664609388800⟩, ⟨.count 6, 13980503184991200⟩, ⟨.count 7, 2887047934570800⟩, ⟨.count 8, 723125636513280⟩, ⟨.count 9, 255587509457280⟩, ⟨.count 10, 198016147929600⟩, ⟨.count 12, 30756674828880⟩, ⟨.path 11, 56398430088000⟩, ⟨.path 12, 30564049993620⟩, ⟨.hall 2 1, 48993450205900200⟩, ⟨.hall 10 1, 1852581630900⟩, ⟨.hall 9 3, 329044690260⟩, ⟨.hall 8 4, 87235949944⟩, ⟨.hall 8 5, 105414070520⟩, ⟨.hall 7 7, 83128662925⟩, ⟨.hall 2 8, 408713885580⟩, ⟨.hall 7 8, 4514257020⟩, ⟨.hall 6 11, 86749036000⟩, ⟨.hall 6 12, 6820992750⟩, ⟨.hall 10 14, 64935850980⟩, ⟨.hall 9 16, 1283437995840⟩, ⟨.hall 5 20, 11336686395091200⟩, ⟨.hall 4 21, 8216982583009200⟩, ⟨.hall 1 24, 3356200626625566720⟩]
  caps := #[0, 8047788451560000, 0, 1604445804029640, 124729789574520, 0, 17020794304800, 2454659699940, 1155813747660, 125692176480, 806834519400, 39915482100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_26_11_checked :
    (Witness.linear .positive case_52_26_11).check 52 26 11 = true := by
  change case_52_26_11.check 52 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_26_12 : Certificate := {
  objectiveScale := 20020000000
  eta := 23211117617688000
  rows := #[⟨.count 2, 7130719188552960⟩, ⟨.count 4, 99304650244800⟩, ⟨.count 5, 17648003973600⟩, ⟨.count 6, 3398771376000⟩, ⟨.count 7, 738185207760⟩, ⟨.count 8, 183881617920⟩, ⟨.count 9, 55233097920⟩, ⟨.count 10, 22399977600⟩, ⟨.count 11, 19978358400⟩, ⟨.path 12, 2477114640⟩, ⟨.path 13, 4508584080⟩, ⟨.privateRow 9 7, 980674240⟩, ⟨.privateRow 11 2, 619819200⟩, ⟨.privateRow 11 3, 88288200⟩, ⟨.privateRow 13 0, 322213320⟩, ⟨.privateRow 16 3, 559684125⟩, ⟨.privateRow 17 3, 567927360⟩, ⟨.privateRow 19 3, 85765680⟩, ⟨.privateRow 21 5, 301078377600⟩, ⟨.hall 2 1, 8753388243600⟩, ⟨.hall 11 1, 638858220⟩, ⟨.hall 13 1, 292672380⟩, ⟨.hall 14 2, 81897816⟩, ⟨.hall 10 3, 48953520⟩, ⟨.hall 19 3, 116396280⟩, ⟨.hall 9 4, 67093488⟩, ⟨.hall 17 4, 119255136⟩, ⟨.hall 18 4, 347963616⟩, ⟨.hall 9 5, 231000⟩, ⟨.hall 20 5, 23279256000⟩, ⟨.hall 8 6, 31178840⟩, ⟨.hall 19 6, 94979364480⟩, ⟨.hall 18 7, 23328264960⟩, ⟨.hall 7 8, 13535760⟩, ⟨.hall 17 8, 7661734080⟩, ⟨.hall 7 9, 9003456⟩, ⟨.hall 16 9, 5024859840⟩, ⟨.hall 15 10, 1677475800⟩, ⟨.hall 6 12, 7664580⟩, ⟨.hall 13 12, 348828480⟩, ⟨.hall 6 13, 63526320⟩, ⟨.hall 2 14, 14126112⟩, ⟨.hall 11 14, 110990880⟩, ⟨.hall 5 20, 3121748229600⟩, ⟨.hall 4 21, 2366103579840⟩, ⟨.hall 1 24, 499678055997120⟩]
  caps := #[0, 0, 3060239262080, 0, 30728617920, 8535727200, 1349428080, 0, 296033920, 96160064, 97137040, 124484360, 71030960, 0, 0, 138738600, 0, 167207040, 0, 61261200, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_26_12_checked :
    (Witness.linear .positive case_52_26_12).check 52 26 12 = true := by
  change case_52_26_12.check 52 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_26_13 : Certificate := {
  objectiveScale := 31531500000
  eta := 24241806677088000
  rows := #[⟨.count 2, 11794381044526080⟩, ⟨.count 3, 1610348586406560⟩, ⟨.count 4, 383738980584960⟩, ⟨.count 5, 69076536328800⟩, ⟨.count 6, 13883748278400⟩, ⟨.count 7, 3074956925040⟩, ⟨.count 8, 769832743680⟩, ⟨.count 9, 213041949120⟩, ⟨.count 10, 72043171200⟩, ⟨.count 11, 31632400800⟩, ⟨.count 12, 31632400800⟩, ⟨.path 14, 9044592480⟩, ⟨.path 15, 128260440⟩, ⟨.privateRow 5 21, 2102116816800⟩, ⟨.privateRow 9 9, 4993468480⟩, ⟨.privateRow 10 6, 957640320⟩, ⟨.privateRow 10 7, 4044104064⟩, ⟨.privateRow 11 4, 1154052900⟩, ⟨.privateRow 11 5, 4275671400⟩, ⟨.privateRow 12 2, 1015993440⟩, ⟨.privateRow 13 13, 428107680⟩, ⟨.privateRow 14 0, 695217600⟩, ⟨.privateRow 15 0, 11561550⟩, ⟨.privateRow 18 4, 68612544⟩, ⟨.privateRow 19 7, 80791270560⟩, ⟨.privateRow 20 0, 99768240⟩, ⟨.privateRow 20 4, 232792560⟩, ⟨.hall 12 1, 987940800⟩, ⟨.hall 14 1, 799638840⟩, ⟨.hall 15 1, 279999720⟩, ⟨.hall 16 1, 6726720⟩, ⟨.hall 17 1, 14294280⟩, ⟨.hall 18 1, 36756720⟩, ⟨.hall 20 1, 465585120⟩, ⟨.hall 21 1, 2444321880⟩, ⟨.hall 12 2, 46652760⟩, ⟨.hall 11 3, 118461420⟩, ⟨.hall 18 3, 7351344⟩, ⟨.hall 22 3, 107550162720⟩, ⟨.hall 20 4, 465585120⟩, ⟨.hall 21 4, 9777287520⟩, ⟨.hall 10 5, 49959000⟩, ⟨.hall 16 5, 40840800⟩, ⟨.hall 18 5, 61261200⟩, ⟨.hall 9 6, 74745720⟩, ⟨.hall 8 8, 65888928⟩, ⟨.hall 17 8, 36250294080⟩, ⟨.hall 16 9, 14227012800⟩, ⟨.hall 15 10, 9345936600⟩, ⟨.hall 7 11, 89379675⟩, ⟨.hall 7 12, 29785140⟩, ⟨.hall 6 15, 1402160760⟩, ⟨.hall 2 16, 659218560⟩, ⟨.hall 5 20, 5587021440000⟩]
  caps := #[0, 0, 0, 337316419440, 65181916800, 3259095840, 18623404800, 0, 2058376320, 495535040, 64421280, 126126000, 187830720, 0, 309133440, 0, 181621440, 0, 1303638336, 0, 6318655200, 0, 0, 0, 0, 0, 0] }

theorem case_52_26_13_checked :
    (Witness.linear .positive case_52_26_13).check 52 26 13 = true := by
  change case_52_26_13.check 52 26 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_26_14 : Certificate := {
  objectiveScale := 3432000000
  eta := 10739779998948000
  rows := #[⟨.count 2, 2343374645451840⟩, ⟨.count 3, 65139548554080⟩, ⟨.count 4, 60299791231680⟩, ⟨.count 5, 13557838694400⟩, ⟨.count 6, 3147355411200⟩, ⟨.count 7, 781368227640⟩, ⟨.count 8, 206523757440⟩, ⟨.count 9, 61579758240⟩, ⟨.count 10, 19877457600⟩, ⟨.count 11, 7214407200⟩, ⟨.count 12, 3440717280⟩, ⟨.count 13, 3452609160⟩, ⟨.path 15, 335419700⟩, ⟨.path 16, 489035680⟩, ⟨.privateRow 5 21, 889733164320⟩, ⟨.privateRow 10 8, 820659840⟩, ⟨.privateRow 10 9, 1233512280⟩, ⟨.privateRow 11 6, 337387050⟩, ⟨.privateRow 12 4, 323302980⟩, ⟨.privateRow 12 5, 388930542⟩, ⟨.privateRow 15 0, 28133105⟩, ⟨.privateRow 16 0, 44717400⟩, ⟨.hall 13 1, 37657620⟩, ⟨.hall 14 1, 39099060⟩, ⟨.hall 16 1, 73993920⟩, ⟨.hall 17 1, 66706640⟩, ⟨.hall 18 1, 134774640⟩, ⟨.hall 13 2, 38618580⟩, ⟨.hall 12 3, 42674940⟩, ⟨.hall 19 3, 128035908⟩, ⟨.hall 2 4, 8807318520⟩, ⟨.hall 11 5, 18115020⟩, ⟨.hall 20 5, 25607181600⟩, ⟨.hall 10 6, 24339420⟩, ⟨.hall 19 6, 5121436320⟩, ⟨.hall 18 7, 1886844960⟩, ⟨.hall 9 8, 22424752⟩, ⟨.hall 17 8, 724243520⟩, ⟨.hall 8 10, 29869420⟩, ⟨.hall 8 11, 4515280⟩, ⟨.hall 7 13, 320320⟩, ⟨.hall 12 13, 138738600⟩, ⟨.hall 7 14, 367699332⟩, ⟨.hall 6 19, 1623146124600⟩, ⟨.hall 5 20, 1620624205200⟩, ⟨.hall 1 24, 305908512829920⟩]
  caps := #[0, 1572861936800, 0, 0, 0, 0, 790755680, 31408520, 116167520, 0, 77797720, 0, 17239222, 0, 71586240, 4177250, 0, 0, 85765680, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_26_14_checked :
    (Witness.linear .positive case_52_26_14).check 52 26 14 = true := by
  change case_52_26_14.check 52 26 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_26_15 : Certificate := {
  objectiveScale := 693000000
  eta := 577185873264000
  rows := #[⟨.count 2, 194122922273280⟩, ⟨.count 3, 48000661909200⟩, ⟨.count 4, 11840760771840⟩, ⟨.count 5, 2907579074400⟩, ⟨.count 6, 810118108800⟩, ⟨.count 7, 233025352560⟩, ⟨.count 8, 70474884480⟩, ⟨.count 9, 23132229120⟩, ⟨.count 10, 8014406400⟩, ⟨.count 11, 3309906600⟩, ⟨.count 12, 1553872320⟩, ⟨.count 13, 1045352880⟩, ⟨.count 14, 1046485440⟩, ⟨.path 15, 138600000⟩, ⟨.privateRow 4 22, 207418170960⟩, ⟨.privateRow 11 7, 267066800⟩, ⟨.privateRow 11 8, 429954525⟩, ⟨.privateRow 13 3, 61364160⟩, ⟨.privateRow 13 4, 70898256⟩, ⟨.privateRow 16 0, 63063000⟩, ⟨.privateRow 19 0, 336936600⟩, ⟨.privateRow 20 0, 232792560⟩, ⟨.privateRow 20 2, 325909584⟩, ⟨.hall 14 1, 81681600⟩, ⟨.hall 16 1, 105064960⟩, ⟨.hall 17 1, 160640480⟩, ⟨.hall 20 1, 1197218880⟩, ⟨.hall 21 1, 3724680960⟩, ⟨.hall 22 1, 27314327040⟩, ⟨.hall 23 1, 314114760960⟩, ⟨.hall 24 1, 7538754263040⟩, ⟨.hall 13 2, 39296400⟩, ⟨.hall 21 2, 7061374320⟩, ⟨.hall 20 3, 1507608960⟩, ⟨.hall 22 3, 466050705120⟩, ⟨.hall 12 4, 11175120⟩, ⟨.hall 19 4, 452282688⟩, ⟨.hall 21 4, 42368245920⟩, ⟨.hall 11 5, 13373580⟩, ⟨.hall 20 5, 10531092000⟩, ⟨.hall 11 6, 367840⟩, ⟨.hall 10 7, 10244080⟩, ⟨.hall 18 7, 1310989680⟩, ⟨.hall 9 8, 6683264⟩, ⟨.hall 17 8, 500980480⟩, ⟨.hall 9 9, 6372576⟩, ⟨.hall 8 10, 1087800⟩, ⟨.hall 8 11, 23326600⟩, ⟨.hall 13 11, 6417840⟩, ⟨.hall 14 11, 10570560⟩, ⟨.hall 7 14, 137693556⟩, ⟨.hall 7 18, 109461512160⟩, ⟨.hall 6 19, 782648586720⟩, ⟨.hall 5 20, 935715237600⟩, ⟨.hall 4 21, 764490767040⟩, ⟨.assumptionRow 15, 1051393728⟩]
  caps := #[0, 0, 0, 18087385008, 0, 0, 0, 186234048, 0, 13069056, 22678656, 1797840, 3459456, 8909472, 4908288, 11806872, 0, 0, 0, 245044800, 0, 1862340480, 0, 0, 0, 0, 0] }

theorem case_52_26_15_checked :
    (Witness.linear .conditional case_52_26_15).check 52 26 15 = true := by
  change case_52_26_15.check 52 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_26_16 : Certificate := {
  objectiveScale := 840000000
  eta := 1495971549072000
  rows := #[⟨.count 3, 25384399120080⟩, ⟨.count 4, 7282682447040⟩, ⟨.count 5, 2169626659200⟩, ⟨.count 6, 665121600000⟩, ⟨.count 7, 210677266800⟩, ⟨.count 8, 69004615680⟩, ⟨.count 9, 25631686080⟩, ⟨.count 10, 10118908800⟩, ⟨.count 11, 4221617400⟩, ⟨.count 12, 1902700800⟩, ⟨.count 13, 898120080⟩, ⟨.count 14, 792792000⟩, ⟨.count 15, 693693000⟩, ⟨.path 14, 99413160⟩, ⟨.privateRow 4 22, 865522738080⟩, ⟨.privateRow 13 4, 25822368⟩, ⟨.privateRow 14 3, 128092536⟩, ⟨.privateRow 14 4, 13339040⟩, ⟨.privateRow 17 0, 83891808⟩, ⟨.privateRow 25 0, 29094879733920⟩, ⟨.privateRow 26 0, 753875426304000⟩, ⟨.hall 1 1, 1914136824600⟩, ⟨.hall 15 1, 94053960⟩, ⟨.hall 17 1, 168127960⟩, ⟨.hall 18 1, 432329040⟩, ⟨.hall 19 1, 1369041960⟩, ⟨.hall 20 1, 5476167840⟩, ⟨.hall 21 1, 28749881160⟩, ⟨.hall 22 1, 210832461840⟩, ⟨.hall 23 1, 2424573311160⟩, ⟨.hall 14 2, 47159112⟩, ⟨.hall 13 3, 4046328⟩, ⟨.hall 12 4, 5281056⟩, ⟨.hall 13 4, 13334464⟩, ⟨.hall 12 5, 16652240⟩, ⟨.hall 11 6, 15774880⟩, ⟨.hall 10 7, 2925720⟩, ⟨.hall 11 7, 4614225⟩, ⟨.hall 10 8, 18604320⟩, ⟨.hall 15 8, 320320⟩, ⟨.hall 9 9, 4416300⟩, ⟨.hall 9 10, 27681120⟩, ⟨.hall 14 11, 55495440⟩, ⟨.hall 8 12, 42557680⟩, ⟨.hall 8 13, 92414608⟩, ⟨.hall 7 14, 80336256⟩, ⟨.hall 1 17, 3403400⟩, ⟨.hall 7 18, 529713344160⟩, ⟨.hall 6 19, 1110653303760⟩, ⟨.hall 5 20, 1367046595200⟩, ⟨.hall 4 21, 1275703228800⟩, ⟨.assumptionRow 16, 700124040⟩]
  caps := #[0, 1473099381600, 0, 0, 10039925280, 464471280, 817293360, 26666640, 249128880, 0, 45645600, 9736080, 27627600, 830760, 6745200, 30861600, 0, 25874688, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_26_16_checked :
    (Witness.linear .conditional case_52_26_16).check 52 26 16 = true := by
  change case_52_26_16.check 52 26 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_27_1_checked :
    (Witness.rising).check 52 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_27_2_checked :
    (Witness.rising).check 52 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_27_3_checked :
    (Witness.rising).check 52 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_27_4_checked :
    (Witness.rising).check 52 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_27_5_checked :
    (Witness.rising).check 52 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_27_6_checked :
    (Witness.rising).check 52 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_27_7_checked :
    (Witness.rising).check 52 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_27_8_checked :
    (Witness.rising).check 52 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_27_9_checked :
    (Witness.rising).check 52 27 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_27_10_checked :
    (Witness.rising).check 52 27 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_27_11 : Certificate := {
  objectiveScale := 200232201728520000000
  eta := 102105323305661364095927520
  rows := #[⟨.count 2, 24002626303577671439049360⟩, ⟨.count 3, 3838663519430318539080120⟩, ⟨.count 4, 534721016985533821563120⟩, ⟨.count 5, 83136290018360466888000⟩, ⟨.count 6, 14355510543868057363800⟩, ⟨.count 7, 2959631573052648934440⟩, ⟨.count 8, 736049568910004949600⟩, ⟨.count 9, 258944193692438173920⟩, ⟨.count 10, 199550440527546408300⟩, ⟨.count 12, 29629536726249860400⟩, ⟨.path 11, 58747796950580892000⟩, ⟨.path 12, 29517838075892966085⟩, ⟨.privateRow 7 12, 133642179792876474720⟩, ⟨.privateRow 8 8, 13899860810733292395⟩, ⟨.privateRow 8 9, 39230794471962873780⟩, ⟨.privateRow 8 10, 67312920253544001036⟩, ⟨.privateRow 8 11, 67735027533205652620⟩, ⟨.privateRow 9 5, 6963439944418317360⟩, ⟨.privateRow 9 6, 16566755732874436320⟩, ⟨.privateRow 9 7, 15410019437647794960⟩, ⟨.privateRow 9 8, 43957281482946992160⟩, ⟨.privateRow 10 3, 14424197197188000222⟩, ⟨.privateRow 10 4, 404039137176134460⟩, ⟨.privateRow 11 0, 1867030522768150740⟩, ⟨.hall 7 9, 1902633895466073⟩, ⟨.hall 6 10, 17072286774527160⟩, ⟨.hall 7 10, 20055727506007116⟩, ⟨.hall 6 11, 35889923357220735⟩, ⟨.hall 5 16, 1002809979715658400⟩, ⟨.hall 8 18, 129464745906751295040⟩, ⟨.hall 4 21, 1056760903133466050520⟩]
  caps := #[0, 62077620480612918976080, 1143818692090214655240, 0, 0, 0, 0, 2462321538739606320, 213754349856542150, 3229910179080354480, 681761200973591700, 336601906385668380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_27_11_checked :
    (Witness.linear .positive case_52_27_11).check 52 27 11 = true := by
  change case_52_27_11.check 52 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_27_12 : Certificate := {
  objectiveScale := 5399222400000
  eta := 4228819913670992640
  rows := #[⟨.count 2, 1100444445837696960⟩, ⟨.count 3, 197961561709591680⟩, ⟨.count 4, 31583610985006080⟩, ⟨.count 5, 5432400621648000⟩, ⟨.count 6, 1038259939036320⟩, ⟨.count 7, 219255672636000⟩, ⟨.count 8, 52771279841280⟩, ⟨.count 9, 15238765301760⟩, ⟨.count 10, 6250274830800⟩, ⟨.count 11, 5383834616160⟩, ⟨.path 12, 838701709560⟩, ⟨.path 13, 1116545694264⟩, ⟨.privateRow 7 13, 4818805992000⟩, ⟨.privateRow 8 10, 1562899410072⟩, ⟨.privateRow 8 11, 4339305050080⟩, ⟨.privateRow 8 12, 3860399022480⟩, ⟨.privateRow 9 7, 420359459520⟩, ⟨.privateRow 9 8, 1386945705600⟩, ⟨.privateRow 9 9, 2167643814336⟩, ⟨.privateRow 9 10, 2778879783680⟩, ⟨.privateRow 10 4, 81494513100⟩, ⟨.privateRow 10 5, 489185124120⟩, ⟨.privateRow 10 6, 754828164090⟩, ⟨.privateRow 10 7, 1029987569520⟩, ⟨.privateRow 10 8, 597248483832⟩, ⟨.privateRow 11 2, 200626105680⟩, ⟨.privateRow 11 3, 307080774000⟩, ⟨.privateRow 11 4, 140421314880⟩, ⟨.privateRow 12 0, 147457825515⟩, ⟨.privateRow 13 0, 74513422368⟩, ⟨.privateRow 14 0, 74610504540⟩, ⟨.privateRow 15 0, 95140528560⟩, ⟨.privateRow 16 0, 75234789630⟩, ⟨.privateRow 17 0, 99411137280⟩, ⟨.privateRow 18 0, 232373533392⟩, ⟨.privateRow 19 0, 524714430240⟩, ⟨.privateRow 20 0, 1373359707720⟩, ⟨.privateRow 21 0, 4185477204480⟩, ⟨.privateRow 22 0, 12818023938720⟩, ⟨.hall 16 3, 1082298672⟩, ⟨.hall 22 4, 1127986106607360⟩, ⟨.hall 16 5, 801702720⟩, ⟨.hall 21 5, 192270359080800⟩, ⟨.hall 20 6, 43598720880000⟩, ⟨.hall 19 7, 12818023938720⟩, ⟨.hall 18 8, 4722429872160⟩, ⟨.hall 8 9, 762104448⟩, ⟨.hall 17 9, 2068874039232⟩, ⟨.hall 7 10, 3044969172⟩, ⟨.hall 8 10, 646988160⟩, ⟨.hall 16 10, 966853480320⟩, ⟨.hall 15 11, 677939862600⟩, ⟨.hall 6 12, 805037904⟩, ⟨.hall 6 13, 8710745472⟩, ⟨.hall 5 17, 229235167200⟩, ⟨.hall 9 17, 4956126215040⟩, ⟨.hall 4 22, 1373200477608960⟩]
  caps := #[0, 0, 0, 0, 10332896848560, 5548411131120, 998807060160, 0, 30739572864, 43540827120, 0, 70380248400, 27915667065, 15154163640, 0, 0, 0, 200425680000, 442259305488, 0, 1678550753880, 14125985565120, 0, 0, 0, 0] }

theorem case_52_27_12_checked :
    (Witness.linear .positive case_52_27_12).check 52 27 12 = true := by
  change case_52_27_12.check 52 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_27_13 : Certificate := {
  objectiveScale := 24657633000000
  eta := 25800990209483448960
  rows := #[⟨.count 2, 7433404942831948080⟩, ⟨.count 3, 1514885341173684480⟩, ⟨.count 4, 269768131814301120⟩, ⟨.count 5, 51882477847200000⟩, ⟨.count 6, 10630719710891280⟩, ⟨.count 7, 2339626685235840⟩, ⟨.count 8, 593826816623040⟩, ⟨.count 9, 165959678364480⟩, ⟨.count 10, 56500500256200⟩, ⟨.count 11, 24736537425600⟩, ⟨.count 12, 24913226978640⟩, ⟨.path 14, 7064707746096⟩, ⟨.privateRow 8 12, 43804285024500⟩, ⟨.privateRow 8 13, 63715323672000⟩, ⟨.privateRow 9 9, 8395430883840⟩, ⟨.privateRow 9 10, 19206213906880⟩, ⟨.privateRow 9 11, 20426383177200⟩, ⟨.privateRow 10 6, 1082223512370⟩, ⟨.privateRow 10 7, 6087028114440⟩, ⟨.privateRow 10 8, 10448376092154⟩, ⟨.privateRow 10 9, 14457756533220⟩, ⟨.privateRow 11 4, 1621713555000⟩, ⟨.privateRow 11 5, 3349739443050⟩, ⟨.privateRow 11 6, 5402173565880⟩, ⟨.privateRow 11 7, 5312733606180⟩, ⟨.privateRow 12 2, 1602826659720⟩, ⟨.privateRow 12 3, 1997951099760⟩, ⟨.privateRow 13 0, 869856261120⟩, ⟨.privateRow 14 0, 504827294400⟩, ⟨.privateRow 15 0, 596790588240⟩, ⟨.privateRow 16 0, 836263623195⟩, ⟨.privateRow 16 6, 126493657290⟩, ⟨.privateRow 17 0, 1594586710080⟩, ⟨.privateRow 18 0, 3408769816452⟩, ⟨.privateRow 19 0, 8829123423120⟩, ⟨.privateRow 20 0, 28211097329415⟩, ⟨.privateRow 21 0, 114141451263840⟩, ⟨.privateRow 22 0, 599242619135160⟩, ⟨.privateRow 24 3, 151608382641195480⟩, ⟨.hall 22 4, 13423034668627584⟩, ⟨.hall 9 8, 8026277616⟩, ⟨.hall 8 9, 29809871280⟩, ⟨.hall 9 9, 6543127584⟩, ⟨.hall 7 11, 307272042⟩, ⟨.hall 7 12, 71480581326⟩, ⟨.hall 6 15, 541016144955⟩, ⟨.hall 10 16, 26390049285600⟩, ⟨.hall 5 21, 12322088488710000⟩, ⟨.hall 4 22, 10753207473808800⟩]
  caps := #[0, 49004729742608640, 0, 0, 105002853411456, 4416540448320, 12561020952480, 1419323703336, 2580470608716, 0, 1218786450336, 0, 0, 0, 22366989216, 0, 49830834690, 27257892480, 605295574884, 3276788074560, 17186070786885, 0, 599242619135160, 0, 0, 0] }

theorem case_52_27_13_checked :
    (Witness.linear .positive case_52_27_13).check 52 27 13 = true := by
  change case_52_27_13.check 52 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_27_14 : Certificate := {
  objectiveScale := 29589159600000
  eta := 41237480078405170560
  rows := #[⟨.count 2, 12992378973009115680⟩, ⟨.count 3, 2893143365184552480⟩, ⟨.count 4, 607523062599573120⟩, ⟨.count 5, 133441733022998400⟩, ⟨.count 6, 29790918779862240⟩, ⟨.count 7, 7489099144406880⟩, ⟨.count 8, 1875779128903680⟩, ⟨.count 9, 555897459237120⟩, ⟨.count 10, 175404538108800⟩, ⟨.count 11, 63078170435280⟩, ⟨.count 12, 29683844910720⟩, ⟨.count 13, 29683844910720⟩, ⟨.path 15, 4158141837696⟩, ⟨.path 16, 2995333387200⟩, ⟨.privateRow 8 13, 94207657143600⟩, ⟨.privateRow 8 14, 28884280064640⟩, ⟨.privateRow 9 10, 499728028800⟩, ⟨.privateRow 9 11, 57006474885360⟩, ⟨.privateRow 9 12, 87980688956160⟩, ⟨.privateRow 10 8, 6071695549920⟩, ⟨.privateRow 10 9, 22843817516520⟩, ⟨.privateRow 10 10, 58903879744710⟩, ⟨.privateRow 11 6, 4906420646400⟩, ⟨.privateRow 11 7, 12446975877336⟩, ⟨.privateRow 11 8, 24699057823440⟩, ⟨.privateRow 11 9, 41911565115420⟩, ⟨.privateRow 12 4, 3173049890010⟩, ⟨.privateRow 12 5, 6858767195280⟩, ⟨.privateRow 12 6, 12235751548020⟩, ⟨.privateRow 12 7, 11955993089040⟩, ⟨.privateRow 13 2, 2201823660960⟩, ⟨.privateRow 13 3, 3846395654640⟩, ⟨.privateRow 13 4, 1986830778240⟩, ⟨.privateRow 14 0, 1710102459780⟩, ⟨.privateRow 15 0, 389211253200⟩, ⟨.privateRow 16 0, 252987314580⟩, ⟨.privateRow 17 0, 408868387200⟩, ⟨.privateRow 18 0, 637153236720⟩, ⟨.privateRow 19 0, 2002481601120⟩, ⟨.privateRow 19 7, 819197018640⟩, ⟨.privateRow 20 0, 6485309730900⟩, ⟨.privateRow 21 0, 26682417178560⟩, ⟨.privateRow 22 0, 145270937972160⟩, ⟨.privateRow 23 0, 319596063538752⟩, ⟨.hall 17 2, 28317921632⟩, ⟨.hall 23 3, 18376773653478240⟩, ⟨.hall 22 4, 2396970476540640⟩, ⟨.hall 17 5, 4045417376⟩, ⟨.hall 19 7, 3891185838540⟩, ⟨.hall 9 9, 105818592096⟩, ⟨.hall 9 10, 5388367320⟩, ⟨.hall 10 10, 41379093000⟩, ⟨.hall 8 11, 211052478560⟩, ⟨.hall 10 11, 58690585800⟩, ⟨.hall 7 14, 1240525516230⟩, ⟨.hall 12 14, 13993812600768⟩, ⟨.hall 11 15, 84026925567585⟩, ⟨.hall 6 20, 25143731121263040⟩, ⟨.hall 5 21, 32737843521583200⟩, ⟨.hall 4 22, 26414046199981440⟩]
  caps := #[0, 81244683520640640, 818398826673120, 1017896406268896, 110100079305216, 56199289962816, 34406274782880, 12561020952480, 1741552180368, 1144151744736, 485444304576, 744354603720, 748563467652, 0, 811147559508, 13383404496, 0, 0, 6498963014544, 19660728447360, 9264728187000, 97835529654720, 653719220874720, 0, 0, 0] }

theorem case_52_27_14_checked :
    (Witness.linear .positive case_52_27_14).check 52 27 14 = true := by
  change case_52_27_14.check 52 27 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_27_15 : Certificate := {
  objectiveScale := 6743968000000
  eta := 10143979056719988480
  rows := #[⟨.count 2, 2879027872378257600⟩, ⟨.count 3, 648780008983666560⟩, ⟨.count 4, 164156159908540800⟩, ⟨.count 5, 41644335552019200⟩, ⟨.count 6, 10604778471967680⟩, ⟨.count 7, 3012460503212160⟩, ⟨.count 8, 902208983195520⟩, ⟨.count 9, 286044323685120⟩, ⟨.count 10, 97821761637600⟩, ⟨.count 11, 37929357385920⟩, ⟨.count 12, 17668955304000⟩, ⟨.count 13, 16608817985760⟩, ⟨.count 14, 5359583108880⟩, ⟨.path 15, 1517301756432⟩, ⟨.privateRow 4 23, 15144495283597680⟩, ⟨.privateRow 9 11, 10294397393280⟩, ⟨.privateRow 9 12, 5682621584640⟩, ⟨.privateRow 10 9, 5278377304200⟩, ⟨.privateRow 10 10, 21482839463085⟩, ⟨.privateRow 11 7, 2721019116816⟩, ⟨.privateRow 11 8, 10161136585600⟩, ⟨.privateRow 11 9, 20463862779360⟩, ⟨.privateRow 12 5, 1325171647800⟩, ⟨.privateRow 12 6, 4953197136888⟩, ⟨.privateRow 12 7, 9907703085280⟩, ⟨.privateRow 12 8, 15165853302600⟩, ⟨.privateRow 13 3, 686370956040⟩, ⟨.privateRow 13 4, 2535433306560⟩, ⟨.privateRow 13 5, 4952744086752⟩, ⟨.privateRow 13 6, 2141416976160⟩, ⟨.privateRow 14 0, 435413541420⟩, ⟨.privateRow 14 2, 1516585330260⟩, ⟨.privateRow 14 3, 741560699880⟩, ⟨.privateRow 15 0, 726527672640⟩, ⟨.privateRow 16 0, 562194032400⟩, ⟨.privateRow 17 0, 935854308480⟩, ⟨.privateRow 18 0, 1996413475056⟩, ⟨.privateRow 19 0, 2245206643680⟩, ⟨.privateRow 20 0, 6052955748840⟩, ⟨.privateRow 21 0, 17788278119040⟩, ⟨.privateRow 22 0, 54476601739560⟩, ⟨.privateRow 24 3, 55130320960434720⟩, ⟨.hall 22 4, 4793940953081280⟩, ⟨.hall 21 5, 823201981842240⟩, ⟨.hall 20 6, 192706346289600⟩, ⟨.hall 19 7, 55773663685740⟩, ⟨.hall 10 8, 53857977600⟩, ⟨.hall 18 8, 20388903575040⟩, ⟨.hall 9 9, 93661489824⟩, ⟨.hall 10 9, 6420366855⟩, ⟨.hall 9 10, 115630200⟩, ⟨.hall 8 11, 161585473280⟩, ⟨.hall 11 11, 43681583946⟩, ⟨.hall 11 12, 139143023019⟩, ⟨.hall 7 14, 845411605038⟩, ⟨.hall 12 14, 17621838089856⟩, ⟨.hall 10 16, 6316415305200⟩, ⟨.hall 6 18, 84587943581856⟩, ⟨.hall 5 21, 22095646777713600⟩, ⟨.hall 4 22, 22276982531643840⟩, ⟨.assumptionRow 15, 11463497965920⟩]
  caps := #[0, 0, 1302624395072000, 48125218662752, 51538617370240, 31047874809952, 657536880000, 1739529471680, 339815059584, 8427832224, 657901265021, 4349859360, 296043455708, 92611265296, 8125277160, 199226930672, 0, 0, 0, 6894908240220, 2594123892360, 9388257896160, 0, 0, 0, 0] }

theorem case_52_27_15_checked :
    (Witness.linear .conditional case_52_27_15).check 52 27 15 = true := by
  change case_52_27_15.check 52 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_27_16 : Certificate := {
  objectiveScale := 7537376000000
  eta := 3454833446853909120
  rows := #[⟨.count 2, 949466638763042400⟩, ⟨.count 3, 266063722896011040⟩, ⟨.count 4, 76848326187272640⟩, ⟨.count 5, 22966643527027200⟩, ⟨.count 6, 7107899465066400⟩, ⟨.count 7, 2301397491032640⟩, ⟨.count 8, 784972787639040⟩, ⟨.count 9, 281546771425920⟩, ⟨.count 10, 107379060188400⟩, ⟨.count 11, 43288940494800⟩, ⟨.count 12, 19082471728320⟩, ⟨.count 13, 9541235864160⟩, ⟨.count 14, 8245512475200⟩, ⟨.count 15, 7308522421200⟩, ⟨.path 14, 708709687686⟩, ⟨.privateRow 3 24, 31426946247977280⟩, ⟨.privateRow 10 10, 12565036624140⟩, ⟨.privateRow 10 11, 14448386632680⟩, ⟨.privateRow 11 8, 3993659830160⟩, ⟨.privateRow 11 9, 17545138761150⟩, ⟨.privateRow 12 6, 1410571598436⟩, ⟨.privateRow 12 7, 7473313687840⟩, ⟨.privateRow 12 8, 17113119418395⟩, ⟨.privateRow 13 4, 380562114240⟩, ⟨.privateRow 13 5, 3329918499600⟩, ⟨.privateRow 13 6, 8118658437120⟩, ⟨.privateRow 13 7, 14162347251360⟩, ⟨.privateRow 13 8, 1161102777120⟩, ⟨.privateRow 14 3, 1290369160080⟩, ⟨.privateRow 14 4, 4555645642548⟩, ⟨.privateRow 14 5, 3677760326240⟩, ⟨.privateRow 15 1, 684002739420⟩, ⟨.privateRow 15 2, 1962568258560⟩, ⟨.privateRow 16 0, 768331844280⟩, ⟨.privateRow 17 0, 681447312000⟩, ⟨.privateRow 18 0, 1359260238336⟩, ⟨.privateRow 19 0, 3519513117120⟩, ⟨.hall 11 7, 45860457643⟩, ⟨.hall 19 7, 67447221201360⟩, ⟨.hall 10 8, 101364002880⟩, ⟨.hall 11 8, 57708977172⟩, ⟨.hall 10 9, 52123203405⟩, ⟨.hall 17 9, 169907529792⟩, ⟨.hall 9 10, 217132959120⟩, ⟨.hall 12 10, 39939017184⟩, ⟨.hall 12 11, 193258243728⟩, ⟨.hall 8 12, 389806167520⟩, ⟨.hall 8 13, 150669879360⟩, ⟨.hall 13 13, 16482611162160⟩, ⟨.hall 7 15, 3883478566968⟩, ⟨.hall 5 20, 1660688490052800⟩, ⟨.hall 6 20, 24173281726102080⟩, ⟨.hall 4 22, 43644442669027200⟩, ⟨.hall 3 23, 42479643445359120⟩, ⟨.assumptionRow 16, 7408181408320⟩]
  caps := #[0, 26942199519515280, 3167473414868840, 400865423373184, 1282459087756, 11465212258500, 2249114149100, 1570370834032, 55085226504, 502752698448, 0, 0, 0, 173913820718, 0, 527345614600, 0, 1449780012800, 0, 1092262691520, 0, 0, 0, 0, 0, 0] }

theorem case_52_27_16_checked :
    (Witness.linear .conditional case_52_27_16).check 52 27 16 = true := by
  change case_52_27_16.check 52 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_27_17 : Certificate := {
  objectiveScale := 173445300000000
  eta := 61745959475686886400
  rows := #[⟨.count 2, 17641702707339110400⟩, ⟨.count 3, 5117531967414266400⟩, ⟨.count 4, 1510091400220603200⟩, ⟨.count 5, 472649373187992000⟩, ⟨.count 6, 151756247703060000⟩, ⟨.count 7, 49774410852566400⟩, ⟨.count 8, 16616956413657600⟩, ⟨.count 9, 5626437876259200⟩, ⟨.count 10, 1905837769836000⟩, ⟨.count 11, 760648525837200⟩, ⟨.count 12, 318041195472000⟩, ⟨.count 13, 137817851371200⟩, ⟨.count 14, 98946149702400⟩, ⟨.count 15, 101194925832000⟩, ⟨.count 16, 94448597443200⟩, ⟨.count 18, 172031373914400⟩, ⟨.path 13, 21030072483420⟩, ⟨.privateRow 2 25, 137825802401086800⟩, ⟨.privateRow 10 10, 100246223402325⟩, ⟨.privateRow 11 8, 7870716453600⟩, ⟨.privateRow 11 9, 251581829499000⟩, ⟨.privateRow 12 7, 68369040940200⟩, ⟨.privateRow 12 8, 302580859581000⟩, ⟨.privateRow 12 9, 239982275075400⟩, ⟨.privateRow 13 5, 14434177332960⟩, ⟨.privateRow 13 6, 113942109204000⟩, ⟨.privateRow 13 7, 302750753382000⟩, ⟨.privateRow 13 8, 319905173174400⟩, ⟨.privateRow 14 4, 39225080774880⟩, ⟨.privateRow 14 5, 132909808231200⟩, ⟨.privateRow 14 6, 270942386489775⟩, ⟨.privateRow 14 7, 150627843966600⟩, ⟨.privateRow 15 2, 6950762582400⟩, ⟨.privateRow 15 3, 60267200273280⟩, ⟨.privateRow 15 4, 137112877902000⟩, ⟨.privateRow 15 5, 5903037340200⟩, ⟨.privateRow 16 1, 24992080167600⟩, ⟨.privateRow 16 2, 23359162046220⟩, ⟨.privateRow 17 0, 8586236131200⟩, ⟨.hall 12 7, 178851837780⟩, ⟨.hall 11 8, 4548305887125⟩, ⟨.hall 12 8, 2836211526720⟩, ⟨.hall 10 9, 5712854568750⟩, ⟨.hall 9 10, 1046029332600⟩, ⟨.hall 10 10, 442533294000⟩, ⟨.hall 9 11, 9385769408400⟩, ⟨.hall 8 13, 22268738892400⟩, ⟨.hall 13 13, 1147598646994800⟩, ⟨.hall 7 15, 32814377996400⟩, ⟨.hall 8 15, 67660544952000⟩, ⟨.hall 7 19, 281890609296135840⟩, ⟨.hall 6 20, 629171397070444800⟩, ⟨.hall 5 21, 884997157350852000⟩, ⟨.hall 4 22, 1108480418004960000⟩, ⟨.hall 3 23, 1164028787670048300⟩, ⟨.hall 2 24, 852682297521390336⟩, ⟨.assumptionRow 17, 97015073971200⟩]
  caps := #[0, 0, 0, 8455003352322912, 0, 252077200128600, 81569243246400, 81746095048800, 13454519638560, 10512605703600, 0, 0, 3712377840600, 865586937180, 803765250750, 0, 6227836148100, 0, 1413926085600, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_27_17_checked :
    (Witness.linear .conditional case_52_27_17).check 52 27 17 = true := by
  change case_52_27_17.check 52 27 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_28_1_checked :
    (Witness.rising).check 52 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_28_2_checked :
    (Witness.rising).check 52 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_28_3_checked :
    (Witness.rising).check 52 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_28_4_checked :
    (Witness.rising).check 52 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_28_5_checked :
    (Witness.rising).check 52 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_28_6_checked :
    (Witness.rising).check 52 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_28_7_checked :
    (Witness.rising).check 52 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_28_8_checked :
    (Witness.rising).check 52 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_28_9_checked :
    (Witness.rising).check 52 28 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_28_10_checked :
    (Witness.rising).check 52 28 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_28_11 : Certificate := {
  objectiveScale := 17582760000000
  eta := 12468802123653876000
  rows := #[⟨.count 2, 2735209643785819200⟩, ⟨.count 3, 402056435435054400⟩, ⟨.count 4, 53815782811190400⟩, ⟨.count 5, 8164663619112000⟩, ⟨.count 6, 1412468122665600⟩, ⟨.count 7, 277552892416800⟩, ⟨.count 8, 67699997164800⟩, ⟨.count 9, 23079544488000⟩, ⟨.count 10, 17694317440800⟩, ⟨.path 11, 5552752826400⟩, ⟨.path 12, 2420125562400⟩, ⟨.privateRow 4 24, 816466361911200⟩, ⟨.privateRow 6 15, 700629029100⟩, ⟨.privateRow 6 16, 60676698139200⟩, ⟨.privateRow 6 17, 77640076113600⟩, ⟨.privateRow 6 18, 88310396734560⟩, ⟨.privateRow 7 12, 9445517281200⟩, ⟨.privateRow 7 13, 16123117410400⟩, ⟨.privateRow 7 14, 25637832620400⟩, ⟨.privateRow 7 15, 34223318500800⟩, ⟨.privateRow 7 16, 35256344723600⟩, ⟨.privateRow 7 17, 36993212736480⟩, ⟨.privateRow 8 8, 703564461600⟩, ⟨.privateRow 8 9, 3568781416200⟩, ⟨.privateRow 8 10, 6426526360800⟩, ⟨.privateRow 8 11, 846249964560⟩, ⟨.privateRow 8 12, 17722810705600⟩, ⟨.privateRow 8 13, 18004181695500⟩, ⟨.privateRow 9 5, 512878766400⟩, ⟨.privateRow 9 6, 592252861200⟩, ⟨.privateRow 9 7, 1900281583200⟩, ⟨.privateRow 9 8, 6307696495100⟩, ⟨.privateRow 10 3, 1259758469970⟩, ⟨.privateRow 10 4, 317984835168⟩, ⟨.privateRow 11 0, 322584462200⟩, ⟨.privateRow 12 0, 142226884800⟩, ⟨.privateRow 13 0, 124961361525⟩, ⟨.privateRow 14 0, 151421350080⟩, ⟨.privateRow 14 14, 18317098800⟩, ⟨.privateRow 15 0, 214310055960⟩, ⟨.privateRow 16 0, 358357599600⟩, ⟨.privateRow 17 0, 719454936200⟩, ⟨.privateRow 18 0, 1755111103200⟩, ⟨.privateRow 19 0, 5293641553200⟩, ⟨.privateRow 20 0, 20247313966880⟩, ⟨.privateRow 21 0, 102058295238900⟩, ⟨.privateRow 22 0, 721803595312800⟩, ⟨.privateRow 23 0, 7896452447083200⟩, ⟨.privateRow 24 0, 184412535610343040⟩, ⟨.hall 12 10, 23225400⟩, ⟨.hall 13 11, 36902580⟩, ⟨.hall 5 17, 16019848000⟩, ⟨.hall 5 18, 103597621920⟩, ⟨.hall 4 21, 11817255777600⟩, ⟨.hall 6 21, 160677590673600⟩]
  caps := #[0, 3290914199196000, 603475137064800, 23102222800800, 0, 1120033533840, 279639145500, 571010929060, 110371139320, 58180404750, 0, 0, 78852228000, 85060446900, 0, 0, 0, 0, 0, 622781359200, 6047898977120, 53247806211600, 0, 6074194190064000, 0] }

theorem case_52_28_11_checked :
    (Witness.linear .positive case_52_28_11).check 52 28 11 = true := by
  change case_52_28_11.check 52 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_28_12 : Certificate := {
  objectiveScale := 186647760000000
  eta := 222864322482557355600
  rows := #[⟨.count 2, 55150295714405892000⟩, ⟨.count 3, 9390131841847957200⟩, ⟨.count 4, 1406222679570508800⟩, ⟨.count 5, 235987450487989200⟩, ⟨.count 6, 42082150847536800⟩, ⟨.count 7, 8620683292821600⟩, ⟨.count 8, 1995414018998400⟩, ⟨.count 9, 556572092076000⟩, ⟨.count 10, 222628836830400⟩, ⟨.count 11, 184640582926800⟩, ⟨.path 12, 35873333496000⟩, ⟨.path 13, 35310434959800⟩, ⟨.privateRow 4 24, 5707072563192000⟩, ⟨.privateRow 6 17, 1276582020714000⟩, ⟨.privateRow 6 18, 2700346439110320⟩, ⟨.privateRow 7 14, 498117298278600⟩, ⟨.privateRow 7 15, 750930600420000⟩, ⟨.privateRow 7 16, 1091352472610400⟩, ⟨.privateRow 7 17, 1547918277665760⟩, ⟨.privateRow 8 10, 21550771242000⟩, ⟨.privateRow 8 11, 133989577722000⟩, ⟨.privateRow 8 12, 232706685411200⟩, ⟨.privateRow 8 13, 359968153995450⟩, ⟨.privateRow 8 14, 416398379997600⟩, ⟨.privateRow 8 15, 538363252026600⟩, ⟨.privateRow 8 16, 471643313581440⟩, ⟨.privateRow 9 7, 7611242284800⟩, ⟨.privateRow 9 8, 44405520309150⟩, ⟨.privateRow 9 9, 76083592384800⟩, ⟨.privateRow 9 10, 111520556227080⟩, ⟨.privateRow 9 11, 104443158019200⟩, ⟨.privateRow 9 12, 227395773730125⟩, ⟨.privateRow 10 4, 1113144184152⟩, ⟨.privateRow 10 5, 16167094103160⟩, ⟨.privateRow 10 6, 27638323546680⟩, ⟨.privateRow 10 7, 39629994333930⟩, ⟨.privateRow 10 8, 31651524024120⟩, ⟨.privateRow 11 2, 3699437516775⟩, ⟨.privateRow 11 3, 16667714503440⟩, ⟨.privateRow 12 0, 4331292550200⟩, ⟨.privateRow 13 0, 2195877377925⟩, ⟨.privateRow 14 0, 1649102495040⟩, ⟨.privateRow 14 14, 11043097065000⟩, ⟨.privateRow 15 0, 2341136577780⟩, ⟨.privateRow 16 0, 3964188690000⟩, ⟨.privateRow 17 0, 7901949455400⟩, ⟨.privateRow 18 0, 19569706556400⟩, ⟨.privateRow 19 0, 42052113623520⟩, ⟨.privateRow 19 5, 30037224016800⟩, ⟨.privateRow 20 1, 192613699007730⟩, ⟨.privateRow 20 4, 68484870758304⟩, ⟨.privateRow 20 8, 57070725631920⟩, ⟨.privateRow 21 0, 392361238719450⟩, ⟨.privateRow 21 2, 856060884478800⟩, ⟨.privateRow 22 2, 4793940953081280⟩, ⟨.privateRow 23 5, 219722293682892000⟩, ⟨.hall 21 1, 3709597166074800⟩, ⟨.hall 22 1, 40282420508530200⟩, ⟨.hall 23 1, 909650295847172880⟩, ⟨.hall 18 8, 2002481601120⟩, ⟨.hall 14 12, 67957520400⟩, ⟨.hall 15 12, 713553964200⟩, ⟨.hall 6 14, 59495345910⟩, ⟨.hall 6 15, 114657993450⟩, ⟨.hall 5 18, 5720810649840⟩, ⟨.hall 7 20, 1002909535227600⟩, ⟨.hall 4 21, 252645109516800⟩]
  caps := #[0, 0, 0, 0, 397824768619200, 303492990715200, 0, 72412051617360, 4204372185640, 0, 0, 2007177073200, 0, 176396913000, 4211101014120, 1739712522240, 0, 21300907227600, 62349995307600, 0, 362399107762692, 998737698558600, 6506062722038880, 0, 0] }

theorem case_52_28_12_checked :
    (Witness.linear .positive case_52_28_12).check 52 28 12 = true := by
  change case_52_28_12.check 52 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_28_13 : Certificate := {
  objectiveScale := 502320000000
  eta := 751285746421610400
  rows := #[⟨.count 2, 192227632334337600⟩, ⟨.count 3, 34352304155769600⟩, ⟨.count 4, 6030575072121600⟩, ⟨.count 5, 1152096199254000⟩, ⟨.count 6, 233712090612000⟩, ⟨.count 7, 52471443024000⟩, ⟨.count 8, 12963532982400⟩, ⟨.count 9, 3521980261800⟩, ⟨.count 10, 1190528539200⟩, ⟨.count 11, 519675156000⟩, ⟨.count 12, 503685151200⟩, ⟨.path 13, 11892739950⟩, ⟨.path 14, 135980535600⟩, ⟨.privateRow 4 24, 242626881697200⟩, ⟨.privateRow 6 17, 816519904200⟩, ⟨.privateRow 6 18, 16657006045680⟩, ⟨.privateRow 7 14, 23424751350⟩, ⟨.privateRow 7 15, 3962129371200⟩, ⟨.privateRow 7 16, 6019045632600⟩, ⟨.privateRow 7 17, 11886388113600⟩, ⟨.privateRow 8 12, 834104871600⟩, ⟨.privateRow 8 13, 1682448317550⟩, ⟨.privateRow 8 14, 3042461822400⟩, ⟨.privateRow 8 15, 4205431830600⟩, ⟨.privateRow 8 16, 5315489459280⟩, ⟨.privateRow 9 9, 154327773600⟩, ⟨.privateRow 9 10, 477864927540⟩, ⟨.privateRow 9 11, 846353107600⟩, ⟨.privateRow 9 12, 1156769338725⟩, ⟨.privateRow 9 13, 1796028834600⟩, ⟨.privateRow 9 14, 1824374752200⟩, ⟨.privateRow 9 15, 931478347800⟩, ⟨.privateRow 10 6, 15517572840⟩, ⟨.privateRow 10 7, 138894996240⟩, ⟨.privateRow 10 8, 249830610120⟩, ⟨.privateRow 10 9, 387583179984⟩, ⟨.privateRow 10 10, 508914205800⟩, ⟨.privateRow 10 11, 524990015550⟩, ⟨.privateRow 11 4, 32226608700⟩, ⟨.privateRow 11 5, 81403660800⟩, ⟨.privateRow 11 6, 137398961700⟩, ⟨.privateRow 11 7, 133354657800⟩, ⟨.privateRow 12 2, 36244010880⟩, ⟨.privateRow 12 3, 33835992300⟩, ⟨.privateRow 13 0, 15490317150⟩, ⟨.privateRow 14 0, 9133684560⟩, ⟨.privateRow 15 0, 11810799000⟩, ⟨.privateRow 16 0, 18231028200⟩, ⟨.privateRow 17 0, 38581943400⟩, ⟨.privateRow 18 0, 94915875600⟩, ⟨.privateRow 19 0, 289128359520⟩, ⟨.privateRow 20 0, 1085123719680⟩, ⟨.privateRow 21 0, 5531587711650⟩, ⟨.privateRow 22 0, 38148880770000⟩, ⟨.privateRow 23 0, 430828026829200⟩, ⟨.privateRow 24 0, 9728880169488480⟩, ⟨.hall 15 4, 23126040⟩, ⟨.hall 16 11, 7348941600⟩, ⟨.hall 7 14, 973412440⟩, ⟨.hall 6 15, 1580693400⟩, ⟨.hall 6 16, 2995621200⟩, ⟨.hall 8 19, 1834295823360⟩, ⟨.hall 5 20, 1513317920400⟩, ⟨.hall 4 23, 473809099163400⟩]
  caps := #[0, 0, 102832021874400, 6696842334000, 0, 506954529900, 314851937400, 21295228500, 0, 0, 33476962806, 0, 6115222980, 20236564950, 0, 0, 90307186200, 8017027200, 167928087600, 0, 2305887904320, 0, 96135179540400, 0, 0] }

theorem case_52_28_13_checked :
    (Witness.linear .positive case_52_28_13).check 52 28 13 = true := by
  change case_52_28_13.check 52 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_28_14 : Certificate := {
  objectiveScale := 22260363125000
  eta := 43598895492877124400
  rows := #[⟨.count 2, 11633296712810572800⟩, ⟨.count 3, 2268587285107743600⟩, ⟨.count 4, 482922103801737600⟩, ⟨.count 5, 105554901180128400⟩, ⟨.count 6, 23500031808052800⟩, ⟨.count 7, 5880924374925600⟩, ⟨.count 8, 1474697412988800⟩, ⟨.count 9, 427548561640200⟩, ⟨.count 10, 133989577722000⟩, ⟨.count 11, 47853420615000⟩, ⟨.count 12, 22969641895200⟩, ⟨.count 13, 22969641895200⟩, ⟨.path 15, 3566339136360⟩, ⟨.path 16, 1815318424920⟩, ⟨.privateRow 4 24, 35297379095378400⟩, ⟨.privateRow 6 18, 675655496596080⟩, ⟨.privateRow 7 16, 540037935837400⟩, ⟨.privateRow 7 17, 1112681935725360⟩, ⟨.privateRow 8 13, 64254092953050⟩, ⟨.privateRow 8 14, 204522619501200⟩, ⟨.privateRow 8 15, 496032123587000⟩, ⟨.privateRow 8 16, 690898986217440⟩, ⟨.privateRow 9 11, 47234709722200⟩, ⟨.privateRow 9 12, 98208270034875⟩, ⟨.privateRow 9 13, 190311603682200⟩, ⟨.privateRow 9 14, 299581747765300⟩, ⟨.privateRow 9 15, 341795231898120⟩, ⟨.privateRow 10 8, 4075054925760⟩, ⟨.privateRow 10 9, 21292161987096⟩, ⟨.privateRow 10 10, 48073836370560⟩, ⟨.privateRow 10 11, 83256251248170⟩, ⟨.privateRow 10 12, 117736815956760⟩, ⟨.privateRow 10 13, 148200593541000⟩, ⟨.privateRow 10 14, 90918018919728⟩, ⟨.privateRow 11 6, 3929780905050⟩, ⟨.privateRow 11 7, 10820409818400⟩, ⟨.privateRow 11 8, 16357169228400⟩, ⟨.privateRow 11 9, 48588139800200⟩, ⟨.privateRow 11 10, 48157942382550⟩, ⟨.privateRow 11 11, 13622688050400⟩, ⟨.privateRow 12 4, 2797584589800⟩, ⟨.privateRow 12 5, 6184134356400⟩, ⟨.privateRow 12 6, 10199806016400⟩, ⟨.privateRow 12 7, 14238233149140⟩, ⟨.privateRow 13 2, 2019309177600⟩, ⟨.privateRow 13 3, 3715011115200⟩, ⟨.privateRow 13 4, 907987980900⟩, ⟨.privateRow 14 0, 1160082924000⟩, ⟨.privateRow 15 0, 261018657900⟩, ⟨.privateRow 16 0, 187398010800⟩, ⟨.privateRow 17 0, 338357519500⟩, ⟨.privateRow 18 0, 896427714000⟩, ⟨.privateRow 19 0, 2366569164960⟩, ⟨.privateRow 20 0, 9992180918720⟩, ⟨.privateRow 21 0, 56206017667800⟩, ⟨.privateRow 22 0, 337236106006800⟩, ⟨.privateRow 23 0, 4327863360420600⟩, ⟨.privateRow 24 4, 398163429158695200⟩, ⟨.hall 8 13, 95871455680⟩, ⟨.hall 7 14, 228556688360⟩, ⟨.hall 7 15, 57113731675⟩, ⟨.hall 6 17, 2310222280080⟩, ⟨.hall 6 18, 7674769243440⟩, ⟨.hall 9 18, 101549995747200⟩, ⟨.hall 5 21, 2066737479697800⟩, ⟨.hall 4 23, 52496420501725200⟩]
  caps := #[0, 0, 0, 0, 0, 120432075283520, 27284141604720, 8053672176550, 15215454284030, 0, 525591146080, 1046191802760, 0, 0, 868637529760, 0, 0, 5413720312000, 0, 42598244969280, 189851437455680, 0, 7081958226142800, 0, 0] }

theorem case_52_28_14_checked :
    (Witness.linear .positive case_52_28_14).check 52 28 14 = true := by
  change case_52_28_14.check 52 28 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_28_15 : Certificate := {
  objectiveScale := 120677356800000
  eta := 327887583912185497200
  rows := #[⟨.count 2, 79147965135371932800⟩, ⟨.count 3, 18781353215730705600⟩, ⟨.count 4, 4354392600759801600⟩, ⟨.count 5, 1084551316917868800⟩, ⟨.count 6, 282106877309056800⟩, ⟨.count 7, 74174194052758800⟩, ⟨.count 8, 20814671855577600⟩, ⟨.count 9, 6479005126393800⟩, ⟨.count 10, 2170631159096400⟩, ⟨.count 11, 809679876805800⟩, ⟨.count 12, 365747374792800⟩, ⟨.count 13, 327317397006600⟩, ⟨.count 14, 87702269054400⟩, ⟨.path 15, 32456067363720⟩, ⟨.privateRow 6 18, 5963754295699200⟩, ⟨.privateRow 7 16, 4431400761387600⟩, ⟨.privateRow 7 17, 14760291881855520⟩, ⟨.privateRow 8 14, 2225967114571200⟩, ⟨.privateRow 8 15, 6153775878650400⟩, ⟨.privateRow 8 16, 11240507483805600⟩, ⟨.privateRow 9 11, 58468179369600⟩, ⟨.privateRow 9 12, 937318000518900⟩, ⟨.privateRow 9 13, 2587738974420600⟩, ⟨.privateRow 9 14, 4564172252039400⟩, ⟨.privateRow 9 15, 6367915585591560⟩, ⟨.privateRow 10 9, 69065536880340⟩, ⟨.privateRow 10 10, 390762332120160⟩, ⟨.privateRow 10 11, 1070789891236065⟩, ⟨.privateRow 10 12, 1930702808754720⟩, ⟨.privateRow 10 13, 2704884148086120⟩, ⟨.privateRow 10 14, 3110799483359568⟩, ⟨.privateRow 11 7, 44420629780800⟩, ⟨.privateRow 11 8, 185584265766900⟩, ⟨.privateRow 11 9, 455042526939000⟩, ⟨.privateRow 11 10, 833954611990500⟩, ⟨.privateRow 11 11, 1205011278385200⟩, ⟨.privateRow 11 12, 1122380228970000⟩, ⟨.privateRow 12 5, 24846968396250⟩, ⟨.privateRow 12 6, 93243895945200⟩, ⟨.privateRow 12 7, 216135495756180⟩, ⟨.privateRow 12 8, 377379437034600⟩, ⟨.privateRow 12 9, 321519771047475⟩, ⟨.privateRow 13 3, 14067206722800⟩, ⟨.privateRow 13 4, 50466953587050⟩, ⟨.privateRow 13 5, 111314418415200⟩, ⟨.privateRow 13 6, 66788651049120⟩, ⟨.privateRow 14 0, 9292264221240⟩, ⟨.privateRow 14 2, 31804119547200⟩, ⟨.privateRow 14 3, 7569541079100⟩, ⟨.privateRow 15 0, 11902450800240⟩, ⟨.privateRow 16 0, 9276201534600⟩, ⟨.privateRow 17 0, 17053218982800⟩, ⟨.privateRow 18 0, 17749268737200⟩, ⟨.privateRow 18 1, 26623903105800⟩, ⟨.privateRow 19 0, 122469954286680⟩, ⟨.privateRow 20 0, 472130548409520⟩, ⟨.privateRow 21 0, 2276343715545900⟩, ⟨.privateRow 22 0, 16187333088326400⟩, ⟨.privateRow 23 0, 168786671056403400⟩, ⟨.privateRow 24 0, 3941817948671082480⟩, ⟨.hall 20 5, 24088293286200⟩, ⟨.hall 16 10, 442940752800⟩, ⟨.hall 8 14, 3340248671760⟩, ⟨.hall 8 15, 7847045125920⟩, ⟨.hall 7 16, 31937693467680⟩, ⟨.hall 9 16, 50752370869200⟩, ⟨.hall 7 17, 34735630309380⟩, ⟨.hall 9 18, 5189435578126800⟩, ⟨.hall 6 19, 2022241035124440⟩, ⟨.hall 5 22, 751743267607332000⟩, ⟨.hall 4 23, 948476548144125000⟩, ⟨.hall 3 24, 751254128629228224⟩, ⟨.assumptionRow 15, 227191046882800⟩]
  caps := #[0, 381601969327378800, 0, 1058382320996000, 0, 638621782718920, 117588695224000, 0, 0, 0, 2137916700920, 24014813438200, 479298481200, 11800042725240, 104814509800, 5828524782080, 25947662340600, 0, 0, 181042541119440, 876813875617680, 0, 0, 129835900812618000, 0] }

theorem case_52_28_15_checked :
    (Witness.linear .conditional case_52_28_15).check 52 28 15 = true := by
  change case_52_28_15.check 52 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_28_16 : Certificate := {
  objectiveScale := 3347190000000
  eta := 4180716006166299600
  rows := #[⟨.count 2, 1066651862060584800⟩, ⟨.count 3, 274562072767382400⟩, ⟨.count 4, 76474772346772800⟩, ⟨.count 5, 21790640695824000⟩, ⟨.count 6, 6373352805019200⟩, ⟨.count 7, 1924202774894400⟩, ⟨.count 8, 604171186819200⟩, ⟨.count 9, 199016687469600⟩, ⟨.count 10, 69712060017600⟩, ⟨.count 11, 26061709073400⟩, ⟨.count 12, 10601373182400⟩, ⟨.count 13, 5742410473800⟩, ⟨.count 14, 4497552259200⟩, ⟨.count 15, 4216455243000⟩, ⟨.path 14, 426237608160⟩, ⟨.privateRow 3 25, 26693534852384400⟩, ⟨.privateRow 6 18, 146363200663680⟩, ⟨.privateRow 7 16, 64777245733200⟩, ⟨.privateRow 7 17, 419428873543680⟩, ⟨.privateRow 8 14, 25700298624000⟩, ⟨.privateRow 8 15, 153229106830800⟩, ⟨.privateRow 8 16, 366775386737760⟩, ⟨.privateRow 9 12, 9615860429175⟩, ⟨.privateRow 9 13, 57009151999800⟩, ⟨.privateRow 9 14, 139346037530700⟩, ⟨.privateRow 9 15, 237077223463080⟩, ⟨.privateRow 10 10, 3454369999080⟩, ⟨.privateRow 10 11, 21756909053880⟩, ⟨.privateRow 10 12, 55368080848080⟩, ⟨.privateRow 10 13, 98702532288360⟩, ⟨.privateRow 10 14, 136500711066720⟩, ⟨.privateRow 11 8, 1180607468040⟩, ⟨.privateRow 11 9, 8522147634000⟩, ⟨.privateRow 11 10, 22758819133050⟩, ⟨.privateRow 11 11, 42307969275000⟩, ⟨.privateRow 11 12, 61955120927700⟩, ⟨.privateRow 11 13, 72860346599040⟩, ⟨.privateRow 12 6, 361410449400⟩, ⟨.privateRow 12 7, 3462435664380⟩, ⟨.privateRow 12 8, 9770781266400⟩, ⟨.privateRow 12 9, 18994126951800⟩, ⟨.privateRow 12 10, 29236296097800⟩, ⟨.privateRow 12 11, 17918132878800⟩, ⟨.privateRow 13 4, 59462830350⟩, ⟨.privateRow 13 5, 1488887492400⟩, ⟨.privateRow 13 6, 4437626082120⟩, ⟨.privateRow 13 7, 9042125631000⟩, ⟨.privateRow 13 8, 7556026799475⟩, ⟨.privateRow 14 3, 635814679500⟩, ⟨.privateRow 14 4, 2179414528200⟩, ⟨.privateRow 14 5, 2823017176980⟩, ⟨.privateRow 15 1, 332991849960⟩, ⟨.privateRow 15 2, 866715799950⟩, ⟨.privateRow 16 0, 309927479400⟩, ⟨.privateRow 17 0, 281097016200⟩, ⟨.privateRow 18 0, 620603802000⟩, ⟨.privateRow 18 8, 151703151600⟩, ⟨.privateRow 19 0, 1911459710160⟩, ⟨.privateRow 20 0, 7494135689040⟩, ⟨.privateRow 21 0, 35669203519950⟩, ⟨.privateRow 22 0, 233471150312400⟩, ⟨.privateRow 23 0, 2663300529489600⟩, ⟨.privateRow 24 0, 64318707787173840⟩, ⟨.hall 21 3, 5188247784720⟩, ⟨.hall 9 13, 132286128975⟩, ⟨.hall 8 14, 219991211440⟩, ⟨.hall 9 14, 57713365710⟩, ⟨.hall 8 15, 328903815240⟩, ⟨.hall 7 17, 6827706405520⟩, ⟨.hall 10 17, 174467548054800⟩, ⟨.hall 7 18, 4387414831800⟩, ⟨.hall 6 21, 16619645696799600⟩, ⟨.hall 5 22, 27527038137799200⟩, ⟨.hall 4 23, 36287469714295800⟩, ⟨.hall 3 24, 35496953693497296⟩, ⟨.assumptionRow 16, 3808020408192⟩]
  caps := #[0, 6437321724440880, 827841664540800, 0, 28125022951872, 1561828564296, 0, 1002701044800, 1076070205392, 539446672128, 0, 37003772364, 48308077692, 131052283740, 0, 0, 180379622808, 1473209892000, 66197738880, 8465035859280, 0, 168618053003400, 0, 12650677515075600, 0] }

theorem case_52_28_16_checked :
    (Witness.linear .conditional case_52_28_16).check 52 28 16 = true := by
  change case_52_28_16.check 52 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_28_17 : Certificate := {
  objectiveScale := 4710860000000
  eta := 3951006335497821600
  rows := #[⟨.count 2, 1098611468414460000⟩, ⟨.count 3, 308882331863305200⟩, ⟨.count 4, 88303977295934400⟩, ⟨.count 5, 25707767773287600⟩, ⟨.count 6, 7634916213724800⟩, ⟨.count 7, 2309680483110000⟩, ⟨.count 8, 758587147718400⟩, ⟨.count 9, 258890351920200⟩, ⟨.count 10, 91637627281200⟩, ⟨.count 11, 33571015077600⟩, ⟨.count 12, 12232353672000⟩, ⟨.count 13, 6625858239000⟩, ⟨.count 14, 3373164194400⟩, ⟨.count 15, 3373164194400⟩, ⟨.count 16, 2998368172800⟩, ⟨.count 18, 8191970186400⟩, ⟨.path 12, 53013214800⟩, ⟨.path 13, 542499948900⟩, ⟨.privateRow 3 25, 8171490260934000⟩, ⟨.privateRow 6 18, 83011964555520⟩, ⟨.privateRow 7 16, 17218307706600⟩, ⟨.privateRow 7 17, 500438356498080⟩, ⟨.privateRow 8 15, 160225299234000⟩, ⟨.privateRow 8 16, 498478708728000⟩, ⟨.privateRow 9 13, 47371540015800⟩, ⟨.privateRow 9 14, 175154674094400⟩, ⟨.privateRow 9 15, 362765069306640⟩, ⟨.privateRow 10 11, 14188371892695⟩, ⟨.privateRow 10 12, 61094428635240⟩, ⟨.privateRow 10 13, 140482918796220⟩, ⟨.privateRow 10 14, 228565605812544⟩, ⟨.privateRow 11 9, 4002286087800⟩, ⟨.privateRow 11 10, 21885410547000⟩, ⟨.privateRow 11 11, 56064513047400⟩, ⟨.privateRow 11 12, 102747652207200⟩, ⟨.privateRow 11 13, 146315012603760⟩, ⟨.privateRow 11 14, 58769354744100⟩, ⟨.privateRow 12 7, 931018029480⟩, ⟨.privateRow 12 8, 7803788592600⟩, ⟨.privateRow 12 9, 22655338363350⟩, ⟨.privateRow 12 10, 45055836025200⟩, ⟨.privateRow 12 11, 69832015337700⟩, ⟨.privateRow 12 12, 85701228976440⟩, ⟨.privateRow 13 5, 37067738400⟩, ⟨.privateRow 13 6, 2738688072120⟩, ⟨.privateRow 13 7, 9381913233000⟩, ⟨.privateRow 13 8, 20574139301100⟩, ⟨.privateRow 13 9, 34789396336200⟩, ⟨.privateRow 13 10, 12911928876000⟩, ⟨.privateRow 14 4, 671712350400⟩, ⟨.privateRow 14 5, 3999608973360⟩, ⟨.privateRow 14 6, 9798238850400⟩, ⟨.privateRow 14 7, 9727964596350⟩, ⟨.privateRow 15 2, 112438806480⟩, ⟨.privateRow 15 3, 1569032435880⟩, ⟨.privateRow 15 4, 4643722707624⟩, ⟨.privateRow 16 1, 671509538700⟩, ⟨.privateRow 16 2, 707001586200⟩, ⟨.privateRow 17 0, 234247513500⟩, ⟨.hall 9 12, 63572701500⟩, ⟨.hall 9 13, 280480575375⟩, ⟨.hall 10 13, 403522509390⟩, ⟨.hall 8 14, 159227068000⟩, ⟨.hall 8 15, 1612241751120⟩, ⟨.hall 11 16, 56748527035200⟩, ⟨.hall 7 18, 75445969478880⟩, ⟨.hall 7 20, 1557839663780400⟩, ⟨.hall 6 21, 27928288176843600⟩, ⟨.hall 5 22, 43519247994222000⟩, ⟨.hall 4 23, 56439488818112400⟩, ⟨.hall 3 24, 59466658458903696⟩, ⟨.hall 2 25, 35339949333612000⟩, ⟨.assumptionRow 17, 3572857549800⟩]
  caps := #[0, 20890931178335400, 514400155220000, 28272760870200, 102416760862416, 4372088821800, 4632313285600, 1362892148800, 1365775138000, 1016635678240, 144786549600, 95446711950, 933976052870, 0, 199693355400, 199693355400, 1889956347300, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_28_17_checked :
    (Witness.linear .conditional case_52_28_17).check 52 28 17 = true := by
  change case_52_28_17.check 52 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_28_18 : Certificate := {
  objectiveScale := 10838520000000
  eta := 12588089952632594400
  rows := #[⟨.count 2, 3275859651272208000⟩, ⟨.count 3, 890147672424410400⟩, ⟨.count 4, 244677765527395200⟩, ⟨.count 5, 68069810935526400⟩, ⟨.count 6, 19120058415057600⟩, ⟨.count 7, 5409430979752800⟩, ⟨.count 8, 1619118813312000⟩, ⟨.count 9, 490795390285200⟩, ⟨.count 10, 148419224553600⟩, ⟨.count 11, 43288940494800⟩, ⟨.count 12, 13047843916800⟩, ⟨.count 13, 4417238826000⟩, ⟨.count 14, 3373164194400⟩, ⟨.count 15, 3373164194400⟩, ⟨.count 16, 2998368172800⟩, ⟨.path 12, 1371783067200⟩, ⟨.path 13, 1214788711500⟩, ⟨.privateRow 3 25, 128927957450292000⟩, ⟨.privateRow 6 18, 166570060456800⟩, ⟨.privateRow 7 16, 34891724868000⟩, ⟨.privateRow 7 17, 1214232025406400⟩, ⟨.privateRow 8 15, 367300101168000⟩, ⟨.privateRow 8 16, 1238850769796640⟩, ⟨.privateRow 9 13, 101114612398800⟩, ⟨.privateRow 9 14, 413806040848200⟩, ⟨.privateRow 9 15, 967348531749600⟩, ⟨.privateRow 10 11, 27027478107630⟩, ⟨.privateRow 10 12, 133705803591360⟩, ⟨.privateRow 10 13, 352233301099680⟩, ⟨.privateRow 10 14, 666424806006960⟩, ⟨.privateRow 11 9, 6282295219200⟩, ⟨.privateRow 11 10, 42445649446200⟩, ⟨.privateRow 11 11, 128203186082400⟩, ⟨.privateRow 11 12, 270442100728800⟩, ⟨.privateRow 11 13, 436664136308400⟩, ⟨.privateRow 12 7, 910630773360⟩, ⟨.privateRow 12 8, 12594793780800⟩, ⟨.privateRow 12 9, 46516922713800⟩, ⟨.privateRow 12 10, 110489219953200⟩, ⟨.privateRow 12 11, 199330733586600⟩, ⟨.privateRow 12 12, 284279899337280⟩, ⟨.privateRow 12 13, 95939029424700⟩, ⟨.privateRow 13 6, 2847420104760⟩, ⟨.privateRow 13 7, 16362660745200⟩, ⟨.privateRow 13 8, 45752400609300⟩, ⟨.privateRow 13 9, 92334853789200⟩, ⟨.privateRow 13 10, 147331904227200⟩, ⟨.privateRow 13 11, 87733158836400⟩, ⟨.privateRow 14 4, 138723202800⟩, ⟨.privateRow 14 5, 4987464201720⟩, ⟨.privateRow 14 6, 18829038228000⟩, ⟨.privateRow 14 7, 44071996468500⟩, ⟨.privateRow 14 8, 64939147416000⟩, ⟨.privateRow 15 3, 623524290480⟩, ⟨.privateRow 15 4, 7184839734072⟩, ⟨.privateRow 15 5, 21225948023280⟩, ⟨.privateRow 15 6, 13661314987320⟩, ⟨.privateRow 16 2, 1618437366000⟩, ⟨.privateRow 16 3, 9725956760520⟩, ⟨.privateRow 16 4, 583016033600⟩, ⟨.privateRow 17 1, 2828006344800⟩, ⟨.privateRow 18 0, 496483041600⟩, ⟨.hall 10 13, 2101141142100⟩, ⟨.hall 9 14, 2857065431220⟩, ⟨.hall 10 14, 364231918050⟩, ⟨.hall 9 15, 4886889032025⟩, ⟨.hall 8 16, 9525775459200⟩, ⟨.hall 11 16, 1090538314866000⟩, ⟨.hall 8 17, 98066803714880⟩, ⟨.hall 7 20, 47788920004425600⟩, ⟨.hall 6 21, 80162151896736000⟩, ⟨.hall 5 22, 121247094969000000⟩, ⟨.hall 4 23, 153900723454077600⟩, ⟨.hall 3 24, 154059829719475680⟩, ⟨.assumptionRow 18, 3095977192000⟩]
  caps := #[0, 22672937874459600, 1911859925248000, 98464726729600, 244963384807680, 12389662747000, 0, 1392311138400, 796061200480, 950621351680, 791919216270, 0, 254037379400, 922990615020, 555625223660, 0, 1774287265800, 3095977192000, 4587272278400, 10838520000000, 0, 0, 0, 0, 0] }

theorem case_52_28_18_checked :
    (Witness.linear .conditional case_52_28_18).check 52 28 18 = true := by
  change case_52_28_18.check 52 28 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_29_1_checked :
    (Witness.rising).check 52 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_29_2_checked :
    (Witness.rising).check 52 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_29_3_checked :
    (Witness.rising).check 52 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_29_4_checked :
    (Witness.rising).check 52 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_29_5_checked :
    (Witness.rising).check 52 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_29_6_checked :
    (Witness.rising).check 52 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_29_7_checked :
    (Witness.rising).check 52 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_29_8_checked :
    (Witness.rising).check 52 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_29_9_checked :
    (Witness.rising).check 52 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_29_10_checked :
    (Witness.rising).check 52 29 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_29_11_checked :
    (Witness.linear .positive case_52_29_11).check 52 29 11 = true := by
  change case_52_29_11.check 52 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_29_12 : Certificate := {
  objectiveScale := 426043800000000
  eta := 665758549859162760000
  rows := #[⟨.count 2, 147054138735768264000⟩, ⟨.count 3, 22000764731105160000⟩, ⟨.count 4, 3314667744701913600⟩, ⟨.count 5, 558692366712480000⟩, ⟨.count 6, 99723583735776000⟩, ⟨.count 7, 20160278001864000⟩, ⟨.count 8, 4638100767300000⟩, ⟨.count 9, 1261563408705600⟩, ⟨.count 10, 503565226164000⟩, ⟨.count 11, 426093652908000⟩, ⟨.path 12, 85674094506000⟩, ⟨.path 13, 78367777488000⟩, ⟨.privateRow 5 21, 26943389943069600⟩, ⟨.privateRow 6 17, 2889294881616000⟩, ⟨.privateRow 6 18, 6800093770470000⟩, ⟨.privateRow 6 19, 8760857004900000⟩, ⟨.privateRow 6 20, 15944759748918000⟩, ⟨.privateRow 7 14, 1154371746528000⟩, ⟨.privateRow 7 15, 2029721240547000⟩, ⟨.privateRow 7 16, 2993625855792000⟩, ⟨.privateRow 7 17, 3869501211576000⟩, ⟨.privateRow 7 18, 4661070409195200⟩, ⟨.privateRow 7 19, 5070990172248000⟩, ⟨.privateRow 8 10, 38006659065375⟩, ⟨.privateRow 8 11, 326072538792000⟩, ⟨.privateRow 8 12, 645469023449250⟩, ⟨.privateRow 8 13, 967988808286500⟩, ⟨.privateRow 8 14, 1200108573538875⟩, ⟨.privateRow 8 15, 1352779390462500⟩, ⟨.privateRow 8 16, 1647814133715750⟩, ⟨.privateRow 8 17, 100492183291500⟩, ⟨.privateRow 9 7, 9423442828800⟩, ⟨.privateRow 9 8, 117974255414400⟩, ⟨.privateRow 9 9, 202015055642400⟩, ⟨.privateRow 9 10, 316702638252000⟩, ⟨.privateRow 9 11, 411451072512480⟩, ⟨.privateRow 9 12, 373338481516000⟩, ⟨.privateRow 10 4, 1822111015725⟩, ⟨.privateRow 10 5, 37281495691440⟩, ⟨.privateRow 10 6, 29911017193200⟩, ⟨.privateRow 10 7, 212027463648000⟩, ⟨.privateRow 11 2, 14510929356000⟩, ⟨.privateRow 11 3, 31600246986000⟩, ⟨.privateRow 12 0, 9032687086500⟩, ⟨.privateRow 13 0, 4557151368000⟩, ⟨.privateRow 14 0, 5466333047175⟩, ⟨.privateRow 15 0, 8520362891040⟩, ⟨.privateRow 16 0, 16012490744250⟩, ⟨.privateRow 17 0, 36697061016000⟩, ⟨.privateRow 18 0, 54233876697000⟩, ⟨.privateRow 18 2, 65080652036400⟩, ⟨.privateRow 19 0, 311294867083200⟩, ⟨.privateRow 19 2, 80099264044800⟩, ⟨.privateRow 19 4, 25746192014400⟩, ⟨.privateRow 20 0, 1797727857405480⟩, ⟨.privateRow 22 0, 119848523827032000⟩, ⟨.privateRow 23 0, 2825000918780040000⟩, ⟨.hall 20 1, 11414145126384000⟩, ⟨.hall 20 4, 45294226692000⟩, ⟨.hall 5 20, 3349718658000⟩, ⟨.hall 5 21, 271136404539000⟩, ⟨.hall 6 22, 10996235922672000⟩, ⟨.hall 4 24, 202304308220030016⟩, ⟨.hall 3 25, 140262283379988000⟩]
  caps := #[0, 186106668143760000, 33607557689706000, 10335535718508000, 0, 72089337640320, 93915386588400, 16308761742000, 6215867658000, 60698138191040, 8152668342000, 550318860000, 0, 896204232000, 0, 0, 0, 286780736088000, 226113547459800, 0, 0, 0, 1198485238270320000, 0] }

theorem case_52_29_12_checked :
    (Witness.linear .positive case_52_29_12).check 52 29 12 = true := by
  change case_52_29_12.check 52 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_29_13 : Certificate := {
  objectiveScale := 49231728000000
  eta := 95039879394836376000
  rows := #[⟨.count 2, 20339384025482121600⟩, ⟨.count 3, 3411480448364788800⟩, ⟨.count 4, 605406257503407360⟩, ⟨.count 5, 115867226316441600⟩, ⟨.count 6, 23642025957950400⟩, ⟨.count 7, 5291370232948800⟩, ⟨.count 8, 1300916990973600⟩, ⟨.count 9, 350809076217600⟩, ⟨.count 10, 119024508002400⟩, ⟨.count 11, 53006865912000⟩, ⟨.count 12, 47706179320800⟩, ⟨.path 13, 1651579675200⟩, ⟨.path 14, 12962858781600⟩, ⟨.privateRow 5 21, 7752880584408960⟩, ⟨.privateRow 6 17, 50712196392000⟩, ⟨.privateRow 6 18, 1782815437603200⟩, ⟨.privateRow 6 19, 2714454832209120⟩, ⟨.privateRow 6 20, 5271532814948400⟩, ⟨.privateRow 7 15, 410843367534600⟩, ⟨.privateRow 7 16, 749347278451200⟩, ⟨.privateRow 7 17, 1266114503253600⟩, ⟨.privateRow 7 18, 1771585834898880⟩, ⟨.privateRow 7 19, 2107986681200400⟩, ⟨.privateRow 7 20, 162875642529600⟩, ⟨.privateRow 8 12, 83499868662210⟩, ⟨.privateRow 8 13, 204841642305300⟩, ⟨.privateRow 8 14, 353092989474225⟩, ⟨.privateRow 8 15, 468789509588400⟩, ⟨.privateRow 8 16, 701009108900100⟩, ⟨.privateRow 8 17, 706368692008980⟩, ⟨.privateRow 8 18, 583768228393350⟩, ⟨.privateRow 9 9, 15104279670480⟩, ⟨.privateRow 9 10, 56076299304480⟩, ⟨.privateRow 9 11, 101052503343792⟩, ⟨.privateRow 9 12, 149526955017440⟩, ⟨.privateRow 9 13, 194650313817960⟩, ⟨.privateRow 9 14, 252109221043680⟩, ⟨.privateRow 9 15, 78932042148960⟩, ⟨.privateRow 10 6, 1342381669200⟩, ⟨.privateRow 10 7, 15661119474000⟩, ⟨.privateRow 10 8, 30695794169040⟩, ⟨.privateRow 10 9, 49659986113920⟩, ⟨.privateRow 10 10, 66904302392928⟩, ⟨.privateRow 10 11, 33828018063840⟩, ⟨.privateRow 11 4, 3341038821120⟩, ⟨.privateRow 11 5, 10119492583200⟩, ⟨.privateRow 11 6, 17644243478400⟩, ⟨.privateRow 11 7, 9035261235000⟩, ⟨.privateRow 12 2, 4141161399375⟩, ⟨.privateRow 12 3, 2738688072120⟩, ⟨.privateRow 13 0, 1388949962400⟩, ⟨.privateRow 14 0, 822208772385⟩, ⟨.privateRow 15 0, 1169363587392⟩, ⟨.privateRow 16 0, 2218658592150⟩, ⟨.privateRow 17 0, 5140059724800⟩, ⟨.privateRow 18 0, 13804986795600⟩, ⟨.privateRow 19 0, 50343380418240⟩, ⟨.privateRow 20 0, 141639164522856⟩, ⟨.privateRow 20 2, 50585415901020⟩, ⟨.privateRow 20 5, 40468332720816⟩, ⟨.privateRow 20 7, 67447221201360⟩, ⟨.privateRow 21 0, 1199061710246400⟩, ⟨.privateRow 22 0, 14163916452285600⟩, ⟨.privateRow 23 6, 2181243133651982400⟩, ⟨.hall 19 2, 4496481413424⟩, ⟨.hall 20 4, 21411816254400⟩, ⟨.hall 21 5, 252927079505100⟩, ⟨.hall 17 8, 35857108560⟩, ⟨.hall 19 9, 80936665441632⟩, ⟨.hall 6 17, 352944602400⟩, ⟨.hall 5 20, 19047140166600⟩, ⟨.hall 7 21, 457114856889600⟩, ⟨.hall 4 24, 77375452162200192⟩, ⟨.hall 3 25, 83271376944756000⟩]
  caps := #[0, 56926745549856000, 0, 552916613995200, 340421872190400, 45111032366400, 66652240151640, 5182707438480, 0, 953829656416, 1005825302352, 0, 2956966948845, 1088453620800, 0, 1754045381088, 4045789197450, 11243880648000, 0, 906180847528320, 0, 20833697215531200, 0, 0] }

theorem case_52_29_13_checked :
    (Witness.linear .positive case_52_29_13).check 52 29 13 = true := by
  change case_52_29_13.check 52 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_29_14 : Certificate := {
  objectiveScale := 96532800000000
  eta := 273174735309748272000
  rows := #[⟨.count 2, 59960579648009040000⟩, ⟨.count 3, 12437267589530784000⟩, ⟨.count 4, 2681701514966073600⟩, ⟨.count 5, 567266628840912000⟩, ⟨.count 6, 133001187070752000⟩, ⟨.count 7, 30500900237808000⟩, ⟨.count 8, 7795757249280000⟩, ⟨.count 9, 2017152188251200⟩, ⟨.count 10, 626444778960000⟩, ⟨.count 11, 212027463648000⟩, ⟨.count 12, 88344776520000⟩, ⟨.count 13, 104407463160000⟩, ⟨.path 15, 23694361891200⟩, ⟨.privateRow 3 26, 202341663604080000⟩, ⟨.privateRow 7 16, 1549207881936000⟩, ⟨.privateRow 7 17, 4696015676352000⟩, ⟨.privateRow 7 18, 7787404652227200⟩, ⟨.privateRow 7 22, 192610888037568000⟩, ⟨.privateRow 8 13, 47370052730000⟩, ⟨.privateRow 8 14, 1006444441752750⟩, ⟨.privateRow 8 15, 2075968392498000⟩, ⟨.privateRow 8 16, 4233867641503500⟩, ⟨.privateRow 8 17, 5983243688822400⟩, ⟨.privateRow 9 11, 126031408863360⟩, ⟨.privateRow 9 12, 414690975899200⟩, ⟨.privateRow 9 13, 921279854094600⟩, ⟨.privateRow 9 14, 1696505268057600⟩, ⟨.privateRow 9 15, 2630526699600800⟩, ⟨.privateRow 9 16, 3389205464124480⟩, ⟨.privateRow 9 18, 4634144587072000⟩, ⟨.privateRow 10 9, 3606803272800⟩, ⟨.privateRow 10 10, 384637094281440⟩, ⟨.privateRow 10 11, 276563769081600⟩, ⟨.privateRow 10 12, 726414924935700⟩, ⟨.privateRow 10 13, 1072413800172000⟩, ⟨.privateRow 10 14, 1472493255433200⟩, ⟨.privateRow 10 15, 1772421094604160⟩, ⟨.privateRow 10 18, 2897307102690000⟩, ⟨.privateRow 11 6, 9761171112000⟩, ⟨.privateRow 11 7, 30920671782000⟩, ⟨.privateRow 11 8, 71697992184000⟩, ⟨.privateRow 11 9, 121594537864800⟩, ⟨.privateRow 11 10, 562015558104000⟩, ⟨.privateRow 11 11, 326674889541000⟩, ⟨.privateRow 11 12, 659258553096000⟩, ⟨.privateRow 11 13, 92092736736000⟩, ⟨.privateRow 11 14, 2268693861033600⟩, ⟨.privateRow 12 5, 44398913328000⟩, ⟨.privateRow 12 6, 28343949133500⟩, ⟨.privateRow 12 7, 64384602282000⟩, ⟨.privateRow 12 8, 108075109942800⟩, ⟨.privateRow 12 10, 1103021345175750⟩, ⟨.privateRow 12 12, 182824606965000⟩, ⟨.privateRow 12 14, 954491689651500⟩, ⟨.privateRow 13 3, 25815032100000⟩, ⟨.privateRow 13 4, 28789276824000⟩, ⟨.privateRow 13 5, 37479602160000⟩, ⟨.privateRow 13 6, 53006865912000⟩, ⟨.privateRow 13 7, 101194925832000⟩, ⟨.privateRow 13 9, 793697503599000⟩, ⟨.privateRow 13 10, 238875097032000⟩, ⟨.privateRow 13 11, 182846916252000⟩, ⟨.privateRow 13 13, 276679777374000⟩, ⟨.privateRow 14 1, 4733138329920⟩, ⟨.privateRow 14 2, 8800057609200⟩, ⟨.privateRow 14 3, 97339881038400⟩, ⟨.privateRow 14 5, 38156181991200⟩, ⟨.privateRow 14 6, 139906000634400⟩, ⟨.privateRow 14 8, 632448208091700⟩, ⟨.privateRow 14 9, 482362479799200⟩, ⟨.privateRow 14 10, 226564195057200⟩, ⟨.privateRow 15 0, 1515841687360⟩, ⟨.privateRow 15 2, 140423576092800⟩, ⟨.privateRow 15 5, 256935166007520⟩, ⟨.privateRow 15 7, 562350197409000⟩, ⟨.privateRow 15 8, 726675943593600⟩, ⟨.privateRow 15 9, 473159155268800⟩, ⟨.privateRow 15 11, 401968733166000⟩, ⟨.privateRow 16 0, 31322238948000⟩, ⟨.privateRow 16 2, 304014231270750⟩, ⟨.privateRow 16 4, 375170817621600⟩, ⟨.privateRow 16 6, 586965706952625⟩, ⟨.privateRow 17 0, 130643184672000⟩, ⟨.privateRow 17 1, 458232754980000⟩, ⟨.privateRow 17 3, 796280919033600⟩, ⟨.privateRow 17 5, 946627665984000⟩, ⟨.privateRow 17 7, 1078877119320000⟩, ⟨.privateRow 18 0, 1097825140412000⟩, ⟨.privateRow 18 3, 933480059512000⟩, ⟨.privateRow 19 0, 6363919627228800⟩, ⟨.privateRow 19 3, 11909759322661200⟩, ⟨.privateRow 19 6, 5821760145801600⟩, ⟨.privateRow 19 10, 98259951729139200⟩, ⟨.privateRow 20 0, 37365760545553440⟩, ⟨.privateRow 20 3, 52416126190771200⟩, ⟨.privateRow 21 0, 298766209469728000⟩, ⟨.privateRow 21 4, 178959960254275200⟩, ⟨.privateRow 22 0, 3434749739679258000⟩, ⟨.privateRow 22 5, 2014423673213952000⟩, ⟨.hall 14 1, 15374965686080⟩, ⟨.hall 17 2, 730887396148000⟩, ⟨.hall 22 5, 29676777328598400000⟩, ⟨.hall 18 6, 57166475932800⟩, ⟨.hall 15 7, 9828254982000⟩, ⟨.hall 20 8, 398688018656928000⟩, ⟨.hall 13 9, 53455369500⟩, ⟨.hall 19 9, 62321232390056640⟩, ⟨.hall 12 10, 169374645000⟩, ⟨.hall 13 11, 1806096134700⟩, ⟨.hall 17 11, 28773536763972000⟩, ⟨.hall 16 12, 18972174613392000⟩, ⟨.hall 14 14, 6154750348306560⟩, ⟨.hall 13 15, 4332909721140000⟩, ⟨.hall 9 16, 7758045575280⟩, ⟨.hall 12 16, 6091632178632000⟩, ⟨.hall 6 17, 5060709056000⟩, ⟨.hall 11 17, 8684291531916000⟩, ⟨.hall 10 18, 9985749581808000⟩, ⟨.hall 9 19, 10133997189235920⟩, ⟨.hall 7 20, 4432782314688000⟩, ⟨.hall 8 20, 35301323377320000⟩, ⟨.hall 4 23, 29987034546124656⟩, ⟨.hall 5 23, 538128245997342000⟩, ⟨.hall 3 25, 649049797868472000⟩]
  caps := #[0, 0, 29044257933600000, 1746958329043200, 1110467069712000, 208785194217600, 177492687372000, 159405532000, 23578796040800, 17169211990840, 0, 4774356636000, 8581725018000, 41728200804000, 0, 3775846252360, 153674734838625, 3835574870400, 189146247654000, 0, 0, 0, 177048955653570000, 0] }

theorem case_52_29_14_checked :
    (Witness.linear .positive case_52_29_14).check 52 29 14 = true := by
  change case_52_29_14.check 52 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_29_15 : Certificate := {
  objectiveScale := 164560032000000
  eta := 807059959451233488000
  rows := #[⟨.count 2, 183281078892575664000⟩, ⟨.count 3, 39942244395445392000⟩, ⟨.count 4, 9671931520275024000⟩, ⟨.count 5, 2302435140589584000⟩, ⟨.count 6, 572946394836816000⟩, ⟨.count 7, 152894289051504000⟩, ⟨.count 8, 41658577800840000⟩, ⟨.count 9, 11664401784235200⟩, ⟨.count 10, 3821313151656000⟩, ⟨.count 11, 1378178513712000⟩, ⟨.count 12, 583075525032000⟩, ⟨.count 13, 501155823168000⟩, ⟨.count 14, 87702269054400⟩, ⟨.path 15, 54853122542400⟩, ⟨.privateRow 3 26, 1740138306995088000⟩, ⟨.privateRow 6 19, 51188891038084800⟩, ⟨.privateRow 6 20, 77327647465068000⟩, ⟨.privateRow 7 16, 2308896471024000⟩, ⟨.privateRow 7 17, 21222557011656000⟩, ⟨.privateRow 7 18, 53565204899606400⟩, ⟨.privateRow 7 19, 78096782443680000⟩, ⟨.privateRow 8 14, 2350146741067125⟩, ⟨.privateRow 8 15, 8318664627273000⟩, ⟨.privateRow 8 16, 20704434975724500⟩, ⟨.privateRow 8 17, 35099178927813000⟩, ⟨.privateRow 8 18, 45600612081774750⟩, ⟨.privateRow 9 12, 1363174774561600⟩, ⟨.privateRow 9 13, 3655479297670200⟩, ⟨.privateRow 9 14, 8065824553987200⟩, ⟨.privateRow 9 15, 13772504473728000⟩, ⟨.privateRow 9 16, 19070371171051200⟩, ⟨.privateRow 9 17, 21499236789030000⟩, ⟨.privateRow 10 10, 673428137382000⟩, ⟨.privateRow 10 11, 1657294465226400⟩, ⟨.privateRow 10 12, 3446229340253700⟩, ⟨.privateRow 10 13, 5605785850579200⟩, ⟨.privateRow 10 14, 7879631244685200⟩, ⟨.privateRow 10 15, 8421923608338240⟩, ⟨.privateRow 11 7, 29715970284000⟩, ⟨.privateRow 11 8, 288252212976000⟩, ⟨.privateRow 11 9, 768599555724000⟩, ⟨.privateRow 11 10, 1577891250936000⟩, ⟨.privateRow 11 11, 2532282548796000⟩, ⟨.privateRow 11 12, 3515663171592000⟩, ⟨.privateRow 11 13, 4313634497172000⟩, ⟨.privateRow 11 16, 2007835830000000⟩, ⟨.privateRow 12 5, 27862583364000⟩, ⟨.privateRow 12 6, 146505087729000⟩, ⟨.privateRow 12 7, 346150897092000⟩, ⟨.privateRow 12 8, 768599555724000⟩, ⟨.privateRow 12 9, 1265784325806000⟩, ⟨.privateRow 12 10, 1798920511888500⟩, ⟨.privateRow 12 11, 2278664200098000⟩, ⟨.privateRow 12 14, 765286626604500⟩, ⟨.privateRow 13 3, 19963624824000⟩, ⟨.privateRow 13 5, 352575971748000⟩, ⟨.privateRow 13 6, 290442579336000⟩, ⟨.privateRow 13 7, 696317465844000⟩, ⟨.privateRow 13 8, 1055318512248000⟩, ⟨.privateRow 13 9, 1426366573632000⟩, ⟨.privateRow 13 10, 1373359707720000⟩, ⟨.privateRow 14 0, 14878063500300⟩, ⟨.privateRow 14 2, 50115582316800⟩, ⟨.privateRow 14 3, 12528895579200⟩, ⟨.privateRow 14 4, 422328188482200⟩, ⟨.privateRow 14 5, 277913683756800⟩, ⟨.privateRow 14 7, 2480721324681600⟩, ⟨.privateRow 14 8, 656983961934300⟩, ⟨.privateRow 14 10, 645238122328800⟩, ⟨.privateRow 14 11, 912103598165760⟩, ⟨.privateRow 14 12, 277201814689800⟩, ⟨.privateRow 14 13, 286076449058400⟩, ⟨.privateRow 15 0, 79256865367680⟩, ⟨.privateRow 15 1, 48723482808000⟩, ⟨.privateRow 15 3, 537582426981600⟩, ⟨.privateRow 15 4, 346379668689600⟩, ⟨.privateRow 15 6, 2389616145716800⟩, ⟨.privateRow 15 7, 1559151449856000⟩, ⟨.privateRow 15 10, 1732607048652480⟩, ⟨.privateRow 16 0, 305391829743000⟩, ⟨.privateRow 16 2, 703445283040500⟩, ⟨.privateRow 16 3, 601292071926000⟩, ⟨.privateRow 16 4, 102319313896800⟩, ⟨.privateRow 16 5, 2631068071632000⟩, ⟨.privateRow 16 6, 2957667667329375⟩, ⟨.privateRow 16 8, 953153132431500⟩, ⟨.privateRow 17 0, 1243251945936000⟩, ⟨.privateRow 17 1, 616004032644000⟩, ⟨.privateRow 17 2, 1245296287872000⟩, ⟨.privateRow 17 3, 542918808432000⟩, ⟨.privateRow 17 4, 3614818391184000⟩, ⟨.privateRow 17 5, 5951225400120000⟩, ⟨.privateRow 17 6, 3484226199168000⟩, ⟨.privateRow 17 7, 1607874932664000⟩, ⟨.privateRow 17 8, 2305316786572800⟩, ⟨.privateRow 17 9, 1232008065288000⟩, ⟨.privateRow 17 10, 918785675808000⟩, ⟨.privateRow 18 0, 7247618067690000⟩, ⟨.privateRow 18 2, 1940586715267200⟩, ⟨.privateRow 18 3, 5969013338288000⟩, ⟨.privateRow 18 4, 12158249084982000⟩, ⟨.privateRow 18 5, 12001886479440000⟩, ⟨.privateRow 18 6, 6843329168676000⟩, ⟨.privateRow 18 9, 10018476131664000⟩, ⟨.privateRow 18 10, 29641278791124000⟩, ⟨.privateRow 19 0, 12856924845273600⟩, ⟨.privateRow 19 1, 17678271662251200⟩, ⟨.privateRow 19 3, 79126240030437600⟩, ⟨.privateRow 19 5, 32232672026755200⟩, ⟨.privateRow 19 8, 51117893963136000⟩, ⟨.privateRow 20 0, 137187647923566240⟩, ⟨.privateRow 20 3, 97991177088261600⟩, ⟨.privateRow 20 6, 867539882702493000⟩, ⟨.privateRow 21 0, 1098640292013264000⟩, ⟨.privateRow 21 5, 2333673853567056000⟩, ⟨.privateRow 21 6, 197845182190656000⟩, ⟨.privateRow 21 8, 10076614847483184000⟩, ⟨.privateRow 22 0, 12216377940096330000⟩, ⟨.privateRow 22 4, 3434749739679258000⟩, ⟨.privateRow 22 5, 18649156662176040000⟩, ⟨.privateRow 23 0, 184292787210596064000⟩, ⟨.privateRow 23 2, 200051155972081814400⟩, ⟨.hall 14 4, 7238917445760⟩, ⟨.hall 15 4, 23035352886000⟩, ⟨.hall 21 6, 333863744946732000⟩, ⟨.hall 16 9, 53766192916800⟩, ⟨.hall 18 10, 49375238487120000⟩, ⟨.hall 13 11, 524905652700⟩, ⟨.hall 15 11, 57557960460000⟩, ⟨.hall 9 19, 22043965326823440⟩, ⟨.hall 8 20, 122539559262120000⟩, ⟨.hall 7 21, 361293483836376000⟩, ⟨.hall 6 22, 882308431852848000⟩, ⟨.hall 5 23, 1890652105886544000⟩, ⟨.hall 4 24, 3151026258973617024⟩, ⟨.hall 3 25, 3013334313365376000⟩, ⟨.assumptionRow 15, 356546736000000⟩]
  caps := #[0, 0, 94089474709776000, 0, 1816409238134400, 1735264693169280, 0, 63595655323200, 1664180222250, 23327457753600, 81861719888520, 21230776224000, 71790059526000, 51716812680000, 63605099425140, 0, 277658230019625, 597930149294400, 288171629127200, 0, 69995762631039960, 0, 0, 0] }

theorem case_52_29_15_checked :
    (Witness.linear .conditional case_52_29_15).check 52 29 15 = true := by
  change case_52_29_15.check 52 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_29_16 : Certificate := {
  objectiveScale := 6216210000000
  eta := 13662731716281648000
  rows := #[⟨.count 2, 3453816550288104000⟩, ⟨.count 3, 879407999510040000⟩, ⟨.count 4, 224754894034070400⟩, ⟨.count 5, 58081068621576000⟩, ⟨.count 6, 16411246940088000⟩, ⟨.count 7, 4756161514104000⟩, ⟨.count 8, 1427972842296000⟩, ⟨.count 9, 448630837855200⟩, ⟨.count 10, 149382985752000⟩, ⟨.count 11, 53006865912000⟩, ⟨.count 12, 20387256120000⟩, ⟨.count 13, 9637611984000⟩, ⟨.count 14, 10119492583200⟩, ⟨.path 13, 1209407472000⟩, ⟨.privateRow 2 27, 38133621217692000⟩, ⟨.privateRow 5 21, 6279145147875600⟩, ⟨.privateRow 6 19, 2414810767168800⟩, ⟨.privateRow 6 20, 6422732180865000⟩, ⟨.privateRow 7 16, 67692750840000⟩, ⟨.privateRow 7 17, 829637764956000⟩, ⟨.privateRow 7 18, 2369567533132800⟩, ⟨.privateRow 7 19, 4277493452232000⟩, ⟨.privateRow 8 14, 44975522592000⟩, ⟨.privateRow 8 15, 309005934237000⟩, ⟨.privateRow 8 16, 863553458517750⟩, ⟨.privateRow 8 17, 1611529193874600⟩, ⟨.privateRow 8 18, 2296035565448625⟩, ⟨.privateRow 9 12, 21571593243200⟩, ⟨.privateRow 9 13, 119559930890400⟩, ⟨.privateRow 9 14, 331105513939200⟩, ⟨.privateRow 9 15, 628220598205200⟩, ⟨.privateRow 9 16, 945385484883840⟩, ⟨.privateRow 9 17, 1144627049966400⟩, ⟨.privateRow 9 18, 401781335155200⟩, ⟨.privateRow 10 10, 9107543324880⟩, ⟨.privateRow 10 11, 47572323598800⟩, ⟨.privateRow 10 12, 132788222617050⟩, ⟨.privateRow 10 13, 256980039544800⟩, ⟨.privateRow 10 14, 395623971943200⟩, ⟨.privateRow 10 15, 499999309729920⟩, ⟨.privateRow 10 16, 492843382831800⟩, ⟨.privateRow 11 8, 3571982064000⟩, ⟨.privateRow 11 9, 19460562660000⟩, ⟨.privateRow 11 10, 55807539480000⟩, ⟨.privateRow 11 11, 111527557911000⟩, ⟨.privateRow 11 12, 177633897804000⟩, ⟨.privateRow 11 13, 225896975766000⟩, ⟨.privateRow 12 6, 1302519141000⟩, ⟨.privateRow 12 7, 8232126903000⟩, ⟨.privateRow 12 8, 24685569285300⟩, ⟨.privateRow 12 9, 51628838415000⟩, ⟨.privateRow 12 10, 86518418159250⟩, ⟨.privateRow 12 11, 7281162900000⟩, ⟨.privateRow 13 4, 370677384000⟩, ⟨.privateRow 13 5, 3644994276000⟩, ⟨.privateRow 13 6, 11575243764000⟩, ⟨.privateRow 13 7, 25613807234400⟩, ⟨.privateRow 13 8, 8196088824000⟩, ⟨.privateRow 14 3, 1686582097200⟩, ⟨.privateRow 14 4, 5842802265300⟩, ⟨.privateRow 14 5, 4249310738400⟩, ⟨.privateRow 15 0, 499728028800⟩, ⟨.privateRow 15 1, 214169155200⟩, ⟨.privateRow 15 2, 1643336402400⟩, ⟨.privateRow 16 0, 552154853250⟩, ⟨.privateRow 17 0, 494236512000⟩, ⟨.privateRow 18 0, 1137773637000⟩, ⟨.privateRow 19 0, 4468347374400⟩, ⟨.privateRow 20 0, 7782371677080⟩, ⟨.privateRow 20 1, 8647079641200⟩, ⟨.privateRow 21 0, 172941592824000⟩, ⟨.privateRow 22 0, 1361915043489000⟩, ⟨.privateRow 23 0, 34242435379152000⟩, ⟨.hall 7 17, 1920690844800⟩, ⟨.hall 8 17, 3523223503800⟩, ⟨.hall 7 18, 3762818841600⟩, ⟨.hall 9 19, 97990419847320⟩, ⟨.hall 6 21, 1788364295172000⟩, ⟨.hall 5 23, 80144774990280000⟩, ⟨.hall 4 24, 140057786598073344⟩, ⟨.hall 3 25, 192703495604004000⟩, ⟨.hall 2 26, 161008622919144000⟩, ⟨.assumptionRow 16, 7341529366080⟩]
  caps := #[0, 0, 2182627065528000, 0, 111357125268480, 42399651752640, 0, 6795332734320, 3460891277025, 0, 0, 1627484733360, 945409111050, 0, 1928453698080, 185974474560, 0, 0, 19342151829000, 0, 1868633910463320, 0, 28600215913269000, 0] }

theorem case_52_29_16_checked :
    (Witness.linear .conditional case_52_29_16).check 52 29 16 = true := by
  change case_52_29_16.check 52 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_29_17 : Certificate := {
  objectiveScale := 2677752000000
  eta := 3315809159214552000
  rows := #[⟨.count 2, 860730307485048000⟩, ⟨.count 3, 228282902527680000⟩, ⟨.count 4, 61843913593862400⟩, ⟨.count 5, 17421589929744000⟩, ⟨.count 6, 4987999624608000⟩, ⟨.count 7, 1495436126184000⟩, ⟨.count 8, 470369007108000⟩, ⟨.count 9, 154041164877600⟩, ⟨.count 10, 53006865912000⟩, ⟨.count 11, 19028105712000⟩, ⟨.count 12, 7475327244000⟩, ⟨.count 13, 4015671660000⟩, ⟨.count 14, 2248776129600⟩, ⟨.count 15, 1873980108000⟩, ⟨.count 16, 3747960216000⟩, ⟨.path 12, 437010483000⟩, ⟨.privateRow 2 27, 83530789333992000⟩, ⟨.privateRow 5 21, 3007818386773200⟩, ⟨.privateRow 6 18, 8343673338000⟩, ⟨.privateRow 6 19, 950571947925600⟩, ⟨.privateRow 6 20, 2885014685553000⟩, ⟨.privateRow 7 16, 688400856000⟩, ⟨.privateRow 7 17, 303763251792000⟩, ⟨.privateRow 7 18, 984321437299200⟩, ⟨.privateRow 7 19, 2018945854926000⟩, ⟨.privateRow 8 15, 94000180774500⟩, ⟨.privateRow 8 16, 340791090890250⟩, ⟨.privateRow 8 17, 735630891395400⟩, ⟨.privateRow 8 18, 1241394697793250⟩, ⟨.privateRow 9 13, 28484497641600⟩, ⟨.privateRow 9 14, 118167831381600⟩, ⟨.privateRow 9 15, 275537541879600⟩, ⟨.privateRow 9 16, 482512398207840⟩, ⟨.privateRow 9 17, 692185785891600⟩, ⟨.privateRow 10 11, 8316902193600⟩, ⟨.privateRow 10 12, 41180712873300⟩, ⟨.privateRow 10 13, 105485957834400⟩, ⟨.privateRow 10 14, 196085247157800⟩, ⟨.privateRow 10 15, 292437272967840⟩, ⟨.privateRow 10 16, 353640124737900⟩, ⟨.privateRow 11 9, 2211708391200⟩, ⟨.privateRow 11 10, 14374045224000⟩, ⟨.privateRow 11 11, 41338250761500⟩, ⟨.privateRow 11 12, 83111164884000⟩, ⟨.privateRow 11 13, 131662547478000⟩, ⟨.privateRow 11 14, 169770241872000⟩, ⟨.privateRow 11 15, 71324506638000⟩, ⟨.privateRow 12 7, 422160354000⟩, ⟨.privateRow 12 8, 4966562115900⟩, ⟨.privateRow 12 9, 16567791779000⟩, ⟨.privateRow 12 10, 36746613374625⟩, ⟨.privateRow 12 11, 63119592162000⟩, ⟨.privateRow 12 12, 52563254320500⟩, ⟨.privateRow 13 6, 1578187044000⟩, ⟨.privateRow 13 7, 6771040214400⟩, ⟨.privateRow 13 8, 16913871744000⟩, ⟨.privateRow 13 9, 30202484350500⟩, ⟨.privateRow 14 4, 348024877200⟩, ⟨.privateRow 14 5, 2730656728800⟩, ⟨.privateRow 14 6, 8071500036600⟩, ⟨.privateRow 14 7, 5220373158000⟩, ⟨.privateRow 15 2, 48050772000⟩, ⟨.privateRow 15 3, 1009867058200⟩, ⟨.privateRow 15 4, 3055155448800⟩, ⟨.privateRow 16 1, 414437908500⟩, ⟨.privateRow 16 2, 448974400875⟩, ⟨.privateRow 17 0, 123559128000⟩, ⟨.hall 8 18, 2575196223600⟩, ⟨.hall 8 19, 182155328355000⟩, ⟨.hall 9 19, 1025329476291120⟩, ⟨.hall 7 21, 10540797383844000⟩, ⟨.hall 6 22, 22324108126320000⟩, ⟨.hall 5 23, 41812043386113000⟩, ⟨.hall 4 24, 70294531585614336⟩, ⟨.hall 3 25, 101869249773060000⟩, ⟨.hall 2 26, 103303778113536000⟩, ⟨.assumptionRow 17, 2282944563900⟩]
  caps := #[0, 0, 0, 0, 26104030923600, 10011172414320, 12439658431200, 658213264800, 0, 1622024487720, 135021127800, 0, 441787066075, 1194745708800, 71817946200, 1905075277700, 0, 1842706196100, 2677752000000, 0, 0, 0, 0, 0] }

theorem case_52_29_17_checked :
    (Witness.linear .conditional case_52_29_17).check 52 29 17 = true := by
  change case_52_29_17.check 52 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_29_18 : Certificate := {
  objectiveScale := 13127400000000
  eta := 18696369717016992000
  rows := #[⟨.count 2, 4695883069950072000⟩, ⟨.count 3, 1190702866593240000⟩, ⟨.count 4, 306625444076952000⟩, ⟨.count 5, 81182424547224000⟩, ⟨.count 6, 21599494724808000⟩, ⟨.count 7, 5970500624088000⟩, ⟨.count 8, 1686582097200000⟩, ⟨.count 9, 485735643993600⟩, ⟨.count 10, 139745373768000⟩, ⟨.count 11, 46890689076000⟩, ⟨.count 12, 20387256120000⟩, ⟨.count 13, 12047014980000⟩, ⟨.count 14, 6746328388800⟩, ⟨.count 15, 5621940324000⟩, ⟨.count 16, 11243880648000⟩, ⟨.path 11, 2278117062000⟩, ⟨.path 12, 1546302303000⟩, ⟨.privateRow 2 27, 441260474090436000⟩, ⟨.privateRow 5 21, 14745546335520000⟩, ⟨.privateRow 6 18, 39442819416000⟩, ⟨.privateRow 6 19, 4432766089752000⟩, ⟨.privateRow 6 20, 14371218808947000⟩, ⟨.privateRow 7 17, 1326777916464000⟩, ⟨.privateRow 7 18, 4682273155560000⟩, ⟨.privateRow 7 19, 10434321241344000⟩, ⟨.privateRow 8 15, 370746886009500⟩, ⟨.privateRow 8 16, 1526591045479500⟩, ⟨.privateRow 8 17, 3653277371043300⟩, ⟨.privateRow 8 18, 6805183076566875⟩, ⟨.privateRow 9 13, 97493815118700⟩, ⟨.privateRow 9 14, 486110440015200⟩, ⟨.privateRow 9 15, 1297668758786400⟩, ⟨.privateRow 9 16, 2557907888215680⟩, ⟨.privateRow 9 17, 4096989011115000⟩, ⟨.privateRow 10 11, 22139736418800⟩, ⟨.privateRow 10 12, 150527452175100⟩, ⟨.privateRow 10 13, 461538353905200⟩, ⟨.privateRow 10 14, 991509489570600⟩, ⟨.privateRow 10 15, 1689617944974960⟩, ⟨.privateRow 10 16, 2350734033047400⟩, ⟨.privateRow 10 17, 990505571655600⟩, ⟨.privateRow 11 9, 3113690025600⟩, ⟨.privateRow 11 10, 43636965372000⟩, ⟨.privateRow 11 11, 163352889661500⟩, ⟨.privateRow 11 12, 393288704424000⟩, ⟨.privateRow 11 13, 724828734630000⟩, ⟨.privateRow 11 14, 1083341722478400⟩, ⟨.privateRow 11 15, 1287686897343000⟩, ⟨.privateRow 11 16, 146541125808000⟩, ⟨.privateRow 12 8, 9853840458000⟩, ⟨.privateRow 12 9, 56121585597000⟩, ⟨.privateRow 12 10, 158489679607875⟩, ⟨.privateRow 12 11, 324302995566000⟩, ⟨.privateRow 12 12, 528992665047000⟩, ⟨.privateRow 12 13, 525719377814400⟩, ⟨.privateRow 13 6, 892995516000⟩, ⟨.privateRow 13 7, 16884354841200⟩, ⟨.privateRow 13 8, 63509391792000⟩, ⟨.privateRow 13 9, 150054838510500⟩, ⟨.privateRow 13 10, 273295139832000⟩, ⟨.privateRow 13 11, 72282089880000⟩, ⟨.privateRow 14 5, 3132223894800⟩, ⟨.privateRow 14 6, 23539867270920⟩, ⟨.privateRow 14 7, 70193940616800⟩, ⟨.privateRow 14 8, 99598696347150⟩, ⟨.privateRow 15 3, 93699005400⟩, ⟨.privateRow 15 4, 6746328388800⟩, ⟨.privateRow 15 5, 31145549394960⟩, ⟨.privateRow 15 6, 23403929348800⟩, ⟨.privateRow 16 2, 995551932375⟩, ⟨.privateRow 16 3, 11691080446500⟩, ⟨.privateRow 16 4, 3935358226800⟩, ⟨.privateRow 17 1, 3614104494000⟩, ⟨.privateRow 18 0, 758515758000⟩, ⟨.hall 8 18, 165781016200800⟩, ⟨.hall 9 18, 484750324978920⟩, ⟨.hall 10 18, 1264682951532000⟩, ⟨.hall 6 21, 6093573817968000⟩, ⟨.hall 7 21, 69125333881968000⟩, ⟨.hall 5 23, 236932257716154000⟩, ⟨.hall 4 24, 383614890603969024⟩, ⟨.hall 3 25, 544586424203052000⟩, ⟨.hall 2 26, 550011912377928000⟩, ⟨.assumptionRow 18, 6205690260000⟩]
  caps := #[0, 18507299468463000, 0, 468839227428000, 49988934210600, 101260588682880, 12894767886000, 11488312836000, 4097982049200, 0, 3674892829140, 0, 0, 0, 2187520244910, 583749936000, 0, 15778496844000, 0, 13127400000000, 0, 0, 0, 0] }

theorem case_52_29_18_checked :
    (Witness.linear .conditional case_52_29_18).check 52 29 18 = true := by
  change case_52_29_18.check 52 29 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_30_1_checked :
    (Witness.rising).check 52 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_30_2_checked :
    (Witness.rising).check 52 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_30_3_checked :
    (Witness.rising).check 52 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_30_4_checked :
    (Witness.rising).check 52 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_30_5_checked :
    (Witness.rising).check 52 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_30_6_checked :
    (Witness.rising).check 52 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_30_7_checked :
    (Witness.rising).check 52 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_30_8_checked :
    (Witness.rising).check 52 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_30_9_checked :
    (Witness.rising).check 52 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_30_10_checked :
    (Witness.rising).check 52 30 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_30_11_checked :
    (Witness.linear .positive case_52_30_11).check 52 30 11 = true := by
  change case_52_30_11.check 52 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_30_12_checked :
    (Witness.linear .positive case_52_30_12).check 52 30 12 = true := by
  change case_52_30_12.check 52 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_30_13 : Certificate := {
  objectiveScale := 7877076480000
  eta := 27591309249052348800
  rows := #[⟨.count 2, 5401173473804908800⟩, ⟨.count 3, 943721519049429120⟩, ⟨.count 4, 170052193917365760⟩, ⟨.count 5, 31759358193763200⟩, ⟨.count 6, 6197627013177600⟩, ⟨.count 7, 1278991423710000⟩, ⟨.count 8, 292340896848000⟩, ⟨.count 9, 75173373475200⟩, ⟨.count 10, 23130268761600⟩, ⟨.count 11, 8834477652000⟩, ⟨.count 12, 7710089587200⟩, ⟨.path 13, 1269084544000⟩, ⟨.path 14, 1444130688000⟩, ⟨.privateRow 6 18, 51308810467200⟩, ⟨.privateRow 6 19, 542454775262400⟩, ⟨.privateRow 6 21, 3050786073535200⟩, ⟨.privateRow 7 15, 7772555590800⟩, ⟨.privateRow 7 16, 122809278541950⟩, ⟨.privateRow 7 17, 227757423207600⟩, ⟨.privateRow 7 18, 397270397323800⟩, ⟨.privateRow 7 19, 332850992554080⟩, ⟨.privateRow 7 20, 1117681893127800⟩, ⟨.privateRow 8 13, 27821108683368⟩, ⟨.privateRow 8 14, 58793002588320⟩, ⟨.privateRow 8 16, 358604833466880⟩, ⟨.privateRow 8 17, 139917601463640⟩, ⟨.privateRow 8 18, 204443733862368⟩, ⟨.privateRow 8 19, 415733117059260⟩, ⟨.privateRow 8 21, 664588305501120⟩, ⟨.privateRow 9 10, 5614801352160⟩, ⟨.privateRow 9 11, 15616825398720⟩, ⟨.privateRow 9 12, 29261931674976⟩, ⟨.privateRow 9 13, 36658620398400⟩, ⟨.privateRow 9 14, 17366441372280⟩, ⟨.privateRow 9 15, 196763322000960⟩, ⟨.privateRow 9 16, 75358986743040⟩, ⟨.privateRow 9 17, 94050242814528⟩, ⟨.privateRow 9 20, 762452900969760⟩, ⟨.privateRow 10 7, 1184049472320⟩, ⟨.privateRow 10 8, 4270203463680⟩, ⟨.privateRow 10 9, 8497161232560⟩, ⟨.privateRow 10 10, 14018344704000⟩, ⟨.privateRow 10 11, 19795655015136⟩, ⟨.privateRow 10 12, 22701930451200⟩, ⟨.privateRow 10 13, 12528895579200⟩, ⟨.privateRow 10 14, 61212604115520⟩, ⟨.privateRow 10 16, 56090901746880⟩, ⟨.privateRow 10 17, 27033501615120⟩, ⟨.privateRow 10 19, 457593817000320⟩, ⟨.privateRow 11 6, 5931720709200⟩, ⟨.privateRow 11 7, 3039554548800⟩, ⟨.privateRow 11 8, 7254980132400⟩, ⟨.privateRow 11 9, 10207107237600⟩, ⟨.privateRow 11 10, 13171403044800⟩, ⟨.privateRow 11 12, 40036246450200⟩, ⟨.privateRow 11 14, 43717278805200⟩, ⟨.privateRow 12 4, 4101339322080⟩, ⟨.privateRow 12 5, 2397929648400⟩, ⟨.privateRow 12 6, 4596399561600⟩, ⟨.privateRow 12 7, 5314072163400⟩, ⟨.privateRow 12 8, 8031343320000⟩, ⟨.privateRow 12 9, 11227817961360⟩, ⟨.privateRow 12 11, 28129779978300⟩, ⟨.privateRow 12 13, 35659164340800⟩, ⟨.privateRow 12 14, 8834477652000⟩, ⟨.privateRow 13 2, 1421547767640⟩, ⟨.privateRow 13 3, 3443840015616⟩, ⟨.privateRow 13 4, 2684763338400⟩, ⟨.privateRow 13 5, 4522264084800⟩, ⟨.privateRow 13 7, 18066141737280⟩, ⟨.privateRow 13 8, 7864291378944⟩, ⟨.privateRow 13 10, 22359259802880⟩, ⟨.privateRow 13 13, 3777943897728⟩, ⟨.privateRow 13 14, 79221170508480⟩, ⟨.privateRow 14 0, 2063582801280⟩, ⟨.privateRow 14 2, 1874694005184⟩, ⟨.privateRow 14 3, 12866976888480⟩, ⟨.privateRow 14 6, 22071104939520⟩, ⟨.privateRow 14 8, 14694383704000⟩, ⟨.privateRow 14 11, 52482151481760⟩, ⟨.privateRow 15 0, 8008922486565⟩, ⟨.privateRow 15 2, 19280578196880⟩, ⟨.privateRow 15 6, 18173859087384⟩, ⟨.privateRow 15 8, 64741327781130⟩, ⟨.privateRow 15 10, 52864978846680⟩, ⟨.privateRow 15 13, 70649050071600⟩, ⟨.privateRow 16 0, 6194842814160⟩, ⟨.privateRow 16 2, 7147895554800⟩, ⟨.privateRow 16 3, 79697696878800⟩, ⟨.privateRow 16 6, 26565898959600⟩, ⟨.privateRow 16 8, 146170448424000⟩, ⟨.privateRow 16 10, 60556328632800⟩, ⟨.privateRow 17 0, 30825060552000⟩, ⟨.privateRow 17 2, 161715559605600⟩, ⟨.privateRow 17 4, 79628091903360⟩, ⟨.privateRow 17 6, 26449890667200⟩, ⟨.privateRow 17 8, 475633998840000⟩, ⟨.privateRow 18 0, 184956482430720⟩, ⟨.privateRow 18 6, 646411463343360⟩, ⟨.privateRow 19 0, 1373793400259280⟩, ⟨.privateRow 19 3, 1528803680564160⟩, ⟨.privateRow 19 5, 1229263640542080⟩, ⟨.privateRow 20 0, 10987765490257920⟩, ⟨.privateRow 20 2, 1858545650881920⟩, ⟨.privateRow 20 3, 4991094368900640⟩, ⟨.privateRow 20 5, 15153142363238880⟩, ⟨.privateRow 20 9, 43975588223286720⟩, ⟨.privateRow 21 0, 80666876556826560⟩, ⟨.privateRow 21 1, 88730566558233600⟩, ⟨.privateRow 21 4, 41817277144843200⟩, ⟨.privateRow 21 9, 64749332353305600⟩, ⟨.privateRow 22 0, 3216782803163529600⟩, ⟨.privateRow 22 3, 302163550982092800⟩, ⟨.privateRow 22 7, 283278329045712000⟩, ⟨.hall 12 1, 588965176800⟩, ⟨.hall 17 2, 127066559780160⟩, ⟨.hall 21 3, 117358164890366400⟩, ⟨.hall 18 4, 64542795408000⟩, ⟨.hall 20 5, 3618596946993600⟩, ⟨.hall 21 7, 91278572692507200⟩, ⟨.hall 13 10, 28051414560⟩, ⟨.hall 17 11, 100124080056000⟩, ⟨.hall 16 12, 28178541705600⟩, ⟨.hall 14 13, 1078877119320⟩, ⟨.hall 7 14, 1907942400⟩, ⟨.hall 10 14, 26199253080⟩, ⟨.hall 12 14, 147871203480⟩, ⟨.hall 15 14, 259208928538560⟩, ⟨.hall 11 15, 205134930000⟩, ⟨.hall 6 16, 15504871200⟩, ⟨.hall 7 21, 8232920514000⟩, ⟨.hall 5 22, 13458575946816⟩, ⟨.hall 4 25, 32309130415161600⟩]
  caps := #[0, 10632349830211200, 2349357752851200, 381806491946880, 0, 0, 0, 0, 6952730032248, 0, 0, 1302815306160, 174437244800, 2746442520256, 213651038952, 8806769517546, 0, 7504079256960, 16852052954880, 721127432694240, 100830189270720, 80337134586508800, 0] }

theorem case_52_30_13_checked :
    (Witness.linear .positive case_52_30_13).check 52 30 13 = true := by
  change case_52_30_13.check 52 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_30_14 : Certificate := {
  objectiveScale := 12871040000000
  eta := 56599010143333257600
  rows := #[⟨.count 2, 12431871811834675200⟩, ⟨.count 3, 2753465358324320640⟩, ⟨.count 4, 605235864523530240⟩, ⟨.count 5, 140574208398624000⟩, ⟨.count 6, 31272123365683200⟩, ⟨.count 7, 7739725244050800⟩, ⟨.count 8, 1870981739827200⟩, ⟨.count 9, 488626927588800⟩, ⟨.count 10, 132999045379200⟩, ⟨.count 11, 42405492729600⟩, ⟨.count 12, 17347701571200⟩, ⟨.count 13, 15034674695040⟩, ⟨.path 14, 3861334713600⟩, ⟨.privateRow 3 27, 506663525664616320⟩, ⟨.privateRow 6 24, 385764694883568000⟩, ⟨.privateRow 7 17, 995152277433600⟩, ⟨.privateRow 7 18, 1987396061250600⟩, ⟨.privateRow 7 19, 3525631215986880⟩, ⟨.privateRow 7 21, 19223502117019200⟩, ⟨.privateRow 8 14, 85915741351440⟩, ⟨.privateRow 8 15, 410008107829320⟩, ⟨.privateRow 8 16, 964307329745760⟩, ⟨.privateRow 8 17, 1857095547226920⟩, ⟨.privateRow 8 19, 8509678081124220⟩, ⟨.privateRow 8 20, 4975154829524880⟩, ⟨.privateRow 9 13, 309974157292800⟩, ⟨.privateRow 9 14, 306018274521960⟩, ⟨.privateRow 9 15, 791706877790400⟩, ⟨.privateRow 9 16, 1256091386790240⟩, ⟨.privateRow 9 17, 789153369548544⟩, ⟨.privateRow 10 9, 4144173153120⟩, ⟨.privateRow 10 10, 22552012042560⟩, ⟨.privateRow 10 11, 62451725656320⟩, ⟨.privateRow 10 12, 226805135356800⟩, ⟨.privateRow 10 13, 275467044532680⟩, ⟨.privateRow 10 14, 547278680520000⟩, ⟨.privateRow 10 15, 802813078267200⟩, ⟨.privateRow 10 16, 708133178136384⟩, ⟨.privateRow 10 18, 1035657783800640⟩, ⟨.privateRow 11 7, 4781738253600⟩, ⟨.privateRow 11 8, 14095007526600⟩, ⟨.privateRow 11 9, 30796551021600⟩, ⟨.privateRow 11 10, 58982185342080⟩, ⟨.privateRow 11 11, 192966408835200⟩, ⟨.privateRow 11 12, 211967228573100⟩, ⟨.privateRow 11 13, 374283545407200⟩, ⟨.privateRow 11 14, 522197942666400⟩, ⟨.privateRow 11 15, 506938390358400⟩, ⟨.privateRow 11 17, 484450629062400⟩, ⟨.privateRow 12 5, 3889464836400⟩, ⟨.privateRow 12 6, 8303173401600⟩, ⟨.privateRow 12 7, 16785507538800⟩, ⟨.privateRow 12 8, 29745175168800⟩, ⟨.privateRow 12 9, 58693056982560⟩, ⟨.privateRow 12 10, 162661473374400⟩, ⟨.privateRow 12 11, 174079366461000⟩, ⟨.privateRow 12 12, 272606738976000⟩, ⟨.privateRow 12 13, 369361479286800⟩, ⟨.privateRow 12 15, 736674966027000⟩, ⟨.privateRow 13 3, 3084035834880⟩, ⟨.privateRow 13 4, 5163006420000⟩, ⟨.privateRow 13 5, 10052770654080⟩, ⟨.privateRow 13 6, 17685017990640⟩, ⟨.privateRow 13 7, 33591458496960⟩, ⟨.privateRow 13 8, 59618267733024⟩, ⟨.privateRow 13 9, 153559284278400⟩, ⟨.privateRow 13 11, 599734825747200⟩, ⟨.privateRow 13 12, 174729905269920⟩, ⟨.privateRow 13 14, 867385078560⟩, ⟨.privateRow 14 0, 982658476800⟩, ⟨.privateRow 14 2, 6292289779776⟩, ⟨.privateRow 14 3, 5787156529440⟩, ⟨.privateRow 14 4, 12271892592960⟩, ⟨.privateRow 14 5, 23596086674160⟩, ⟨.privateRow 14 6, 41079590959680⟩, ⟨.privateRow 14 7, 69994763302464⟩, ⟨.privateRow 14 8, 166866327788160⟩, ⟨.privateRow 14 9, 51159656948400⟩, ⟨.privateRow 14 10, 349973816512320⟩, ⟨.privateRow 14 11, 682546389164640⟩, ⟨.privateRow 15 0, 6486313648815⟩, ⟨.privateRow 15 1, 5359583108880⟩, ⟨.privateRow 15 2, 7726152273840⟩, ⟨.privateRow 15 3, 24286782199680⟩, ⟨.privateRow 15 5, 60860059434720⟩, ⟨.privateRow 15 7, 198142163419200⟩, ⟨.privateRow 15 8, 617752857651930⟩, ⟨.privateRow 15 11, 1568701252486368⟩, ⟨.privateRow 16 0, 39048391221840⟩, ⟨.privateRow 16 2, 45055836025200⟩, ⟨.privateRow 16 4, 102509145648000⟩, ⟨.privateRow 16 5, 22552012042560⟩, ⟨.privateRow 16 6, 254754210110400⟩, ⟨.privateRow 16 7, 847658091530250⟩, ⟨.privateRow 16 8, 529345838221200⟩, ⟨.privateRow 17 0, 195689416665600⟩, ⟨.privateRow 17 2, 15313094596800⟩, ⟨.privateRow 17 3, 188313097190400⟩, ⟨.privateRow 17 4, 106077982570560⟩, ⟨.privateRow 17 5, 400924658534400⟩, ⟨.privateRow 17 6, 1384442961501600⟩, ⟨.privateRow 17 8, 2644989066720000⟩, ⟨.privateRow 18 0, 917500660876800⟩, ⟨.privateRow 18 2, 170392979877120⟩, ⟨.privateRow 18 3, 400423502711232⟩, ⟨.privateRow 18 4, 848809473832320⟩, ⟨.privateRow 18 5, 2775985630498080⟩, ⟨.privateRow 18 6, 2215108738402560⟩, ⟨.privateRow 18 8, 9275057871311232⟩, ⟨.privateRow 19 0, 5622968335944960⟩, ⟨.privateRow 19 3, 2612692358115840⟩, ⟨.privateRow 19 4, 7252351206019920⟩, ⟨.privateRow 19 5, 10132296839121600⟩, ⟨.privateRow 19 8, 52523636047122240⟩, ⟨.privateRow 20 0, 43852956912011520⟩, ⟨.privateRow 21 1, 499109436890064000⟩, ⟨.privateRow 22 7, 42151815362001945600⟩, ⟨.hall 11 9, 44934591240⟩, ⟨.hall 19 10, 8167245330928320⟩, ⟨.hall 10 11, 28028412720⟩, ⟨.hall 15 12, 16432128432720⟩, ⟨.hall 16 12, 118680307574400⟩, ⟨.hall 17 12, 1682084544940800⟩, ⟨.hall 13 15, 7489700077860⟩, ⟨.hall 12 16, 16440632208000⟩, ⟨.hall 12 17, 3113912432030400⟩, ⟨.hall 6 18, 623484669600⟩, ⟨.hall 9 18, 8446171260384⟩, ⟨.hall 10 18, 5904305447040⟩, ⟨.hall 6 21, 95229510667200⟩, ⟨.hall 8 21, 21507254016655680⟩, ⟨.hall 4 25, 386372635447518720⟩, ⟨.hall 3 26, 449828000598936960⟩]
  caps := #[0, 0, 5381603592019200, 1397313554232960, 181777260304640, 0, 75173373475200, 9476659107240, 0, 0, 2147669596800, 8775996757800, 0, 0, 22105438033120, 0, 80351947141830, 0, 478180470095328, 46470812693760, 6180618088270080, 0, 0] }

theorem case_52_30_14_checked :
    (Witness.linear .positive case_52_30_14).check 52 30 14 = true := by
  change case_52_30_14.check 52 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_30_15 : Certificate := {
  objectiveScale := 2920320000000
  eta := 12067656817347331200
  rows := #[⟨.count 2, 2956886177467622400⟩, ⟨.count 3, 717908222467275840⟩, ⟨.count 4, 187261884884954880⟩, ⟨.count 5, 49035313097971200⟩, ⟨.count 6, 12913115043628800⟩, ⟨.count 7, 3420388493121600⟩, ⟨.count 8, 912103598165760⟩, ⟨.count 9, 255589469815680⟩, ⟨.count 10, 77100895872000⟩, ⟨.count 11, 24736537425600⟩, ⟨.count 12, 9637611984000⟩, ⟨.count 13, 5011558231680⟩, ⟨.count 14, 3897878624640⟩, ⟨.path 14, 530975827200⟩, ⟨.privateRow 2 28, 207737441300188800⟩, ⟨.privateRow 3 27, 375815916533977920⟩, ⟨.privateRow 7 17, 242076161012400⟩, ⟨.privateRow 8 15, 117362689213770⟩, ⟨.privateRow 8 16, 364173231502080⟩, ⟨.privateRow 8 17, 554067205331640⟩, ⟨.privateRow 8 18, 985676057205840⟩, ⟨.privateRow 8 19, 1642834031578740⟩, ⟨.privateRow 8 21, 7066853946472320⟩, ⟨.privateRow 9 13, 49063773799040⟩, ⟨.privateRow 9 14, 142516187213400⟩, ⟨.privateRow 9 15, 352917112616640⟩, ⟨.privateRow 9 16, 527373697250400⟩, ⟨.privateRow 9 17, 854080890638976⟩, ⟨.privateRow 9 18, 1314281146258080⟩, ⟨.privateRow 9 19, 1384953397988160⟩, ⟨.privateRow 9 20, 1340452617023520⟩, ⟨.privateRow 10 11, 20797966661472⟩, ⟨.privateRow 10 12, 55876732591680⟩, ⟨.privateRow 10 13, 140492288696760⟩, ⟨.privateRow 10 14, 274727013612480⟩, ⟨.privateRow 10 16, 512489654861184⟩, ⟨.privateRow 11 8, 923604481800⟩, ⟨.privateRow 11 9, 7315823642400⟩, ⟨.privateRow 11 10, 23965528466880⟩, ⟨.privateRow 11 11, 58182620496000⟩, ⟨.privateRow 11 12, 118000511729100⟩, ⟨.privateRow 11 13, 206520256800000⟩, ⟨.privateRow 11 14, 92949413356800⟩, ⟨.privateRow 11 15, 275956956475200⟩, ⟨.privateRow 11 17, 202389851664000⟩, ⟨.privateRow 12 6, 778422506400⟩, ⟨.privateRow 12 7, 3440092055400⟩, ⟨.privateRow 12 8, 9360165578400⟩, ⟨.privateRow 12 9, 26712247882320⟩, ⟨.privateRow 12 10, 54327575702400⟩, ⟨.privateRow 12 12, 363842799091200⟩, ⟨.privateRow 12 13, 20881492632000⟩, ⟨.privateRow 12 14, 175854293334720⟩, ⟨.privateRow 12 16, 140066627500800⟩, ⟨.privateRow 13 4, 523184650560⟩, ⟨.privateRow 13 5, 1868214015360⟩, ⟨.privateRow 13 6, 4561803005760⟩, ⟨.privateRow 13 7, 11705317827840⟩, ⟨.privateRow 13 8, 28411680128832⟩, ⟨.privateRow 13 9, 53563705715520⟩, ⟨.privateRow 13 10, 13155340358160⟩, ⟨.privateRow 13 11, 257269167904320⟩, ⟨.privateRow 13 12, 160915994759520⟩, ⟨.privateRow 13 13, 101541879863424⟩, ⟨.privateRow 14 2, 389787862464⟩, ⟨.privateRow 14 3, 1113679607040⟩, ⟨.privateRow 14 4, 2591446777920⟩, ⟨.privateRow 14 5, 6403657740480⟩, ⟨.privateRow 14 7, 62449583964768⟩, ⟨.privateRow 14 8, 45568057254720⟩, ⟨.privateRow 14 9, 29860534463760⟩, ⟨.privateRow 14 10, 206269372932480⟩, ⟨.privateRow 14 11, 603243120480⟩, ⟨.privateRow 14 13, 6890892568560⟩, ⟨.privateRow 14 15, 2000307784194720⟩, ⟨.privateRow 15 1, 649646437440⟩, ⟨.privateRow 15 2, 1670519410560⟩, ⟨.privateRow 15 3, 4235195044080⟩, ⟨.privateRow 15 4, 9582284952240⟩, ⟨.privateRow 15 5, 797293355040⟩, ⟨.privateRow 15 6, 78055019458416⟩, ⟨.privateRow 15 8, 202019740592670⟩, ⟨.privateRow 15 9, 124453696086720⟩, ⟨.privateRow 15 10, 155021881134120⟩, ⟨.privateRow 15 12, 1461704484240⟩, ⟨.privateRow 16 0, 2853803993040⟩, ⟨.privateRow 16 1, 2833916857200⟩, ⟨.privateRow 16 2, 7870716453600⟩, ⟨.privateRow 16 3, 17053218982800⟩, ⟨.privateRow 16 4, 3986466775200⟩, ⟨.privateRow 16 5, 111820393044360⟩, ⟨.privateRow 16 6, 44547184281600⟩, ⟨.privateRow 16 8, 758743950135600⟩, ⟨.privateRow 16 9, 25927853351400⟩, ⟨.privateRow 16 10, 176239797814080⟩, ⟨.privateRow 17 0, 20682621273600⟩, ⟨.privateRow 17 2, 24129724819200⟩, ⟨.privateRow 17 3, 72136065456000⟩, ⟨.privateRow 17 4, 155636725083840⟩, ⟨.privateRow 17 5, 159936765788800⟩, ⟨.privateRow 17 7, 974867398876800⟩, ⟨.privateRow 17 8, 993959049283200⟩, ⟨.privateRow 17 10, 263802856917600⟩, ⟨.privateRow 17 11, 451968307190400⟩, ⟨.privateRow 18 0, 124517946833280⟩, ⟨.privateRow 18 2, 178138115326080⟩, ⟨.privateRow 18 4, 1162248412124800⟩, ⟨.privateRow 18 6, 1282004324789760⟩, ⟨.privateRow 18 7, 2925079487890560⟩, ⟨.privateRow 18 8, 1908401374623744⟩, ⟨.privateRow 19 0, 901662851849760⟩, ⟨.privateRow 19 3, 2896680657911040⟩, ⟨.privateRow 19 5, 6274112937618240⟩, ⟨.privateRow 20 1, 15377966433910080⟩, ⟨.privateRow 20 3, 9206545693985640⟩, ⟨.privateRow 20 5, 42806503055796480⟩, ⟨.privateRow 21 0, 76889832169550400⟩, ⟨.privateRow 21 2, 165920164155345600⟩, ⟨.privateRow 21 7, 640298953271577600⟩, ⟨.privateRow 22 0, 2303997076238457600⟩, ⟨.privateRow 22 6, 15240374102659305600⟩, ⟨.hall 14 1, 456782651325⟩, ⟨.hall 18 1, 31948683726960⟩, ⟨.hall 18 2, 84551061984480⟩, ⟨.hall 15 6, 9178678080⟩, ⟨.hall 17 7, 3767754637920⟩, ⟨.hall 21 8, 113311331618284800⟩, ⟨.hall 20 9, 37230866103150720⟩, ⟨.hall 14 10, 15900437280⟩, ⟨.hall 18 11, 227190639836160⟩, ⟨.hall 15 12, 985178113920⟩, ⟨.hall 14 14, 7308522421200⟩, ⟨.hall 12 15, 5384149570800⟩, ⟨.hall 14 15, 3688124031151560⟩, ⟨.hall 13 16, 2231912198355840⟩, ⟨.hall 12 17, 3148286581440000⟩, ⟨.hall 11 18, 5146129729540800⟩, ⟨.hall 10 19, 8151106711587840⟩, ⟨.hall 9 20, 14969047146768000⟩, ⟨.hall 8 21, 15948170392714560⟩, ⟨.hall 7 22, 31883905705251600⟩, ⟨.hall 6 23, 88632887576032800⟩, ⟨.hall 5 24, 143563658567801472⟩, ⟨.hall 4 25, 209019757700033280⟩, ⟨.hall 3 26, 254171106029480640⟩]
  caps := #[0, 16878103712121600, 3082108312483200, 94297566467520, 76660690179840, 43251970819200, 4677454349568, 0, 9356230905450, 869878638720, 5277090797784, 840834801720, 802957255920, 0, 0, 4341857919633, 534101714640, 81297004272640, 0, 47438954624880, 1629974512366200, 0, 0] }

theorem case_52_30_15_checked :
    (Witness.linear .positive case_52_30_15).check 52 30 15 = true := by
  change case_52_30_15.check 52 30 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_30_16 : Certificate := {
  objectiveScale := 2194133760000
  eta := 10367986843073059200
  rows := #[⟨.count 2, 2411912630160633600⟩, ⟨.count 3, 548750591694264960⟩, ⟨.count 4, 138359099660221440⟩, ⟨.count 5, 35025223641408000⟩, ⟨.count 6, 8920573652390400⟩, ⟨.count 7, 2302184562678000⟩, ⟨.count 8, 658741487564160⟩, ⟨.count 9, 195450771035520⟩, ⟨.count 10, 61680716697600⟩, ⟨.count 11, 21202746364800⟩, ⟨.count 12, 7710089587200⟩, ⟨.count 13, 2505779115840⟩, ⟨.count 14, 3897878624640⟩, ⟨.path 12, 455688874368⟩, ⟨.path 13, 285106407040⟩, ⟨.privateRow 2 28, 51259888113033600⟩, ⟨.privateRow 4 24, 16613315538019200⟩, ⟨.privateRow 5 21, 999638815279104⟩, ⟨.privateRow 5 22, 5686865703398880⟩, ⟨.privateRow 5 23, 13609350411296640⟩, ⟨.privateRow 6 19, 654286769136000⟩, ⟨.privateRow 6 20, 2102627098091520⟩, ⟨.privateRow 6 21, 4837545793080000⟩, ⟨.privateRow 6 22, 7860721893024000⟩, ⟨.privateRow 7 17, 310835933179200⟩, ⟨.privateRow 7 18, 813856175332200⟩, ⟨.privateRow 7 19, 1783697100625440⟩, ⟨.privateRow 7 20, 2880862927242300⟩, ⟨.privateRow 7 21, 3858203788639200⟩, ⟨.privateRow 8 15, 131370690521070⟩, ⟨.privateRow 8 16, 323732740771440⟩, ⟨.privateRow 8 17, 688462812077040⟩, ⟨.privateRow 8 18, 1102709862910656⟩, ⟨.privateRow 8 19, 1468282154419080⟩, ⟨.privateRow 8 20, 1578478431369840⟩, ⟨.privateRow 9 12, 3591616732704⟩, ⟨.privateRow 9 13, 49156580432960⟩, ⟨.privateRow 9 14, 131448996118440⟩, ⟨.privateRow 9 15, 279175612921920⟩, ⟨.privateRow 9 16, 448070428565760⟩, ⟨.privateRow 9 17, 598547104803648⟩, ⟨.privateRow 9 18, 655261238792160⟩, ⟨.privateRow 9 19, 431736460995840⟩, ⟨.privateRow 10 10, 2733577217280⟩, ⟨.privateRow 10 11, 20007682478784⟩, ⟨.privateRow 10 12, 52557110686080⟩, ⟨.privateRow 10 13, 119024508002400⟩, ⟨.privateRow 10 14, 195698595343680⟩, ⟨.privateRow 10 15, 266736974343840⟩, ⟨.privateRow 10 16, 190978919074944⟩, ⟨.privateRow 11 8, 1418870653200⟩, ⟨.privateRow 11 9, 8776067882400⟩, ⟨.privateRow 11 10, 22616262789120⟩, ⟨.privateRow 11 11, 51900325276800⟩, ⟨.privateRow 11 12, 92400604896600⟩, ⟨.privateRow 11 13, 90708286125600⟩, ⟨.privateRow 12 6, 617795640000⟩, ⟨.privateRow 12 7, 4042442804400⟩, ⟨.privateRow 12 8, 10309324334400⟩, ⟨.privateRow 12 9, 25298731458000⟩, ⟨.privateRow 12 10, 37747313604000⟩, ⟨.privateRow 13 4, 206520256800⟩, ⟨.privateRow 13 5, 1942349492160⟩, ⟨.privateRow 13 6, 5413125397680⟩, ⟨.privateRow 13 7, 12704124888000⟩, ⟨.privateRow 14 3, 974469656160⟩, ⟨.privateRow 14 4, 2976951257280⟩, ⟨.privateRow 14 5, 626444778960⟩, ⟨.privateRow 15 0, 152260883775⟩, ⟨.privateRow 15 1, 227376253104⟩, ⟨.privateRow 15 2, 452432340360⟩, ⟨.privateRow 16 0, 139209950880⟩, ⟨.privateRow 17 0, 198871358400⟩, ⟨.privateRow 18 0, 728175127680⟩, ⟨.privateRow 19 0, 3549853747440⟩, ⟨.privateRow 20 0, 24526262255040⟩, ⟨.privateRow 21 0, 269788884805440⟩, ⟨.hall 7 21, 113542084492200⟩, ⟨.hall 7 22, 605336313582000⟩, ⟨.hall 6 23, 11036564905766400⟩, ⟨.hall 5 24, 27626381804077056⟩, ⟨.hall 4 25, 57311023424054400⟩, ⟨.hall 3 26, 101050925631015360⟩, ⟨.hall 2 27, 125644537780819200⟩, ⟨.assumptionRow 16, 2725927986600⟩]
  caps := #[0, 0, 0, 291841910530560, 2068181775296, 0, 1279044154752, 5980393199352, 0, 5421989587456, 0, 0, 926264340288, 624008990800, 46136432160, 2862003581346, 11180766051000, 5376075494400, 12378977170560, 63897367453920, 465998982845760, 0, 0] }

theorem case_52_30_16_checked :
    (Witness.linear .conditional case_52_30_16).check 52 30 16 = true := by
  change case_52_30_16.check 52 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_30_17 : Certificate := {
  objectiveScale := 83720000000
  eta := 303253083016884000
  rows := #[⟨.count 2, 68657812351128000⟩, ⟨.count 3, 16965570256034400⟩, ⟨.count 4, 4221595302724800⟩, ⟨.count 5, 1058887998168000⟩, ⟨.count 6, 270923981328000⟩, ⟨.count 7, 71211244104000⟩, ⟨.count 8, 19614325130400⟩, ⟨.count 9, 5782567190400⟩, ⟨.count 10, 1791607356000⟩, ⟨.count 11, 622943937000⟩, ⟨.count 12, 247118256000⟩, ⟨.count 13, 160626866400⟩, ⟨.count 14, 124932007200⟩, ⟨.path 11, 38581215624⟩, ⟨.privateRow 2 28, 5361189377544000⟩, ⟨.privateRow 4 23, 90794336232600⟩, ⟨.privateRow 4 24, 711791187307200⟩, ⟨.privateRow 5 21, 55341309703680⟩, ⟨.privateRow 5 22, 239918534255400⟩, ⟨.privateRow 5 23, 589619582552000⟩, ⟨.privateRow 6 19, 24094029960000⟩, ⟨.privateRow 6 20, 83686597394400⟩, ⟨.privateRow 6 21, 205022347530000⟩, ⟨.privateRow 6 22, 359447232144000⟩, ⟨.privateRow 7 17, 9135653026500⟩, ⟨.privateRow 7 18, 29821939397250⟩, ⟨.privateRow 7 19, 73259236650600⟩, ⟨.privateRow 7 20, 130567890828375⟩, ⟨.privateRow 7 21, 193711539021000⟩, ⟨.privateRow 8 15, 3197478559275⟩, ⟨.privateRow 8 16, 10755307262700⟩, ⟨.privateRow 8 17, 27016546557000⟩, ⟨.privateRow 8 18, 49282553540220⟩, ⟨.privateRow 8 19, 74057351393025⟩, ⟨.privateRow 8 20, 92611055837300⟩, ⟨.privateRow 9 13, 1050023774800⟩, ⟨.privateRow 9 14, 3899663367600⟩, ⟨.privateRow 9 15, 10287768348000⟩, ⟨.privateRow 9 16, 19481956694200⟩, ⟨.privateRow 9 17, 30003313900560⟩, ⟨.privateRow 9 18, 38369742711300⟩, ⟨.privateRow 9 19, 37970406474000⟩, ⟨.privateRow 10 11, 321253732800⟩, ⟨.privateRow 10 12, 1412692696800⟩, ⟨.privateRow 10 13, 4036522262850⟩, ⟨.privateRow 10 14, 8103713666400⟩, ⟨.privateRow 10 15, 13006657540800⟩, ⟨.privateRow 10 16, 17303220285120⟩, ⟨.privateRow 10 17, 15157616027400⟩, ⟨.privateRow 11 9, 86116968000⟩, ⟨.privateRow 11 10, 507107254500⟩, ⟨.privateRow 11 11, 1624573720000⟩, ⟨.privateRow 11 12, 3546533095875⟩, ⟨.privateRow 11 13, 6067635750000⟩, ⟨.privateRow 11 14, 8568482307000⟩, ⟨.privateRow 11 15, 201813242400⟩, ⟨.privateRow 12 7, 15444891000⟩, ⟨.privateRow 12 8, 176914206000⟩, ⟨.privateRow 12 9, 666704461500⟩, ⟨.privateRow 12 10, 1626289819000⟩, ⟨.privateRow 12 11, 3043930601250⟩, ⟨.privateRow 12 12, 1440787689000⟩, ⟨.privateRow 13 6, 53542288800⟩, ⟨.privateRow 13 7, 275761508400⟩, ⟨.privateRow 13 8, 775333528200⟩, ⟨.privateRow 13 9, 1059176302800⟩, ⟨.privateRow 14 4, 10296594000⟩, ⟨.privateRow 14 5, 107084577600⟩, ⟨.privateRow 14 6, 379663502400⟩, ⟨.privateRow 14 7, 107084577600⟩, ⟨.privateRow 15 2, 1115464350⟩, ⟨.privateRow 15 3, 37239348300⟩, ⟨.privateRow 15 4, 109315506300⟩, ⟨.privateRow 16 1, 14341684500⟩, ⟨.privateRow 16 2, 15444891000⟩, ⟨.privateRow 17 0, 6374082000⟩, ⟨.hall 8 21, 43112899939200⟩, ⟨.hall 7 22, 231477282036000⟩, ⟨.hall 6 23, 638023298913000⟩, ⟨.hall 5 24, 1414298141736480⟩, ⟨.hall 4 25, 2740319052609600⟩, ⟨.hall 3 26, 4733795710243600⟩, ⟨.hall 2 27, 6689133751014000⟩, ⟨.assumptionRow 17, 77783448288⟩]
  caps := #[0, 32783828903280, 32200332484320, 10823624019824, 0, 1980681943520, 0, 45088218721, 0, 14001946640, 28789102440, 110895562222, 27192417000, 0, 159134473680, 78838738888, 77783448288, 0, 83720000000, 0, 0, 0, 0] }

theorem case_52_30_17_checked :
    (Witness.linear .conditional case_52_30_17).check 52 30 17 = true := by
  change case_52_30_17.check 52 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_30_18 : Certificate := {
  objectiveScale := 425013507864000000
  eta := 1869843244085589939566400
  rows := #[⟨.count 2, 395973134123721535180800⟩, ⟨.count 3, 90546574012258606482240⟩, ⟨.count 4, 20523550315565887349760⟩, ⟨.count 5, 4615533528473012745600⟩, ⟨.count 6, 1037703857177440252800⟩, ⟨.count 7, 236835501111424215000⟩, ⟨.count 8, 55966050724176552960⟩, ⟨.count 9, 14241361121777069280⟩, ⟨.count 10, 4036013273378116800⟩, ⟨.count 11, 2114102190817108800⟩, ⟨.count 12, 960955541280504000⟩, ⟨.count 13, 499696881465862080⟩, ⟨.count 14, 388653130029003840⟩, ⟨.path 10, 455885346403594800⟩, ⟨.privateRow 2 28, 28783373200569432244800⟩, ⟨.privateRow 4 23, 521371233699443847720⟩, ⟨.privateRow 4 24, 3724990402887268875360⟩, ⟨.privateRow 5 21, 296942095717302619584⟩, ⟨.privateRow 5 22, 1212403439125477478880⟩, ⟨.privateRow 5 23, 3129564554036881920960⟩, ⟨.privateRow 6 19, 118631741118376886400⟩, ⟨.privateRow 6 20, 405420736495969434240⟩, ⟨.privateRow 6 21, 1053596994101840588400⟩, ⟨.privateRow 6 22, 1986295103826801768000⟩, ⟨.privateRow 7 17, 40169085620217067800⟩, ⟨.privateRow 7 18, 136479710750363580600⟩, ⟨.privateRow 7 19, 362176135545777953400⟩, ⟨.privateRow 7 20, 704702732263080601050⟩, ⟨.privateRow 7 21, 1145589801932812836600⟩, ⟨.privateRow 8 15, 12005738094802196745⟩, ⟨.privateRow 8 16, 45451595509999038360⟩, ⟨.privateRow 8 17, 127138155160737881160⟩, ⟨.privateRow 8 18, 257968515056751298800⟩, ⟨.privateRow 8 19, 431587155486895357950⟩, ⟨.privateRow 8 20, 606833280899035870680⟩, ⟨.privateRow 9 13, 3084548651023840000⟩, ⟨.privateRow 9 14, 14695946479221707700⟩, ⟨.privateRow 9 15, 45301884737972559840⟩, ⟨.privateRow 9 16, 97866559599684395520⟩, ⟨.privateRow 9 17, 170529889081583199168⟩, ⟨.privateRow 9 18, 248314648916209435560⟩, ⟨.privateRow 9 19, 289907474063777650080⟩, ⟨.privateRow 10 11, 574651413685741392⟩, ⟨.privateRow 10 12, 4475917365608747520⟩, ⟨.privateRow 10 13, 16175284148604083580⟩, ⟨.privateRow 10 14, 38419002540394549920⟩, ⟨.privateRow 10 15, 71059459092555669120⟩, ⟨.privateRow 10 16, 108576444698201585952⟩, ⟨.privateRow 10 17, 136042475979080951280⟩, ⟨.privateRow 10 18, 116141086719161713440⟩, ⟨.privateRow 11 10, 1183576908343820760⟩, ⟨.privateRow 11 11, 5655401315165632800⟩, ⟨.privateRow 11 12, 15459372270350108100⟩, ⟨.privateRow 11 13, 31226479112848377600⟩, ⟨.privateRow 11 14, 51010723316306754000⟩, ⟨.privateRow 11 15, 68993404678802585520⟩, ⟨.privateRow 11 16, 8888838756844662000⟩, ⟨.privateRow 12 8, 126671412259702800⟩, ⟨.privateRow 12 9, 1833823491276961800⟩, ⟨.privateRow 12 10, 6249770112920611200⟩, ⟨.privateRow 12 11, 14350269416455526400⟩, ⟨.privateRow 12 12, 25730728612477495200⟩, ⟨.privateRow 12 13, 19744967052366355800⟩, ⟨.privateRow 13 7, 379140640832489760⟩, ⟨.privateRow 13 8, 2429295608357114112⟩, ⟨.privateRow 13 9, 6758720640339544800⟩, ⟨.privateRow 13 10, 13796919183934836180⟩, ⟨.privateRow 13 11, 442039548989031840⟩, ⟨.privateRow 14 5, 48581641253625480⟩, ⟨.privateRow 14 6, 699070889727493920⟩, ⟨.privateRow 14 7, 3117553321589795088⟩, ⟨.privateRow 14 8, 4108618803163754880⟩, ⟨.privateRow 15 4, 165987274283220390⟩, ⟨.privateRow 15 5, 1135043800198340760⟩, ⟨.privateRow 15 6, 1093086928206573300⟩, ⟨.privateRow 16 2, 24023888532012600⟩, ⟨.privateRow 16 3, 381712895564200200⟩, ⟨.privateRow 16 4, 208207033944109200⟩, ⟨.privateRow 17 1, 128127405504067200⟩, ⟨.hall 8 20, 10048618264494482400⟩, ⟨.hall 8 21, 351854745035803158240⟩, ⟨.hall 7 22, 1811894555459400211800⟩, ⟨.hall 6 23, 4257001016021256703200⟩, ⟨.hall 5 24, 8626045177242303370560⟩, ⟨.hall 4 25, 15791920544965639314240⟩, ⟨.hall 3 26, 26365330737510172568160⟩, ⟨.hall 2 27, 36699761557468368216000⟩, ⟨.assumptionRow 18, 253929629364640320⟩]
  caps := #[0, 2887067143047134502000, 0, 40168450299218687760, 2542456972623615432, 2809261929126757968, 1051691580881230800, 0, 270311110391103705, 5042572756908720, 47907127643732940, 103678274500684680, 71908500477631560, 124956235188680784, 0, 563596979060251500, 748918348568488560, 253929629364640320, 4421218957139359680, 425013507864000000, 0, 0, 0] }

theorem case_52_30_18_checked :
    (Witness.linear .conditional case_52_30_18).check 52 30 18 = true := by
  change case_52_30_18.check 52 30 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_30_19 : Certificate := {
  objectiveScale := 260260000000
  eta := 1019801984564563200
  rows := #[⟨.count 2, 245957533314292800⟩, ⟨.count 3, 62860810159667520⟩, ⟨.count 4, 16173133673336640⟩, ⟨.count 5, 4173050294212800⟩, ⟨.count 6, 1077485019811200⟩, ⟨.count 7, 277723852005600⟩, ⟨.count 8, 70811461680960⟩, ⟨.count 9, 17749268737200⟩, ⟨.count 10, 4176298526400⟩, ⟨.count 11, 883447765200⟩, ⟨.count 12, 160626866400⟩, ⟨.path 12, 122824956072⟩, ⟨.privateRow 2 28, 26754064409872800⟩, ⟨.privateRow 4 23, 188142248614320⟩, ⟨.privateRow 4 24, 2893130804163600⟩, ⟨.privateRow 5 21, 113753091195744⟩, ⟨.privateRow 5 22, 911523556703760⟩, ⟨.privateRow 5 23, 2541695283167040⟩, ⟨.privateRow 6 19, 48027433053600⟩, ⟨.privateRow 6 20, 292062476946240⟩, ⟨.privateRow 6 21, 844192343794800⟩, ⟨.privateRow 6 22, 1686064521741600⟩, ⟨.privateRow 7 17, 17438532239700⟩, ⟨.privateRow 7 18, 94387246903950⟩, ⟨.privateRow 7 19, 283483663723260⟩, ⟨.privateRow 7 20, 591120253924200⟩, ⟨.privateRow 7 21, 1014724533622800⟩, ⟨.privateRow 8 15, 5775762857865⟩, ⟨.privateRow 8 16, 30510180901200⟩, ⟨.privateRow 8 17, 96323618651260⟩, ⟨.privateRow 8 18, 211630447576548⟩, ⟨.privateRow 8 19, 376906591696635⟩, ⟨.privateRow 8 20, 565246537775920⟩, ⟨.privateRow 9 13, 1771059930640⟩, ⟨.privateRow 9 14, 9764998012770⟩, ⟨.privateRow 9 15, 33062363334000⟩, ⟨.privateRow 9 16, 77578612070960⟩, ⟨.privateRow 9 17, 145209899762928⟩, ⟨.privateRow 9 18, 227109434031480⟩, ⟨.privateRow 9 19, 290933329566880⟩, ⟨.privateRow 10 11, 497943285840⟩, ⟨.privateRow 10 12, 3051910461600⟩, ⟨.privateRow 10 13, 11402499678570⟩, ⟨.privateRow 10 14, 29133124225920⟩, ⟨.privateRow 10 15, 58256687328840⟩, ⟨.privateRow 10 16, 96273318645504⟩, ⟨.privateRow 10 17, 131866625971080⟩, ⟨.privateRow 10 18, 136859444401680⟩, ⟨.privateRow 11 9, 122903890200⟩, ⟨.privateRow 11 10, 907541795160⟩, ⟨.privateRow 11 11, 3905612510800⟩, ⟨.privateRow 11 12, 11170260000900⟩, ⟨.privateRow 11 13, 24375126976200⟩, ⟨.privateRow 11 14, 43277785851300⟩, ⟨.privateRow 11 15, 63972326658240⟩, ⟨.privateRow 11 16, 57337098518700⟩, ⟨.privateRow 12 7, 23424751350⟩, ⟨.privateRow 12 8, 242157169800⟩, ⟨.privateRow 12 9, 1297061946180⟩, ⟨.privateRow 12 10, 4330976249600⟩, ⟨.privateRow 12 11, 10608065968500⟩, ⟨.privateRow 12 12, 20665411252200⟩, ⟨.privateRow 12 13, 33376924280700⟩, ⟨.privateRow 12 14, 9158408499240⟩, ⟨.privateRow 13 5, 2471182560⟩, ⟨.privateRow 13 6, 49526617140⟩, ⟨.privateRow 13 7, 397186433280⟩, ⟨.privateRow 13 8, 1662488067240⟩, ⟨.privateRow 13 9, 4756339988400⟩, ⟨.privateRow 13 10, 10444761987660⟩, ⟨.privateRow 13 11, 12902926710960⟩, ⟨.privateRow 14 4, 3569485920⟩, ⟨.privateRow 14 5, 94740105460⟩, ⟨.privateRow 14 6, 601133878800⟩, ⟨.privateRow 14 7, 2150793741096⟩, ⟨.privateRow 14 8, 5529728604400⟩, ⟨.privateRow 14 9, 2543481810870⟩, ⟨.privateRow 15 3, 6246600360⟩, ⟨.privateRow 15 4, 175945910140⟩, ⟨.privateRow 15 5, 933866753820⟩, ⟨.privateRow 15 6, 2533621106016⟩, ⟨.privateRow 16 2, 6692786100⟩, ⟨.privateRow 16 3, 340774358925⟩, ⟨.privateRow 16 4, 783055973700⟩, ⟨.privateRow 17 1, 17847429600⟩, ⟨.privateRow 17 2, 290020731000⟩, ⟨.privateRow 18 0, 60681260640⟩, ⟨.hall 9 20, 100439979559920⟩, ⟨.hall 8 21, 678762409590720⟩, ⟨.hall 7 22, 1855914532371900⟩, ⟨.hall 6 23, 4042656973555200⟩, ⟨.hall 5 24, 7791534547436640⟩, ⟨.hall 4 25, 13698612545698080⟩, ⟨.hall 3 26, 22035256971007280⟩, ⟨.hall 2 27, 29789189363934000⟩]
  caps := #[0, 163699703010480, 0, 0, 0, 0, 1424581830672, 149968393536, 104415518207, 279343077104, 10545343770, 0, 49243861342, 1219595160, 17564987440, 0, 378431128075, 71389718400, 886206441120, 2602600000000, 260260000000, 0, 0] }

theorem case_52_30_19_checked :
    (Witness.linear .conditional case_52_30_19).check 52 30 19 = true := by
  change case_52_30_19.check 52 30 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_31_1_checked :
    (Witness.rising).check 52 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_31_2_checked :
    (Witness.rising).check 52 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_31_3_checked :
    (Witness.rising).check 52 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_31_4_checked :
    (Witness.rising).check 52 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_31_5_checked :
    (Witness.rising).check 52 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_31_6_checked :
    (Witness.rising).check 52 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_31_7_checked :
    (Witness.rising).check 52 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_31_8_checked :
    (Witness.rising).check 52 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_31_9_checked :
    (Witness.rising).check 52 31 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_31_10_checked :
    (Witness.linear .positive case_52_31_10).check 52 31 10 = true := by
  change case_52_31_10.check 52 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_31_11_checked :
    (Witness.linear .positive case_52_31_11).check 52 31 11 = true := by
  change case_52_31_11.check 52 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_31_12_checked :
    (Witness.linear .positive case_52_31_12).check 52 31 12 = true := by
  change case_52_31_12.check 52 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_31_13_checked :
    (Witness.linear .positive case_52_31_13).check 52 31 13 = true := by
  change case_52_31_13.check 52 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_31_14 : Certificate := {
  objectiveScale := 3822698880000
  eta := 29142595336683628800
  rows := #[⟨.count 2, 6042191864102634240⟩, ⟨.count 3, 1363569821466652800⟩, ⟨.count 4, 293852160074753280⟩, ⟨.count 5, 67132606712371200⟩, ⟨.count 6, 15205902934622400⟩, ⟨.count 7, 3580201516731840⟩, ⟨.count 8, 869783773098240⟩, ⟨.count 9, 220508562193920⟩, ⟨.count 10, 60074448033600⟩, ⟨.count 11, 17668955304000⟩, ⟨.count 12, 8481098545920⟩, ⟨.count 13, 6125237838720⟩, ⟨.path 13, 1737583271424⟩, ⟨.privateRow 2 29, 299735451018843840⟩, ⟨.privateRow 3 27, 154319242108711680⟩, ⟨.privateRow 6 20, 3704492801209200⟩, ⟨.privateRow 6 25, 278954815996256400⟩, ⟨.privateRow 7 17, 368662752417960⟩, ⟨.privateRow 7 18, 1107136739348640⟩, ⟨.privateRow 7 19, 2541718484825520⟩, ⟨.privateRow 7 20, 2586075415507584⟩, ⟨.privateRow 7 21, 3950778405974400⟩, ⟨.privateRow 7 22, 5026778519642880⟩, ⟨.privateRow 7 23, 2329121688173280⟩, ⟨.privateRow 8 14, 24883778719800⟩, ⟨.privateRow 8 15, 201707484938960⟩, ⟨.privateRow 8 16, 462264043140900⟩, ⟨.privateRow 8 17, 865299223966320⟩, ⟨.privateRow 8 18, 1833743077966800⟩, ⟨.privateRow 9 12, 26899645893120⟩, ⟨.privateRow 9 13, 90135230657472⟩, ⟨.privateRow 9 14, 201085799474560⟩, ⟨.privateRow 9 15, 351965589655680⟩, ⟨.privateRow 9 16, 672497266446720⟩, ⟨.privateRow 9 17, 1140393639665280⟩, ⟨.privateRow 9 18, 282609050435712⟩, ⟨.privateRow 9 19, 1026919682268480⟩, ⟨.privateRow 10 9, 1223235367200⟩, ⟨.privateRow 10 10, 16814955797640⟩, ⟨.privateRow 10 11, 43626256914240⟩, ⟨.privateRow 10 12, 88910183089728⟩, ⟨.privateRow 10 13, 156782530064160⟩, ⟨.privateRow 10 14, 289638349820820⟩, ⟨.privateRow 10 15, 466107040919520⟩, ⟨.privateRow 10 16, 722778064968960⟩, ⟨.privateRow 10 17, 432818729126784⟩, ⟨.privateRow 10 19, 1407508979516640⟩, ⟨.privateRow 11 7, 1996362482400⟩, ⟨.privateRow 11 8, 8896257216000⟩, ⟨.privateRow 11 9, 22782243884400⟩, ⟨.privateRow 11 10, 43778122315200⟩, ⟨.privateRow 11 11, 75076997355360⟩, ⟨.privateRow 11 12, 140923304121600⟩, ⟨.privateRow 11 13, 223833538328400⟩, ⟨.privateRow 11 14, 331533852249600⟩, ⟨.privateRow 11 15, 470101295664000⟩, ⟨.privateRow 11 16, 339243941836800⟩, ⟨.privateRow 11 18, 16598109528000⟩, ⟨.privateRow 11 20, 4432016497708800⟩, ⟨.privateRow 12 5, 1908247172832⟩, ⟨.privateRow 12 6, 5149238402880⟩, ⟨.privateRow 12 7, 12531366761760⟩, ⟨.privateRow 12 8, 24736537425600⟩, ⟨.privateRow 12 9, 41891486757120⟩, ⟨.privateRow 12 10, 77990768711856⟩, ⟨.privateRow 12 11, 130279097108160⟩, ⟨.privateRow 12 12, 197936471793060⟩, ⟨.privateRow 12 13, 285328386794880⟩, ⟨.privateRow 12 14, 400201837635600⟩, ⟨.privateRow 12 16, 936101252005920⟩, ⟨.privateRow 13 3, 1737447271560⟩, ⟨.privateRow 13 4, 3392439418368⟩, ⟨.privateRow 13 5, 7774340333760⟩, ⟨.privateRow 13 6, 2972008892160⟩, ⟨.privateRow 13 7, 53242451982720⟩, ⟨.privateRow 13 8, 38464780273920⟩, ⟨.privateRow 13 9, 85093688744064⟩, ⟨.privateRow 13 10, 133498773408000⟩, ⟨.privateRow 13 11, 190530234694800⟩, ⟨.privateRow 13 12, 255779162496000⟩, ⟨.privateRow 13 13, 328956683415360⟩, ⟨.privateRow 13 15, 415691621785440⟩, ⟨.privateRow 14 2, 6173091259335⟩, ⟨.privateRow 14 3, 3930360946512⟩, ⟨.privateRow 14 4, 10117580358600⟩, ⟨.privateRow 14 5, 4122756237600⟩, ⟨.privateRow 14 6, 79819505585820⟩, ⟨.privateRow 14 7, 52969386309840⟩, ⟨.privateRow 14 8, 112015286975592⟩, ⟨.privateRow 14 9, 174654351151280⟩, ⟨.privateRow 14 10, 250177682975220⟩, ⟨.privateRow 14 12, 1143760557259320⟩, ⟨.privateRow 14 15, 1239850225854240⟩, ⟨.privateRow 15 0, 3152695946400⟩, ⟨.privateRow 15 1, 9379270440540⟩, ⟨.privateRow 15 3, 32595015641760⟩, ⟨.privateRow 15 5, 136924587519720⟩, ⟨.privateRow 15 6, 94662766598400⟩, ⟨.privateRow 15 7, 175028671241424⟩, ⟨.privateRow 15 8, 272573083823040⟩, ⟨.privateRow 15 9, 385698570156900⟩, ⟨.privateRow 15 11, 1338109249517040⟩, ⟨.privateRow 16 1, 70950671631840⟩, ⟨.privateRow 16 2, 34454462842800⟩, ⟨.privateRow 16 4, 273721565917800⟩, ⟨.privateRow 16 5, 219255672636000⟩, ⟨.privateRow 16 6, 339185045319120⟩, ⟨.privateRow 16 7, 525324217418000⟩, ⟨.privateRow 16 8, 741249485326350⟩, ⟨.privateRow 16 9, 385561846098000⟩, ⟨.privateRow 16 10, 1337981640395400⟩, ⟨.privateRow 16 14, 4459938801318000⟩, ⟨.privateRow 17 0, 213158276787456⟩, ⟨.privateRow 17 1, 89253465649920⟩, ⟨.privateRow 17 4, 1940029875463680⟩, ⟨.privateRow 17 6, 1671509347988480⟩, ⟨.privateRow 17 7, 1614000170502720⟩, ⟨.privateRow 17 8, 1571561022620160⟩, ⟨.privateRow 17 10, 5245653685079808⟩, ⟨.privateRow 17 14, 8759090109369600⟩, ⟨.privateRow 18 0, 1491276655234080⟩, ⟨.privateRow 18 3, 5140188226293120⟩, ⟨.privateRow 18 8, 43951133675248800⟩, ⟨.privateRow 19 0, 11918770489866240⟩, ⟨.privateRow 19 2, 15363767018920320⟩, ⟨.privateRow 19 3, 10277536569588288⟩, ⟨.privateRow 19 7, 87884912509954560⟩, ⟨.privateRow 20 0, 184737938870525040⟩, ⟨.privateRow 20 1, 7014511004941440⟩, ⟨.privateRow 20 5, 477372161028597120⟩, ⟨.privateRow 20 10, 1149975121483188000⟩, ⟨.privateRow 21 10, 124167636342855705600⟩, ⟨.hall 16 2, 6883600618752⟩, ⟨.hall 12 8, 70412126400⟩, ⟨.hall 10 11, 18366464160⟩, ⟨.hall 16 11, 4958525869440⟩, ⟨.hall 13 12, 192307303760⟩, ⟨.hall 17 12, 189949683306240⟩, ⟨.hall 11 15, 320238418500⟩, ⟨.hall 8 16, 24674432640⟩, ⟨.hall 12 17, 13068827291520⟩, ⟨.hall 11 19, 33217635971520⟩, ⟨.hall 6 20, 2839623600528⟩, ⟨.hall 9 21, 6516953223580800⟩, ⟨.hall 8 22, 13610811107013120⟩, ⟨.hall 7 23, 36810510055639320⟩, ⟨.hall 4 26, 298850354151148800⟩, ⟨.hall 3 27, 396486207783357120⟩]
  caps := #[0, 0, 0, 0, 10447730092800, 0, 808224729312, 11861758660752, 1785925709568, 3840241290160, 779476683744, 1929417272424, 0, 2624626005408, 0, 5047043121120, 124470683015250, 9625373746560, 0, 2574681616450944, 19126104869242800, 0] }

theorem case_52_31_14_checked :
    (Witness.linear .positive case_52_31_14).check 52 31 14 = true := by
  change case_52_31_14.check 52 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_31_15 : Certificate := {
  objectiveScale := 7167560400000
  eta := 83866572730619078400
  rows := #[⟨.count 2, 18215605924293697920⟩, ⟨.count 3, 4301570776997894400⟩, ⟨.count 4, 995265395462257920⟩, ⟨.count 5, 223264919221344000⟩, ⟨.count 6, 54851504845737600⟩, ⟨.count 7, 13313204442457920⟩, ⟨.count 8, 3160622724779520⟩, ⟨.count 9, 826907108227200⟩, ⟨.count 10, 222628836830400⟩, ⟨.count 11, 63608239094400⟩, ⟨.count 12, 12721647818880⟩, ⟨.path 12, 4430787352992⟩, ⟨.privateRow 2 29, 1282036780595450880⟩, ⟨.privateRow 3 28, 2378515606104718080⟩, ⟨.privateRow 6 20, 8077657399812000⟩, ⟨.privateRow 6 21, 17211152672073360⟩, ⟨.privateRow 6 24, 201489698704694400⟩, ⟨.privateRow 7 17, 495570023888940⟩, ⟨.privateRow 7 18, 3214437314362560⟩, ⟨.privateRow 7 19, 7586107063254720⟩, ⟨.privateRow 7 20, 15716747770371648⟩, ⟨.privateRow 7 21, 17330594809928400⟩, ⟨.privateRow 7 22, 30399555393567360⟩, ⟨.privateRow 7 24, 391664551811813280⟩, ⟨.privateRow 8 15, 370832107485840⟩, ⟨.privateRow 8 16, 1252132603812090⟩, ⟨.privateRow 8 17, 2834453809867680⟩, ⟨.privateRow 8 18, 6204100275893520⟩, ⟨.privateRow 8 20, 11193680736578340⟩, ⟨.privateRow 8 21, 56976196721043600⟩, ⟨.privateRow 8 23, 52205402099410560⟩, ⟨.privateRow 9 13, 196054728053184⟩, ⟨.privateRow 9 14, 527555741032320⟩, ⟨.privateRow 9 15, 1096535366166240⟩, ⟨.privateRow 9 16, 2376928832952960⟩, ⟨.privateRow 9 18, 10431751211481600⟩, ⟨.privateRow 9 20, 17529488350133760⟩, ⟨.privateRow 10 10, 8481098545920⟩, ⟨.privateRow 10 12, 402004071076608⟩, ⟨.privateRow 10 14, 1752406987050720⟩, ⟨.privateRow 10 16, 3515768726389920⟩, ⟨.privateRow 10 17, 3821370977327904⟩, ⟨.privateRow 11 9, 38871701668800⟩, ⟨.privateRow 11 10, 59227506374400⟩, ⟨.privateRow 11 11, 340882335874080⟩, ⟨.privateRow 11 12, 71318328681600⟩, ⟨.privateRow 11 13, 1374443939068200⟩, ⟨.privateRow 11 14, 294497886196800⟩, ⟨.privateRow 11 15, 2095216845321600⟩, ⟨.privateRow 11 16, 2922123953548800⟩, ⟨.privateRow 11 18, 2608259056603200⟩, ⟨.privateRow 12 6, 3104687860560⟩, ⟨.privateRow 12 7, 14189530259520⟩, ⟨.privateRow 12 9, 161719129091520⟩, ⟨.privateRow 12 10, 313164563808096⟩, ⟨.privateRow 12 12, 1316690549254080⟩, ⟨.privateRow 12 13, 430415751205440⟩, ⟨.privateRow 12 14, 1391606919743040⟩, ⟨.privateRow 12 15, 2348204159901600⟩, ⟨.privateRow 12 17, 3655706852397600⟩, ⟨.privateRow 13 4, 2638563992064⟩, ⟨.privateRow 13 5, 8380133087040⟩, ⟨.privateRow 13 6, 17397125222400⟩, ⟨.privateRow 13 7, 4004963202240⟩, ⟨.privateRow 13 8, 202518353157120⟩, ⟨.privateRow 13 9, 5795417339712⟩, ⟨.privateRow 13 11, 2302971634323360⟩, ⟨.privateRow 13 12, 45030594660480⟩, ⟨.privateRow 13 13, 1127750520536640⟩, ⟨.privateRow 13 14, 2088329165290368⟩, ⟨.privateRow 13 15, 1591972872890400⟩, ⟨.privateRow 13 16, 1330118955285120⟩, ⟨.privateRow 13 17, 3581850619226880⟩, ⟨.privateRow 14 2, 1866283403985⟩, ⟨.privateRow 14 3, 5972106892752⟩, ⟨.privateRow 14 4, 13453647395760⟩, ⟨.privateRow 14 5, 24913226978640⟩, ⟨.privateRow 14 6, 6890892568560⟩, ⟨.privateRow 14 7, 279394371416160⟩, ⟨.privateRow 14 8, 33535677166992⟩, ⟨.privateRow 14 9, 2296964189520⟩, ⟨.privateRow 14 10, 1428998846405130⟩, ⟨.privateRow 14 11, 2941754851292400⟩, ⟨.privateRow 15 0, 1891617567840⟩, ⟨.privateRow 15 1, 4306807855350⟩, ⟨.privateRow 15 2, 11331690001632⟩, ⟨.privateRow 15 3, 23297779636560⟩, ⟨.privateRow 15 5, 104129043258240⟩, ⟨.privateRow 15 6, 393824951039520⟩, ⟨.privateRow 15 7, 127711208937312⟩, ⟨.privateRow 15 8, 17354840543040⟩, ⟨.privateRow 15 9, 1634290020843480⟩, ⟨.privateRow 15 10, 3081213391370400⟩, ⟨.privateRow 15 12, 3843280481904864⟩, ⟨.privateRow 16 0, 24405244513650⟩, ⟨.privateRow 16 1, 16844404056480⟩, ⟨.privateRow 16 2, 54142727324400⟩, ⟨.privateRow 16 5, 1172495811286800⟩, ⟨.privateRow 16 6, 200984366583000⟩, ⟨.privateRow 16 7, 111019935826800⟩, ⟨.privateRow 16 8, 2193600800991600⟩, ⟨.privateRow 16 9, 5228874908571600⟩, ⟨.privateRow 16 11, 10391465993388480⟩, ⟨.privateRow 17 3, 1044353051501760⟩, ⟨.privateRow 17 4, 1820866157510400⟩, ⟨.privateRow 17 5, 1341427086679680⟩, ⟨.privateRow 17 6, 400182205463040⟩, ⟨.privateRow 17 7, 3642985204578720⟩, ⟨.privateRow 17 9, 29150006874468480⟩, ⟨.privateRow 17 12, 32034993896505600⟩, ⟨.privateRow 18 3, 11828112686470080⟩, ⟨.privateRow 18 4, 1046496884745312⟩, ⟨.privateRow 18 6, 3123871297747200⟩, ⟨.privateRow 18 13, 556830058823438400⟩, ⟨.privateRow 19 2, 43365013378727040⟩, ⟨.privateRow 19 3, 27083964151468224⟩, ⟨.privateRow 19 4, 2499097038197760⟩, ⟨.privateRow 19 5, 8434452503917440⟩, ⟨.privateRow 20 7, 3830084882028909504⟩, ⟨.privateRow 21 8, 105946095063096288000⟩, ⟨.hall 17 4, 485744822671680⟩, ⟨.hall 18 4, 2908477094979456⟩, ⟨.hall 18 10, 891286356280320⟩, ⟨.hall 19 10, 35072555024707200⟩, ⟨.hall 15 13, 38679236262810⟩, ⟨.hall 8 15, 256893797160⟩, ⟨.hall 11 15, 861703462620⟩, ⟨.hall 14 15, 53556422389470⟩, ⟨.hall 10 17, 4004963202240⟩, ⟨.hall 12 17, 90911424764160⟩, ⟨.hall 9 19, 38685374503776⟩, ⟨.hall 5 21, 30159859137408⟩, ⟨.hall 4 26, 1106868590047700480⟩, ⟨.hall 3 27, 1436065948940800320⟩]
  caps := #[0, 0, 0, 762836263757568, 285360512168160, 0, 0, 0, 7390232609760, 14195967092736, 23944168086696, 0, 27317178024048, 12608824924872, 13833531203349, 3986870880564, 0, 108398148418560, 671211027691776, 4788042734547072, 0, 0] }

theorem case_52_31_15_checked :
    (Witness.linear .positive case_52_31_15).check 52 31 15 = true := by
  change case_52_31_15.check 52 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_31_16 : Certificate := {
  objectiveScale := 142648506000000
  eta := 1394214998897552832000
  rows := #[⟨.count 2, 289686894215380421760⟩, ⟨.count 3, 64981833574347930240⟩, ⟨.count 4, 14023683029846730240⟩, ⟨.count 5, 3362571816322118400⟩, ⟨.count 6, 799343537952960000⟩, ⟨.count 7, 188378627110914240⟩, ⟨.count 8, 49559299353083520⟩, ⟨.count 9, 13650328109658240⟩, ⟨.count 10, 3996717689764800⟩, ⟨.count 11, 1229759289158400⟩, ⟨.count 12, 368927786747520⟩, ⟨.count 13, 532895691968640⟩, ⟨.path 11, 72695798471296⟩, ⟨.path 12, 38188967648832⟩, ⟨.privateRow 2 29, 13683962026216722240⟩, ⟨.privateRow 3 26, 434842884646410240⟩, ⟨.privateRow 3 27, 6740064712019358720⟩, ⟨.privateRow 4 24, 818727618748319280⟩, ⟨.privateRow 4 25, 2507895942353081280⟩, ⟨.privateRow 5 22, 468735050655615744⟩, ⟨.privateRow 5 23, 920843755721809920⟩, ⟨.privateRow 5 24, 1826766432068497920⟩, ⟨.privateRow 6 19, 32164061408107200⟩, ⟨.privateRow 6 20, 175022928830950200⟩, ⟨.privateRow 6 21, 356906889695996640⟩, ⟨.privateRow 6 22, 659375153859321900⟩, ⟨.privateRow 6 23, 937341318185672400⟩, ⟨.privateRow 7 17, 23230921571757900⟩, ⟨.privateRow 7 18, 67753880836012800⟩, ⟨.privateRow 7 19, 133534778812475040⟩, ⟨.privateRow 7 20, 250460975225260800⟩, ⟨.privateRow 7 21, 346681953606348360⟩, ⟨.privateRow 7 22, 407087900689710240⟩, ⟨.privateRow 8 15, 11805119842916400⟩, ⟨.privateRow 8 16, 28285104150272970⟩, ⟨.privateRow 8 17, 52109585878933440⟩, ⟨.privateRow 8 18, 97086933880536600⟩, ⟨.privateRow 8 19, 137260607858822448⟩, ⟨.privateRow 8 20, 159119323023761100⟩, ⟨.privateRow 8 21, 143015881332083760⟩, ⟨.privateRow 9 12, 395013589850880⟩, ⟨.privateRow 9 13, 4853449994545152⟩, ⟨.privateRow 9 14, 12420568820499840⟩, ⟨.privateRow 9 15, 22022939270011680⟩, ⟨.privateRow 9 16, 40008168873953280⟩, ⟨.privateRow 9 17, 57682542657579840⟩, ⟨.privateRow 9 18, 68817329821304064⟩, ⟨.privateRow 9 19, 16581254415485760⟩, ⟨.privateRow 10 10, 327935810442240⟩, ⟨.privateRow 10 11, 2071026439241760⟩, ⟨.privateRow 10 12, 5423238465188544⟩, ⟨.privateRow 10 13, 10138682139505920⟩, ⟨.privateRow 10 14, 18211966472880180⟩, ⟨.privateRow 10 15, 26575976638205280⟩, ⟨.privateRow 10 16, 9489642514672320⟩, ⟨.privateRow 11 8, 187043807966400⟩, ⟨.privateRow 11 9, 964243078999200⟩, ⟨.privateRow 11 10, 2502712602936000⟩, ⟨.privateRow 11 11, 4885498266929280⟩, ⟨.privateRow 11 12, 9310147345699200⟩, ⟨.privateRow 11 13, 4139956697877000⟩, ⟨.privateRow 12 6, 90035947956240⟩, ⟨.privateRow 12 7, 484808950533600⟩, ⟨.privateRow 12 8, 1278437261020920⟩, ⟨.privateRow 12 9, 2562930154905120⟩, ⟨.privateRow 12 10, 1730886199490448⟩, ⟨.privateRow 13 4, 38259177884928⟩, ⟨.privateRow 13 5, 260591849369280⟩, ⟨.privateRow 13 6, 728395886655360⟩, ⟨.privateRow 13 7, 498735711714240⟩, ⟨.privateRow 14 0, 3700664527560⟩, ⟨.privateRow 14 2, 4163247593505⟩, ⟨.privateRow 14 3, 146546315291376⟩, ⟨.privateRow 14 4, 171287900989920⟩, ⟨.privateRow 15 1, 58285466309070⟩, ⟨.privateRow 16 0, 20816237967525⟩, ⟨.hall 6 23, 7643722581675180⟩, ⟨.hall 7 23, 58518608174306280⟩, ⟨.hall 6 24, 572649710589500544⟩, ⟨.hall 5 25, 2450500343529638400⟩, ⟨.hall 4 26, 5934129056987971840⟩, ⟨.hall 3 27, 12069801943254712800⟩, ⟨.hall 2 28, 10149457846380652800⟩, ⟨.assumptionRow 16, 182052099028800⟩]
  caps := #[0, 1848752416450779840, 19648061531658560, 33817159687671360, 1441254123429120, 0, 0, 438127159396212, 227909334340688, 267718831283904, 0, 215508526777936, 119543851475928, 0, 486345648315813, 930506597600580, 0, 142648506000000, 0, 0, 0, 0] }

theorem case_52_31_16_checked :
    (Witness.linear .conditional case_52_31_16).check 52 31 16 = true := by
  change case_52_31_16.check 52 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_31_17 : Certificate := {
  objectiveScale := 2936023870567788000000
  eta := 27712943614302766164090345600
  rows := #[⟨.count 2, 5775079860564435499295337120⟩, ⟨.count 3, 1240768492798613780041840800⟩, ⟨.count 4, 258758557472531420795050560⟩, ⟨.count 5, 58926546357144978995683200⟩, ⟨.count 6, 13460013235487920690789200⟩, ⟨.count 7, 3140669754947181494517480⟩, ⟨.count 8, 767772590972573016230400⟩, ⟨.count 9, 205969762385911414931040⟩, ⟨.count 10, 66441858834164972558400⟩, ⟨.count 11, 22147286278054990852800⟩, ⟨.count 12, 6644185883416497255840⟩, ⟨.count 13, 9597157387157162702880⟩, ⟨.path 10, 4626380731918706560800⟩, ⟨.privateRow 2 29, 432433516129221015647718480⟩, ⟨.privateRow 3 26, 24309599661669093126395040⟩, ⟨.privateRow 3 27, 159317611205502479449159440⟩, ⟨.privateRow 4 24, 20312383609918134860645520⟩, ⟨.privateRow 4 25, 58054804561144870050171600⟩, ⟨.privateRow 5 22, 9720001001712774385476864⟩, ⟨.privateRow 5 23, 20633888382387899811192000⟩, ⟨.privateRow 5 24, 43507113488445804253056000⟩, ⟨.privateRow 6 19, 442154751051169281668400⟩, ⟨.privateRow 6 20, 3408990280229783835085500⟩, ⟨.privateRow 6 21, 7635738346156917575478900⟩, ⟨.privateRow 6 22, 15485913177683128005100275⟩, ⟨.privateRow 6 23, 24116856750810353442112200⟩, ⟨.privateRow 7 17, 288514543951412203755330⟩, ⟨.privateRow 7 18, 1225351344967387737957000⟩, ⟨.privateRow 7 19, 2758782867249886061965380⟩, ⟨.privateRow 7 20, 5756854858686224047322568⟩, ⟨.privateRow 7 21, 8944550684830475639084160⟩, ⟨.privateRow 7 22, 11862086530526253100759680⟩, ⟨.privateRow 8 15, 128628567758425861226100⟩, ⟨.privateRow 8 16, 464862310940425068420750⟩, ⟨.privateRow 8 17, 1029980641014545497219800⟩, ⟨.privateRow 8 18, 2189151588166328634038190⟩, ⟨.privateRow 8 19, 3515678679850347627132516⟩, ⟨.privateRow 8 20, 4684612449606090044343300⟩, ⟨.privateRow 8 21, 5096490454138251610341900⟩, ⟨.privateRow 9 13, 48133435510972846786752⟩, ⟨.privateRow 9 14, 181771801452480961962240⟩, ⟨.privateRow 9 15, 407325506797228040101080⟩, ⟨.privateRow 9 16, 874923271251162876737280⟩, ⟨.privateRow 9 17, 1456676234699405759479440⟩, ⟨.privateRow 9 18, 2008168271118839537259552⟩, ⟨.privateRow 9 19, 2260315125394495608118680⟩, ⟨.privateRow 9 20, 689272765164800326429920⟩, ⟨.privateRow 10 11, 15956113068507800228040⟩, ⟨.privateRow 10 12, 71480366462422482977412⟩, ⟨.privateRow 10 13, 170411063861700901839600⟩, ⟨.privateRow 10 14, 375742553761126704187035⟩, ⟨.privateRow 10 15, 648599098143039017832000⟩, ⟨.privateRow 10 16, 937753013156645071025640⟩, ⟨.privateRow 10 17, 591996962212409905495344⟩, ⟨.privateRow 11 9, 4572072356643928035900⟩, ⟨.privateRow 11 10, 27867143271354317002800⟩, ⟨.privateRow 11 11, 74344413256107321567240⟩, ⟨.privateRow 11 12, 174381915694382478482400⟩, ⟨.privateRow 11 13, 316794279573883178817750⟩, ⟨.privateRow 11 14, 360828190075584234088800⟩, ⟨.privateRow 12 7, 937000573302326536080⟩, ⟨.privateRow 12 8, 10566101161822068552690⟩, ⟨.privateRow 12 9, 33271264158623520349320⟩, ⟨.privateRow 12 10, 86595889347195014234448⟩, ⟨.privateRow 12 11, 170841705539329748883960⟩, ⟨.privateRow 12 12, 5329190760656982173955⟩, ⟨.privateRow 13 6, 3634426466142357473280⟩, ⟨.privateRow 13 7, 15010938477348382689120⟩, ⟨.privateRow 13 8, 45167041409487905587680⟩, ⟨.privateRow 13 9, 28939120736658521380992⟩, ⟨.privateRow 14 4, 856889052424746669900⟩, ⟨.privateRow 14 5, 6459625164432705665400⟩, ⟨.privateRow 14 6, 17394847764222357398970⟩, ⟨.privateRow 15 0, 141134667458193569160⟩, ⟨.privateRow 15 3, 2227911536304341341740⟩, ⟨.privateRow 15 4, 3322092941708248627920⟩, ⟨.privateRow 16 1, 399881557798215112620⟩, ⟨.privateRow 16 2, 428444526212373334950⟩, ⟨.hall 7 23, 6294635571691153641529575⟩, ⟨.hall 6 24, 27039511080445948057229256⟩, ⟨.hall 5 25, 71664927181406274567852000⟩, ⟨.hall 4 26, 156395987681660320232999360⟩, ⟨.hall 3 27, 299494034757940967786092680⟩, ⟨.hall 2 28, 253976525602034144896546560⟩, ⟨.assumptionRow 17, 2915427663115754967180⟩]
  caps := #[0, 44002313368044103903931100, 0, 1612129456276669378208160, 0, 122482122815697509520656, 5552667072587858085720, 0, 1715526426188494639434, 3228743736498498213996, 5342189215544874766359, 1193966747002248118200, 4983785197382775840903, 0, 5001770419861040216820, 0, 43907904584495923115430, 35252882654265489032820, 2936023870567788000000, 0, 0, 0] }

theorem case_52_31_17_checked :
    (Witness.linear .conditional case_52_31_17).check 52 31 17 = true := by
  change case_52_31_17.check 52 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_31_18 : Certificate := {
  objectiveScale := 36292347708283368090576000000
  eta := 274405461840272437564260705023289600
  rows := #[⟨.count 2, 58747025670224071577983990716312000⟩, ⟨.count 3, 12291992264173878745790741962441920⟩, ⟨.count 4, 2502816124762007984375005558078080⟩, ⟨.count 5, 546811424394775139425557568636800⟩, ⟨.count 6, 119394983760017962310194168688400⟩, ⟨.count 7, 26421396078588741536621182948080⟩, ⟨.count 8, 6179986055391593135138633465280⟩, ⟨.count 9, 1570570944943725227138445311040⟩, ⟨.count 10, 676970234889536735835536772000⟩, ⟨.count 11, 270788093955814694334214708800⟩, ⟨.count 12, 108315237582325877733685883520⟩, ⟨.count 13, 78227671587235356140995360320⟩, ⟨.path 9, 51839195546821142711852092800⟩, ⟨.path 10, 27307406430882102922801588800⟩, ⟨.privateRow 2 29, 6746432625354764348955580869357120⟩, ⟨.privateRow 3 26, 453485812191203359549350103775040⟩, ⟨.privateRow 3 27, 2006774459227348591084953978288960⟩, ⟨.privateRow 4 24, 261319536937159707188995001148960⟩, ⟨.privateRow 4 25, 714805349128363066738345104924000⟩, ⟨.privateRow 5 22, 106858999388163496488599662197120⟩, ⟨.privateRow 5 23, 244969953575427517755526970842080⟩, ⟨.privateRow 5 24, 550566352630962436520325345932160⟩, ⟨.privateRow 6 19, 2968460752194198782135984655000⟩, ⟨.privateRow 6 20, 34933544593174788726713240592900⟩, ⟨.privateRow 6 21, 86040660287010487335577271931960⟩, ⟨.privateRow 6 22, 191633349241355611496644571733900⟩, ⟨.privateRow 6 23, 326600528876707611888655629336000⟩, ⟨.privateRow 7 17, 1674561094914256842393181931850⟩, ⟨.privateRow 7 18, 11485498496254448181986854509840⟩, ⟨.privateRow 7 19, 29609173695768582299366743881120⟩, ⟨.privateRow 7 20, 68938135586251157599252161282000⟩, ⟨.privateRow 7 21, 119791011347428341300657957700020⟩, ⟨.privateRow 7 22, 177263903816675317015495486485120⟩, ⟨.privateRow 8 15, 589967023220399977563340009080⟩, ⟨.privateRow 8 16, 3858824362514094052142536758285⟩, ⟨.privateRow 8 17, 10367960330722514522829777933840⟩, ⟨.privateRow 8 18, 25256129720570548210770939559980⟩, ⟨.privateRow 8 19, 46013516427611836482133470940224⟩, ⟨.privateRow 8 20, 69605515409479759231330027949730⟩, ⟨.privateRow 8 21, 87758409575613530364173295052320⟩, ⟨.privateRow 9 13, 138402803577416399326376406720⟩, ⟨.privateRow 9 14, 1279724473657850185075770253440⟩, ⟨.privateRow 9 15, 3734619129140610992692711192200⟩, ⟨.privateRow 9 16, 9573003854895087098748619038720⟩, ⟨.privateRow 9 17, 18443677954990489736319290721600⟩, ⟨.privateRow 9 18, 29146426930764090077271163634304⟩, ⟨.privateRow 9 19, 38257844541057352731185634774960⟩, ⟨.privateRow 9 20, 38688598194220398698654320765440⟩, ⟨.privateRow 10 11, 4102849908421434762639616800⟩, ⟨.privateRow 10 12, 395350617175489453727953474848⟩, ⟨.privateRow 10 13, 1364972577310606662921726735840⟩, ⟨.privateRow 10 14, 3787084322344550089719965292030⟩, ⟨.privateRow 10 15, 7790315569685973694381705539120⟩, ⟨.privateRow 10 16, 13048977372070759214749879911840⟩, ⟨.privateRow 10 17, 18163562715576196980291341950608⟩, ⟨.privateRow 10 18, 12317473423815120908527591566540⟩, ⟨.privateRow 11 10, 78700120970629339537905376800⟩, ⟨.privateRow 11 11, 487418569120466449801586475840⟩, ⟨.privateRow 11 12, 1552244882019442818531988356000⟩, ⟨.privateRow 11 13, 3495115265736509738423623561500⟩, ⟨.privateRow 11 14, 6293185638102992149494509368800⟩, ⟨.privateRow 11 15, 9233463718902438933320457608400⟩, ⟨.privateRow 12 8, 9402364373465787997715788500⟩, ⟨.privateRow 12 9, 136624901950433777595899239440⟩, ⟨.privateRow 12 10, 639962528715575394276527428464⟩, ⟨.privateRow 12 11, 1656320508029733213677613302160⟩, ⟨.privateRow 12 12, 3286690490388700852481531028060⟩, ⟨.privateRow 12 13, 2028331770440459591370093985440⟩, ⟨.privateRow 13 7, 28081728262084486819844488320⟩, ⟨.privateRow 13 8, 223742081672582242389280436160⟩, ⟨.privateRow 13 9, 806948519988327789115959832224⟩, ⟨.privateRow 13 10, 1581268746186424079260290830400⟩, ⟨.privateRow 14 5, 2256567449631789119451789240⟩, ⟨.privateRow 14 6, 65189726322696130117496133600⟩, ⟨.privateRow 14 7, 345801866448119926577809035960⟩, ⟨.privateRow 14 8, 437097114993677552437811575788⟩, ⟨.privateRow 15 4, 12035026398036208637076209280⟩, ⟨.privateRow 15 5, 128749709487324856982054863860⟩, ⟨.privateRow 15 6, 101340392738009438637198534960⟩, ⟨.privateRow 16 3, 37609457493863151990863154000⟩, ⟨.privateRow 16 4, 20371789475842540661717541750⟩, ⟨.privateRow 17 1, 11175381655319336591570765760⟩, ⟨.hall 8 22, 14376885556488863061216842959680⟩, ⟨.hall 7 23, 159828911511670237015571145553800⟩, ⟨.hall 6 24, 477544732587857593330513226841456⟩, ⟨.hall 5 25, 1095879416239182067970566926513600⟩, ⟨.hall 4 26, 2192118991786868330629235985512320⟩, ⟨.hall 3 27, 3970660597506995398165607250282480⟩, ⟨.hall 2 28, 3390206553694354653465861444229440⟩, ⟨.assumptionRow 18, 25420714594120482276620700720⟩]
  caps := #[0, 0, 12805853848800425135634845934000, 0, 103052261987785510308186743520, 1013945263430313254653613957440, 0, 61918795256966661307638175920, 123127555364987932899321240213, 0, 0, 0, 37148545203944006959350057504, 0, 39969796074078078739286102160, 90359361426115118794760641800, 332302066760970956855096926650, 25420714594120482276620700720, 410087457905279934810291299280, 36292347708283368090576000000, 0, 0] }

theorem case_52_31_18_checked :
    (Witness.linear .conditional case_52_31_18).check 52 31 18 = true := by
  change case_52_31_18.check 52 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_31_19 : Certificate := {
  objectiveScale := 1614813128812283400000
  eta := 16677364277958487915302691200
  rows := #[⟨.count 2, 3567963993295579849537806240⟩, ⟨.count 3, 751802921080343497492807680⟩, ⟨.count 4, 151839826074675856843165440⟩, ⟨.count 5, 32534363542462781562763200⟩, ⟨.count 6, 6706013724276067438637400⟩, ⟨.count 7, 1304413641537777697366440⟩, ⟨.count 8, 233530829754157625770080⟩, ⟨.count 9, 37650386672693484449760⟩, ⟨.count 10, 5536821569513747713200⟩, ⟨.path 10, 3402967000692363904800⟩, ⟨.privateRow 2 29, 382835406752392798799234640⟩, ⟨.privateRow 3 26, 23058770148876276254119680⟩, ⟨.privateRow 3 27, 117306054743221999717302240⟩, ⟨.privateRow 4 24, 14282569599878849177448540⟩, ⟨.privateRow 4 25, 41368013741930552210614080⟩, ⟨.privateRow 5 22, 6041090669969195349372864⟩, ⟨.privateRow 5 23, 13981458786856793197645680⟩, ⟨.privateRow 5 24, 32242183417564885720475520⟩, ⟨.privateRow 6 19, 225361820787708374183700⟩, ⟨.privateRow 6 20, 1960752571737248102213400⟩, ⟨.privateRow 6 21, 4850563296092349316080600⟩, ⟨.privateRow 6 22, 11038730403019728183875100⟩, ⟨.privateRow 6 23, 19476897741825064085344800⟩, ⟨.privateRow 7 17, 139558663671577074304380⟩, ⟨.privateRow 7 18, 644152063676096229986160⟩, ⟨.privateRow 7 19, 1633782751310907545127780⟩, ⟨.privateRow 7 20, 3893566751969660908558416⟩, ⟨.privateRow 7 21, 7024319444283446668282920⟩, ⟨.privateRow 7 22, 10912234536902892803249640⟩, ⟨.privateRow 8 15, 57938394596541389650720⟩, ⟨.privateRow 8 16, 220534679125715634609930⟩, ⟨.privateRow 8 17, 559148669675561360332080⟩, ⟨.privateRow 8 18, 1388788650233201086129260⟩, ⟨.privateRow 8 19, 2639698139337577601427144⟩, ⟨.privateRow 8 20, 4217750730876673900359450⟩, ⟨.privateRow 8 21, 5699245255592761190097780⟩, ⟨.privateRow 9 13, 19661868595739930768208⟩, ⟨.privateRow 9 14, 76695232111042283138400⟩, ⟨.privateRow 9 15, 198587333626559751313440⟩, ⟨.privateRow 9 16, 510547680343162908182880⟩, ⟨.privateRow 9 17, 1028044218232826667993120⟩, ⟨.privateRow 9 18, 1725765762977773898340960⟩, ⟨.privateRow 9 19, 2440015745445047353343760⟩, ⟨.privateRow 9 20, 2745935390533958791808640⟩, ⟨.privateRow 10 11, 5671047546956505233520⟩, ⟨.privateRow 10 12, 26152253880003268365348⟩, ⟨.privateRow 10 13, 72963004238258942087280⟩, ⟨.privateRow 10 14, 196695586256975887511430⟩, ⟨.privateRow 10 15, 419849269871128183738080⟩, ⟨.privateRow 10 16, 749008917875887537869000⟩, ⟨.privateRow 10 17, 1125045230781396777004152⟩, ⟨.privateRow 10 18, 1388311868375826291187290⟩, ⟨.privateRow 10 19, 130299867602556862850640⟩, ⟨.privateRow 11 9, 1328277901777287961500⟩, ⟨.privateRow 11 10, 8404376542154476556400⟩, ⟨.privateRow 11 11, 27130425690617363794680⟩, ⟨.privateRow 11 12, 79678031609770228034400⟩, ⟨.privateRow 11 13, 182400519659322211597350⟩, ⟨.privateRow 11 14, 348028784369435570544000⟩, ⟨.privateRow 11 15, 561679788107339073572400⟩, ⟨.privateRow 11 16, 430261370692759231385760⟩, ⟨.privateRow 12 7, 212954675750528758200⟩, ⟨.privateRow 12 8, 2383909286873974709850⟩, ⟨.privateRow 12 9, 9798496353321298983360⟩, ⟨.privateRow 12 10, 33387034064167898710596⟩, ⟨.privateRow 12 11, 84754383506667849254280⟩, ⟨.privateRow 12 12, 175194262495364167225170⟩, ⟨.privateRow 12 13, 306107135343117195001200⟩, ⟨.privateRow 12 14, 13626733084969945760820⟩, ⟨.privateRow 13 6, 511091221801269019680⟩, ⟨.privateRow 13 7, 3178545715831966279800⟩, ⟨.privateRow 13 8, 13937130657806322526560⟩, ⟨.privateRow 13 9, 39938939588092500171216⟩, ⟨.privateRow 13 10, 99279995648910705909280⟩, ⟨.privateRow 13 11, 77730822812006891506980⟩, ⟨.privateRow 14 4, 28562968414158222330⟩, ⟨.privateRow 14 5, 769002995765798293500⟩, ⟨.privateRow 14 6, 5365077567126052760985⟩, ⟨.privateRow 14 7, 20757488136616439027820⟩, ⟨.privateRow 14 8, 54463868172116898338844⟩, ⟨.privateRow 15 4, 1538005991531596587000⟩, ⟨.privateRow 15 5, 9797098166056270259190⟩, ⟨.privateRow 15 6, 15631733623021136220600⟩, ⟨.privateRow 16 3, 3537413780522672150100⟩, ⟨.privateRow 16 4, 4498667525229920016975⟩, ⟨.privateRow 17 2, 1968647669160443631360⟩, ⟨.hall 8 22, 2349356310528574423396320⟩, ⟨.hall 7 23, 11979518414666328938832420⟩, ⟨.hall 6 24, 31809778159732415778695760⟩, ⟨.hall 5 25, 69094611568358670351657600⟩, ⟨.hall 4 26, 133905227069994308645516800⟩, ⟨.hall 3 27, 237770259778060645761187920⟩, ⟨.hall 2 28, 201706104297575097398898720⟩, ⟨.assumptionRow 19, 354250315743164446320⟩]
  caps := #[0, 7982706904853259448069200, 439165065568026105902880, 0, 21575568354072878882880, 9602262317226581196480, 2963386508644447657200, 5878015776096413794416, 1492668080160685788074, 0, 0, 1083699079949244357300, 0, 1181017829530597940112, 0, 2921633965882155183660, 354250315743164446320, 9993937675638761404560, 100711849583880447644160, 17408694101191952953680, 1614813128812283400000, 0] }

theorem case_52_31_19_checked :
    (Witness.linear .conditional case_52_31_19).check 52 31 19 = true := by
  change case_52_31_19.check 52 31 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_31_20 : Certificate := {
  objectiveScale := 343006413750000
  eta := 6489717666217898112000
  rows := #[⟨.count 2, 879693871962978072000⟩, ⟨.count 3, 130748071231560182400⟩, ⟨.count 4, 23916879300768854400⟩, ⟨.count 5, 5207830341425712000⟩, ⟨.count 6, 1227210542355798000⟩, ⟨.count 7, 281592496540555200⟩, ⟨.count 8, 60884864116876800⟩, ⟨.count 9, 12043159935206400⟩, ⟨.count 10, 1881743739876000⟩, ⟨.path 4, 1462991543513136000⟩, ⟨.path 11, 228655784477120⟩, ⟨.privateRow 2 29, 105879322314106941600⟩, ⟨.privateRow 3 28, 163074672388472644800⟩, ⟨.privateRow 5 25, 32425539061102387200⟩, ⟨.privateRow 6 20, 277017071484153000⟩, ⟨.privateRow 7 17, 2582170576385400⟩, ⟨.privateRow 7 18, 95171429815347600⟩, ⟨.privateRow 7 19, 289927924366080000⟩, ⟨.privateRow 7 22, 5671624417935075600⟩, ⟨.privateRow 8 15, 1510041272740000⟩, ⟨.privateRow 8 16, 28115080946827875⟩, ⟨.privateRow 8 17, 94453081609887000⟩, ⟨.privateRow 8 18, 273642129239579100⟩, ⟨.privateRow 8 19, 322472333876172480⟩, ⟨.privateRow 8 20, 616221417682921050⟩, ⟨.privateRow 8 21, 2222433443980549800⟩, ⟨.privateRow 8 22, 2017082931300637200⟩, ⟨.privateRow 9 13, 577068080228640⟩, ⟨.privateRow 9 14, 8000895605102400⟩, ⟨.privateRow 9 15, 29512014320388600⟩, ⟨.privateRow 9 16, 93334489497849600⟩, ⟨.privateRow 9 17, 218184701927992800⟩, ⟨.privateRow 9 19, 745254154046001600⟩, ⟨.privateRow 9 20, 1071004903682313600⟩, ⟨.privateRow 10 11, 165365358958800⟩, ⟨.privateRow 10 12, 2107552988661120⟩, ⟨.privateRow 10 13, 8551479884547600⟩, ⟨.privateRow 10 14, 29755072886789250⟩, ⟨.privateRow 10 15, 75529609444832400⟩, ⟨.privateRow 10 16, 152076256577645400⟩, ⟨.privateRow 10 17, 79384495906235520⟩, ⟨.privateRow 10 19, 1004391175290703200⟩, ⟨.privateRow 11 9, 38015025048000⟩, ⟨.privateRow 11 10, 544306040460000⟩, ⟨.privateRow 11 11, 2634441235826400⟩, ⟨.privateRow 11 12, 10517490263280000⟩, ⟨.privateRow 11 13, 30756531202897500⟩, ⟨.privateRow 11 14, 70960474969956000⟩, ⟨.privateRow 11 15, 136141308453150000⟩, ⟨.privateRow 11 16, 146878652277957600⟩, ⟨.privateRow 11 18, 712914772237668000⟩, ⟨.privateRow 12 7, 9649967896800⟩, ⟨.privateRow 12 8, 120222516714300⟩, ⟨.privateRow 12 9, 729888480921600⟩, ⟨.privateRow 12 10, 3562768147498560⟩, ⟨.privateRow 12 11, 12043159935206400⟩, ⟨.privateRow 12 12, 31315352071103100⟩, ⟨.privateRow 12 13, 66013362531745200⟩, ⟨.privateRow 12 14, 117692616797355600⟩, ⟨.privateRow 12 15, 142611085566069120⟩, ⟨.privateRow 12 16, 73435049448660900⟩, ⟨.privateRow 12 17, 164819843349361200⟩, ⟨.privateRow 12 18, 127582225563592800⟩, ⟨.privateRow 13 6, 19299935793600⟩, ⟨.privateRow 13 7, 174235531470000⟩, ⟨.privateRow 13 8, 1125244741420800⟩, ⟨.privateRow 13 9, 4716904307955840⟩, ⟨.privateRow 13 10, 14264082176344000⟩, ⟨.privateRow 13 11, 33944566240985400⟩, ⟨.privateRow 13 12, 66810863450073600⟩, ⟨.privateRow 13 13, 112820991337454400⟩, ⟨.privateRow 13 14, 144618278888603520⟩, ⟨.privateRow 13 18, 564355855852588800⟩, ⟨.privateRow 14 4, 9707408181900⟩, ⟨.privateRow 14 5, 31362395664600⟩, ⟨.privateRow 14 6, 305783357729850⟩, ⟨.privateRow 14 7, 1754393405965200⟩, ⟨.privateRow 14 8, 6632101269874080⟩, ⟨.privateRow 14 10, 77957768256793425⟩, ⟨.privateRow 14 11, 58807478765950200⟩, ⟨.privateRow 14 12, 126367803909246900⟩, ⟨.privateRow 14 14, 223323778928700450⟩, ⟨.privateRow 15 4, 62724791329200⟩, ⟨.privateRow 15 5, 566265477277500⟩, ⟨.privateRow 15 6, 2989881720025200⟩, ⟨.privateRow 15 7, 10437405277178880⟩, ⟨.privateRow 15 8, 3503295752756800⟩, ⟨.privateRow 15 9, 89628499743482700⟩, ⟨.privateRow 15 11, 382161245305039200⟩, ⟨.privateRow 15 13, 97375011472638900⟩, ⟨.privateRow 16 3, 104541318882000⟩, ⟨.privateRow 16 4, 1189157502282750⟩, ⟨.privateRow 16 5, 5868569491785000⟩, ⟨.privateRow 16 6, 19162423751070600⟩, ⟨.privateRow 16 7, 12533342563742000⟩, ⟨.privateRow 16 8, 122483222735123250⟩, ⟨.privateRow 16 9, 89211081191661000⟩, ⟨.privateRow 16 10, 381436425494124000⟩, ⟨.privateRow 17 2, 334532220422400⟩, ⟨.privateRow 17 3, 3080484196389600⟩, ⟨.privateRow 17 4, 13837469117472000⟩, ⟨.privateRow 17 5, 43054296768362880⟩, ⟨.privateRow 17 6, 41073122618528000⟩, ⟨.privateRow 17 7, 207117260969018400⟩, ⟨.privateRow 17 8, 283611637442390400⟩, ⟨.privateRow 17 9, 566809092135686400⟩, ⟨.privateRow 18 1, 710880968397600⟩, ⟨.privateRow 18 2, 9241452589168800⟩, ⟨.privateRow 18 3, 41166470624479200⟩, ⟨.privateRow 18 4, 124759609953778800⟩, ⟨.privateRow 18 5, 157104694015869600⟩, ⟨.privateRow 18 6, 488641805652300300⟩, ⟨.privateRow 18 7, 924145258916880000⟩, ⟨.privateRow 18 9, 1729999924692399360⟩, ⟨.privateRow 18 11, 5082798924042840000⟩, ⟨.privateRow 19 0, 8530571620771200⟩, ⟨.privateRow 19 1, 36965810356675200⟩, ⟨.privateRow 19 2, 166346146605038400⟩, ⟨.privateRow 19 3, 360416650977583200⟩, ⟨.privateRow 19 4, 351175198388414400⟩, ⟨.privateRow 19 5, 894110538002081400⟩, ⟨.privateRow 19 6, 2249633601706233600⟩, ⟨.privateRow 19 7, 1016559784808568000⟩, ⟨.privateRow 19 10, 6284187760634784000⟩, ⟨.privateRow 19 11, 10867948244862508800⟩, ⟨.privateRow 20 0, 351175198388414400⟩, ⟨.privateRow 20 1, 957750541059312000⟩, ⟨.privateRow 20 2, 2370432589121797200⟩, ⟨.privateRow 20 3, 4331160780123777600⟩, ⟨.privateRow 20 4, 9086658258300222600⟩, ⟨.privateRow 20 5, 20167489964591798400⟩, ⟨.privateRow 20 8, 111146950289933157600⟩, ⟨.privateRow 21 0, 21070511903304864000⟩, ⟨.hall 18 4, 137264652443318400⟩, ⟨.hall 16 7, 566001484048000⟩, ⟨.hall 19 7, 577975847347598700⟩, ⟨.hall 14 9, 18068317787520⟩, ⟨.hall 9 12, 9059197878720⟩, ⟨.hall 14 13, 199858403745000⟩, ⟨.hall 17 13, 58089130560489600⟩, ⟨.hall 8 16, 59884148438400⟩, ⟨.hall 6 20, 184003346549880⟩, ⟨.hall 7 22, 252480542151337500⟩, ⟨.hall 8 22, 178778382057475200⟩, ⟨.hall 4 24, 72832124815562112⟩, ⟨.hall 6 24, 12444648779546343360⟩, ⟨.hall 5 25, 41039994636144504000⟩, ⟨.hall 3 27, 85947489390538947600⟩]
  caps := #[0, 5699501548991686800, 138501695407639200, 0, 0, 392610730912400, 1115962908620560, 0, 1372366163623455, 195891414869040, 176158320418080, 1183372415386520, 0, 600831078353880, 0, 212557232350320, 3586004682310050, 0, 75226620793252500, 572857170056542800, 0, 0] }

theorem case_52_31_20_checked :
    (Witness.linear .conditional case_52_31_20).check 52 31 20 = true := by
  change case_52_31_20.check 52 31 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_32_1_checked :
    (Witness.rising).check 52 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_32_2_checked :
    (Witness.rising).check 52 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_32_3_checked :
    (Witness.rising).check 52 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_32_4_checked :
    (Witness.rising).check 52 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_32_5_checked :
    (Witness.rising).check 52 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_32_6_checked :
    (Witness.rising).check 52 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_32_7_checked :
    (Witness.rising).check 52 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_32_8_checked :
    (Witness.rising).check 52 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_32_9_checked :
    (Witness.rising).check 52 32 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_32_10_checked :
    (Witness.linear .positive case_52_32_10).check 52 32 10 = true := by
  change case_52_32_10.check 52 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_32_11_checked :
    (Witness.linear .positive case_52_32_11).check 52 32 11 = true := by
  change case_52_32_11.check 52 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_32_12_checked :
    (Witness.linear .positive case_52_32_12).check 52 32 12 = true := by
  change case_52_32_12.check 52 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_32_13_checked :
    (Witness.linear .positive case_52_32_13).check 52 32 13 = true := by
  change case_52_32_13.check 52 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_32_14_checked :
    (Witness.linear .positive case_52_32_14).check 52 32 14 = true := by
  change case_52_32_14.check 52 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_32_15 : Certificate := {
  objectiveScale := 27042978967804800000
  eta := 691048029349438189171142400
  rows := #[⟨.count 2, 143070557336002418810688000⟩, ⟨.count 3, 28068259943227783770691200⟩, ⟨.count 4, 5945218765746001764422400⟩, ⟨.count 5, 1187184816070655554152000⟩, ⟨.count 6, 257293791098586915472800⟩, ⟨.count 7, 53233198158328327339200⟩, ⟨.count 8, 11829599590739628297600⟩, ⟨.count 9, 2632410897939312890400⟩, ⟨.count 10, 620433544968861624000⟩, ⟨.count 11, 194993399847356510400⟩, ⟨.path 10, 49166694986506272000⟩, ⟨.path 11, 22673584760467761120⟩, ⟨.privateRow 2 30, 15125833019559291868238400⟩, ⟨.privateRow 3 29, 24759633600551154875169600⟩, ⟨.privateRow 5 22, 65555697732015440149200⟩, ⟨.privateRow 6 20, 45125496398008480053600⟩, ⟨.privateRow 6 21, 85025247058441078389000⟩, ⟨.privateRow 7 17, 3148524380868625558800⟩, ⟨.privateRow 7 18, 18529015685495234119200⟩, ⟨.privateRow 7 19, 39498101840508919264800⟩, ⟨.privateRow 7 20, 67034397680857893686400⟩, ⟨.privateRow 7 21, 72118308933544805371440⟩, ⟨.privateRow 7 23, 392197498676315788856400⟩, ⟨.privateRow 8 15, 2510540023034715071400⟩, ⟨.privateRow 8 16, 7501829410794132414000⟩, ⟨.privateRow 8 17, 16042269499941892907700⟩, ⟨.privateRow 8 18, 27763345978266474576000⟩, ⟨.privateRow 8 19, 51397010309765720199600⟩, ⟨.privateRow 8 21, 173154139064452581235200⟩, ⟨.privateRow 8 24, 1051453160326908143204400⟩, ⟨.privateRow 9 12, 123676369347628897800⟩, ⟨.privateRow 9 13, 1270411544460049992000⟩, ⟨.privateRow 9 14, 3347386697379620095200⟩, ⟨.privateRow 9 15, 6687551416987115875200⟩, ⟨.privateRow 9 16, 11679292178357290987500⟩, ⟨.privateRow 9 17, 21902711016187592791200⟩, ⟨.privateRow 9 18, 34241202112084409442000⟩, ⟨.privateRow 9 19, 16591771733678401740480⟩, ⟨.privateRow 9 21, 179787525648148764746400⟩, ⟨.privateRow 10 10, 123404913889410938400⟩, ⟨.privateRow 10 11, 610831597249105432200⟩, ⟨.privateRow 10 12, 1589760239251381797600⟩, ⟨.privateRow 10 13, 3108372060293996736240⟩, ⟨.privateRow 10 14, 5308153662511371672000⟩, ⟨.privateRow 10 15, 10058778847807669079100⟩, ⟨.privateRow 10 16, 16173056469157692904800⟩, ⟨.privateRow 10 17, 23764081995033516536400⟩, ⟨.privateRow 10 18, 17951801456856176189280⟩, ⟨.privateRow 10 19, 10170678469310981622000⟩, ⟨.privateRow 11 8, 84834790842681079200⟩, ⟨.privateRow 11 9, 320443699049851608000⟩, ⟨.privateRow 11 10, 813949722090101797200⟩, ⟨.privateRow 11 11, 1626019342528782801600⟩, ⟨.privateRow 11 12, 2783973949638849087120⟩, ⟨.privateRow 11 13, 5193915105025041595200⟩, ⟨.privateRow 11 14, 8608515436442955033000⟩, ⟨.privateRow 11 15, 13062025407956686761600⟩, ⟨.privateRow 11 17, 50895050027431388819040⟩, ⟨.privateRow 12 6, 52720437736507500960⟩, ⟨.privateRow 12 7, 190350699850990879200⟩, ⟨.privateRow 12 8, 472484007322440775200⟩, ⟨.privateRow 12 10, 3635937536547677961600⟩, ⟨.privateRow 12 11, 2233757724918050691360⟩, ⟨.privateRow 12 13, 19044355385091819182400⟩, ⟨.privateRow 12 14, 6942384061232073854400⟩, ⟨.privateRow 12 15, 4591372368628033388400⟩, ⟨.privateRow 12 16, 28586032417622464424640⟩, ⟨.privateRow 12 20, 137210355692589864484800⟩, ⟨.privateRow 13 4, 33514490598764400225⟩, ⟨.privateRow 13 5, 127829006566600379040⟩, ⟨.privateRow 13 6, 321506974748319960600⟩, ⟨.privateRow 13 7, 548731426493522487600⟩, ⟨.privateRow 13 8, 20311812484099636500⟩, ⟨.privateRow 13 9, 5024034491521662817200⟩, ⟨.privateRow 13 11, 5949104189787404646000⟩, ⟨.privateRow 13 12, 16259605893521759018250⟩, ⟨.privateRow 13 13, 13252587139625694260400⟩, ⟨.privateRow 13 14, 6954764594555715537600⟩, ⟨.privateRow 13 16, 48598042549456790289900⟩, ⟨.privateRow 14 2, 23076949981935049200⟩, ⟨.privateRow 14 3, 96190940549700421425⟩, ⟨.privateRow 14 4, 259526929796838784080⟩, ⟨.privateRow 14 5, 543195899574778850400⟩, ⟨.privateRow 14 6, 865863549322190218800⟩, ⟨.privateRow 14 7, 37721937470470753500⟩, ⟨.privateRow 14 8, 7898287852908021769200⟩, ⟨.privateRow 14 9, 721243444435400806920⟩, ⟨.privateRow 14 10, 7651685449565711954400⟩, ⟨.privateRow 14 12, 6518350794897346204800⟩, ⟨.privateRow 14 15, 25560384829990982571600⟩, ⟨.privateRow 14 18, 407457279781036891005600⟩, ⟨.privateRow 15 1, 120118483239302948400⟩, ⟨.privateRow 15 2, 228846420654189237900⟩, ⟨.privateRow 15 3, 568008551777577390480⟩, ⟨.privateRow 15 4, 1076332615824098833200⟩, ⟨.privateRow 15 5, 1841604331891700376000⟩, ⟨.privateRow 15 7, 14332507296356075626800⟩, ⟨.privateRow 15 8, 3562962733877530903920⟩, ⟨.privateRow 15 9, 11399290081817221183600⟩, ⟨.privateRow 15 10, 4374487348658925047550⟩, ⟨.privateRow 15 12, 10562142491731810980000⟩, ⟨.privateRow 16 0, 509468049601181470800⟩, ⟨.privateRow 16 1, 580917837045249603900⟩, ⟨.privateRow 16 2, 1478699948842453537200⟩, ⟨.privateRow 16 3, 3017754997637660280000⟩, ⟨.privateRow 16 4, 4809837196234793923200⟩, ⟨.privateRow 16 5, 457692841308378475800⟩, ⟨.privateRow 16 6, 31763243056953482474400⟩, ⟨.privateRow 16 7, 16202326582316598043320⟩, ⟨.privateRow 16 9, 59676105078284732037000⟩, ⟨.privateRow 16 11, 7780778302242434088600⟩, ⟨.privateRow 16 12, 22560736362339148253280⟩, ⟨.privateRow 17 0, 6390096207497745642900⟩, ⟨.privateRow 17 1, 3210891317486470537920⟩, ⟨.privateRow 17 2, 10562142491731810980000⟩, ⟨.privateRow 17 3, 16379445587177946873600⟩, ⟨.privateRow 17 4, 3802371297023451952800⟩, ⟨.privateRow 17 5, 64141010767971361224000⟩, ⟨.privateRow 17 7, 235371477571303556683200⟩, ⟨.privateRow 17 9, 104414322918263045688000⟩, ⟨.privateRow 17 11, 70808603264570060809920⟩, ⟨.privateRow 18 0, 84591025644892103937600⟩, ⟨.privateRow 18 3, 236216448970642101561600⟩, ⟨.privateRow 18 4, 129715912395426313756800⟩, ⟨.privateRow 18 5, 106776219163080787800480⟩, ⟨.privateRow 18 6, 705989251765860515252800⟩, ⟨.privateRow 18 8, 1224403794374853364272000⟩, ⟨.privateRow 19 0, 1034244992790378931161600⟩, ⟨.privateRow 19 2, 1098885304839777614359200⟩, ⟨.privateRow 19 4, 3533670392033794681468800⟩, ⟨.privateRow 19 8, 18932429173579436545430400⟩, ⟨.hall 14 5, 7725189808767431000⟩, ⟨.hall 14 10, 8807015228795984200⟩, ⟨.hall 15 11, 45761318714177416350⟩, ⟨.hall 13 12, 3598811181393327900⟩, ⟨.hall 16 12, 532981959582774461760⟩, ⟨.hall 17 12, 5303820475848097082880⟩, ⟨.hall 18 13, 43093541366265788798400⟩, ⟨.hall 10 15, 312939457127797500⟩, ⟨.hall 12 17, 30218275414941213600⟩, ⟨.hall 8 19, 8948360770333704720⟩, ⟨.hall 6 21, 33721783483483551456⟩, ⟨.hall 9 22, 203691801075329892124800⟩, ⟨.hall 4 27, 8140092330627824839272000⟩, ⟨.hall 3 28, 11950780144182697544126400⟩]
  caps := #[0, 0, 25492260488938198956000, 0, 351125070031587962880, 0, 559083826009846573800, 102710113659570474900, 0, 190593443506485440400, 0, 110206490221396596720, 191115354940085212560, 27480687478487743500, 27042978967804800000, 253860313089236303450, 0, 10419381811641545783040, 0, 0, 0] }

theorem case_52_32_15_checked :
    (Witness.linear .positive case_52_32_15).check 52 32 15 = true := by
  change case_52_32_15.check 52 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_32_16 : Certificate := {
  objectiveScale := 1729072800000
  eta := 33599642608111900320
  rows := #[⟨.count 2, 6684474002334448320⟩, ⟨.count 3, 1325941371743788800⟩, ⟨.count 4, 287909008851784320⟩, ⟨.count 5, 60298964236110600⟩, ⟨.count 6, 13818954194004960⟩, ⟨.count 7, 3094428393136080⟩, ⟨.count 8, 730402486894080⟩, ⟨.count 9, 185861347111440⟩, ⟨.count 10, 44464437108000⟩, ⟨.count 11, 9782176163760⟩, ⟨.path 11, 2412965427600⟩, ⟨.privateRow 2 30, 389134967794372800⟩, ⟨.privateRow 3 27, 41956115869187520⟩, ⟨.privateRow 3 28, 164301430846512960⟩, ⟨.privateRow 4 25, 34123491184582800⟩, ⟨.privateRow 4 26, 61605971662435200⟩, ⟨.privateRow 4 27, 108516940909977600⟩, ⟨.privateRow 5 22, 3497127978544200⟩, ⟨.privateRow 5 23, 13128006484304712⟩, ⟨.privateRow 5 24, 23414861419980030⟩, ⟨.privateRow 5 25, 40736242271284560⟩, ⟨.privateRow 5 26, 49320101854983960⟩, ⟨.privateRow 6 19, 65350371316230⟩, ⟨.privateRow 6 20, 2402067702434400⟩, ⟨.privateRow 6 21, 5025502428426480⟩, ⟨.privateRow 6 22, 8668638443785320⟩, ⟨.privateRow 6 23, 14936975411388030⟩, ⟨.privateRow 6 24, 18856231464110040⟩, ⟨.privateRow 6 25, 18389947733637480⟩, ⟨.privateRow 7 17, 204209397111720⟩, ⟨.privateRow 7 18, 1029079109703645⟩, ⟨.privateRow 7 19, 2081407524150240⟩, ⟨.privateRow 7 20, 3307889451566700⟩, ⟨.privateRow 7 21, 5624471803414464⟩, ⟨.privateRow 7 22, 7108556027382810⟩, ⟨.privateRow 7 23, 7266759435936000⟩, ⟨.privateRow 7 24, 4547780280323280⟩, ⟨.privateRow 8 15, 152928020693448⟩, ⟨.privateRow 8 16, 437480656212600⟩, ⟨.privateRow 8 17, 867760543860210⟩, ⟨.privateRow 8 18, 1372066661445480⟩, ⟨.privateRow 8 19, 2242563885541980⟩, ⟨.privateRow 8 20, 2869764413908392⟩, ⟨.privateRow 8 21, 2922425128923300⟩, ⟨.privateRow 9 12, 4347633850560⟩, ⟨.privateRow 9 13, 79937176934160⟩, ⟨.privateRow 9 14, 202925809974888⟩, ⟨.privateRow 9 15, 380659497137920⟩, ⟨.privateRow 9 16, 606223195037460⟩, ⟨.privateRow 9 17, 996073969690800⟩, ⟨.privateRow 9 18, 1277660897833320⟩, ⟨.privateRow 9 19, 38476559577456⟩, ⟨.privateRow 10 10, 4788477842400⟩, ⟨.privateRow 10 11, 38535845493600⟩, ⟨.privateRow 10 12, 100489627864080⟩, ⟨.privateRow 10 13, 186039204859872⟩, ⟨.privateRow 10 14, 293465284912800⟩, ⟨.privateRow 10 15, 491332030043400⟩, ⟨.privateRow 10 16, 7368392435040⟩, ⟨.privateRow 11 8, 3303072470880⟩, ⟨.privateRow 11 9, 19564352327520⟩, ⟨.privateRow 11 10, 52838572763340⟩, ⟨.privateRow 11 11, 102268205348400⟩, ⟨.privateRow 11 12, 149311579808664⟩, ⟨.privateRow 12 6, 1956435232752⟩, ⟨.privateRow 12 7, 10946720945160⟩, ⟨.privateRow 12 8, 30517045297200⟩, ⟨.privateRow 12 9, 44382095557800⟩, ⟨.privateRow 13 4, 1018976683725⟩, ⟨.privateRow 13 5, 6847523314632⟩, ⟨.privateRow 13 6, 13159356029820⟩, ⟨.privateRow 14 2, 534320546760⟩, ⟨.privateRow 14 3, 3784770539550⟩, ⟨.privateRow 15 1, 831165294960⟩, ⟨.hall 6 25, 1752639896007000⟩, ⟨.hall 5 26, 15134596504227200⟩, ⟨.hall 4 27, 46410370264177920⟩, ⟨.hall 3 28, 107993650704619680⟩, ⟨.hall 2 29, 208691641987500672⟩, ⟨.assumptionRow 16, 2285889723936⟩]
  caps := #[0, 0, 371228644921680, 0, 0, 1157425561656, 25369431616620, 11707664271030, 3864135186912, 7958742139712, 6279971688984, 5240402550264, 9882216622992, 2507043740292, 3750306888510, 0, 23650202276064, 1729072800000, 0, 0, 0] }

theorem case_52_32_16_checked :
    (Witness.linear .conditional case_52_32_16).check 52 32 16 = true := by
  change case_52_32_16.check 52 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_32_17 : Certificate := {
  objectiveScale := 23270193795849850824975000
  eta := 613239524628942610653556867044480
  rows := #[⟨.count 2, 112400913973210680936868354725120⟩, ⟨.count 3, 20407461790651537619896613935200⟩, ⟨.count 4, 3991874336712970871921224346880⟩, ⟨.count 5, 739901874356097358813004097000⟩, ⟨.count 6, 148810171365824440763138767920⟩, ⟨.count 7, 30149272637313873686212129560⟩, ⟨.count 8, 6638371956839752004303588160⟩, ⟨.count 9, 1659592989209938001075897040⟩, ⟨.count 10, 580277268954523776599964000⟩, ⟨.count 11, 255321998339990461703984160⟩, ⟨.path 9, 142687687795402134302517600⟩, ⟨.path 10, 9628388498041323726643200⟩, ⟨.privateRow 2 30, 6094025456378892339950693930880⟩, ⟨.privateRow 3 27, 635316782832367377004461918720⟩, ⟨.privateRow 3 28, 2639490449727894727488932247840⟩, ⟨.privateRow 4 25, 508112053529776017996070477080⟩, ⟨.privateRow 4 26, 969571104140650445517451848480⟩, ⟨.privateRow 4 27, 1797339207314362855165196494320⟩, ⟨.privateRow 5 22, 46099805255831611140997140000⟩, ⟨.privateRow 5 23, 188972321704704940389175476288⟩, ⟨.privateRow 5 24, 360269978074324041066892649100⟩, ⟨.privateRow 5 25, 672227360240536553658020295480⟩, ⟨.privateRow 5 26, 877371493628987223235457568480⟩, ⟨.privateRow 6 20, 29951702043360309638464998960⟩, ⟨.privateRow 6 21, 69641439139809620563666346160⟩, ⟨.privateRow 6 22, 130757487627640781840324287896⟩, ⟨.privateRow 6 23, 244951315226861265797688303390⟩, ⟨.privateRow 6 24, 341046359282642259221096841720⟩, ⟨.privateRow 6 25, 371287831530467796129590965560⟩, ⟨.privateRow 7 17, 1409336903535423540596198280⟩, ⟨.privateRow 7 18, 12096259614806958823318070985⟩, ⟨.privateRow 7 19, 27676817775837843602976609480⟩, ⟨.privateRow 7 20, 48918479062902458222189536560⟩, ⟨.privateRow 7 21, 91783395127067714021406991536⟩, ⟨.privateRow 7 22, 129873029935375326786576299910⟩, ⟨.privateRow 7 23, 152432298921639781638502828920⟩, ⟨.privateRow 7 24, 123264293567628609389434781340⟩, ⟨.privateRow 8 15, 976606643650463516017739412⟩, ⟨.privateRow 8 16, 4723456969289823541523706960⟩, ⟨.privateRow 8 17, 11077251282146461177053062775⟩, ⟨.privateRow 8 18, 19766178038154261576916773720⟩, ⟨.privateRow 8 19, 36298277430668643972249748080⟩, ⟨.privateRow 8 20, 52600587024677034952049136696⟩, ⟨.privateRow 8 21, 62958149424002648015174094120⟩, ⟨.privateRow 8 22, 53993510371176316248678650280⟩, ⟨.privateRow 9 13, 456484784910892037591971680⟩, ⟨.privateRow 9 14, 1943284098476594069635879440⟩, ⟨.privateRow 9 15, 4595795970119828310671714880⟩, ⟨.privateRow 9 16, 8452221986713434242658975630⟩, ⟨.privateRow 9 17, 15748909294431792606058451520⟩, ⟨.privateRow 9 18, 23130281775541358123257231680⟩, ⟨.privateRow 9 19, 28817342879306923444323012192⟩, ⟨.privateRow 9 20, 3124148340799049955016806180⟩, ⟨.privateRow 10 11, 178918824594311497784988900⟩, ⟨.privateRow 10 12, 840874515194100818091220560⟩, ⟨.privateRow 10 13, 2050699868485287026504272776⟩, ⟨.privateRow 10 14, 3878831166700461155583759360⟩, ⟨.privateRow 10 15, 7463816371927562076517036950⟩, ⟨.privateRow 10 16, 11448041548945676221207861200⟩, ⟨.privateRow 10 17, 4203141684793933888505739240⟩, ⟨.privateRow 11 9, 62491398195102560556919200⟩, ⟨.privateRow 11 10, 373311709694076962945976840⟩, ⟨.privateRow 11 11, 993856704282111631922120160⟩, ⟨.privateRow 11 12, 1963658278142108460014278176⟩, ⟨.privateRow 11 13, 3909779287711369090335757440⟩, ⟨.privateRow 11 14, 2641712266915469492971336110⟩, ⟨.privateRow 12 7, 19250468128808804652284520⟩, ⟨.privateRow 12 8, 168032426257942440608604960⟩, ⟨.privateRow 12 9, 516554228123036258169634620⟩, ⟨.privateRow 12 10, 1107684831182079831331931280⟩, ⟨.privateRow 12 11, 1259588525143952944406321856⟩, ⟨.privateRow 13 5, 2836911092666560685599824⟩, ⟨.privateRow 13 6, 75988689982140018364281000⟩, ⟨.privateRow 13 7, 283145549441143268428136280⟩, ⟨.privateRow 13 8, 507097857814147722550968540⟩, ⟨.privateRow 14 4, 31611295032570247639540896⟩, ⟨.privateRow 14 5, 160878912219330724594092060⟩, ⟨.privateRow 14 6, 27355928393570406611141160⟩, ⟨.privateRow 15 2, 11524951313957902785249285⟩, ⟨.privateRow 15 3, 36879844204665288912797712⟩, ⟨.hall 6 25, 79256203651372039153945083000⟩, ⟨.hall 5 26, 336733466390930012934350220400⟩, ⟨.hall 4 27, 883061526734849867810574929760⟩, ⟨.hall 3 28, 1897735045270821518379707369280⟩, ⟨.hall 2 29, 3494660277145673446798885593696⟩, ⟨.assumptionRow 17, 24451247801449638647694216⟩]
  caps := #[0, 0, 0, 3217576813231631517850622712, 0, 739323120476160574053178752, 383632529359767354283974630, 315859006904471967149223426, 0, 219083587012122789807682104, 0, 0, 111719244078193973665995012, 57951202142797410886647516, 141300934018529394367100700, 1401345173533833077195646, 2053331437746639906081986760, 301331465340448272901955784, 23270193795849850824975000, 0, 0] }

theorem case_52_32_17_checked :
    (Witness.linear .conditional case_52_32_17).check 52 32 17 = true := by
  change case_52_32_17.check 52 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_32_18 : Certificate := {
  objectiveScale := 91182294279876880080000000
  eta := 1969103451755770148249147186870400
  rows := #[⟨.count 2, 356343214358298497967084358310400⟩, ⟨.count 3, 62246886355691888256500670576000⟩, ⟨.count 4, 11133744073399027835845701811200⟩, ⟨.count 5, 1894194784697015698154273016000⟩, ⟨.count 6, 342381651459878988118261900800⟩, ⟨.count 7, 64989109767847400522447860800⟩, ⟨.count 8, 14631694506832435389669312000⟩, ⟨.count 9, 5486885440062163271125992000⟩, ⟨.count 10, 1995231069113513916773088000⟩, ⟨.count 11, 731584725341621769483465600⟩, ⟨.count 12, 487723150227747846322310400⟩, ⟨.path 8, 1190205517700781038814156800⟩, ⟨.path 9, 128763509724347402176272000⟩, ⟨.privateRow 2 30, 35893009794710647254397789267200⟩, ⟨.privateRow 3 27, 3988112199412294139377532140800⟩, ⟨.privateRow 3 28, 10949344079017086837615341620800⟩, ⟨.privateRow 4 24, 202258790399447031869862122880⟩, ⟨.privateRow 4 25, 2010699652207668964944514912800⟩, ⟨.privateRow 4 26, 3962750595600451251368772000000⟩, ⟨.privateRow 4 27, 7583119539741023514619282099200⟩, ⟨.privateRow 5 22, 200779363510422863402684448000⟩, ⟨.privateRow 5 23, 697761124873327456341013373760⟩, ⟨.privateRow 5 24, 1403804398491459855797387481000⟩, ⟨.privateRow 5 25, 2816458939979760719389498552800⟩, ⟨.privateRow 5 26, 3943729392741569085362201894400⟩, ⟨.privateRow 6 20, 97294962242456793581225659200⟩, ⟨.privateRow 6 21, 245690536927227977584863864000⟩, ⟨.privateRow 6 22, 493441704164168189820439489440⟩, ⟨.privateRow 6 23, 1006736788812294640410236526600⟩, ⟨.privateRow 6 24, 1545824976781562694811720526400⟩, ⟨.privateRow 6 25, 1859058396082691697058803237600⟩, ⟨.privateRow 7 17, 1673161362586857195022370400⟩, ⟨.privateRow 7 18, 35013732048269701413879792600⟩, ⟨.privateRow 7 19, 91159438191037319398834281600⟩, ⟨.privateRow 7 20, 179323899571386134484559239600⟩, ⟨.privateRow 7 21, 370687012857025068485181700800⟩, ⟨.privateRow 7 22, 586062507727909593997074459000⟩, ⟨.privateRow 7 23, 778246476494065764328337594400⟩, ⟨.privateRow 7 24, 749639191242016792437503983200⟩, ⟨.privateRow 8 15, 676715870941000136772205680⟩, ⟨.privateRow 8 16, 11976312911148030448581177600⟩, ⟨.privateRow 8 17, 34026310402607720841079936500⟩, ⟨.privateRow 8 18, 69160884570688315136526194400⟩, ⟨.privateRow 8 19, 143461732459699413379681261200⟩, ⟨.privateRow 8 20, 234472904471989777119450724800⟩, ⟨.privateRow 8 21, 320799902062301145918499665600⟩, ⟨.privateRow 8 22, 352319010645769350487078975200⟩, ⟨.privateRow 8 23, 218256109726917161229233904000⟩, ⟨.privateRow 9 12, 27095730568208213684572800⟩, ⟨.privateRow 9 14, 4027780348964150964211746720⟩, ⟨.privateRow 9 15, 12888535840277706975961795200⟩, ⟨.privateRow 9 16, 27876426305204712841359553800⟩, ⟨.privateRow 9 17, 59682217395131191813655102400⟩, ⟨.privateRow 9 18, 100552256138620680983449660800⟩, ⟨.privateRow 9 19, 143455635920321566531602232320⟩, ⟨.privateRow 9 20, 167736120082492946814347918400⟩, ⟨.privateRow 9 21, 6773932642052053421143200000⟩, ⟨.privateRow 10 12, 1112492474899656244503782400⟩, ⟨.privateRow 10 13, 4974776132323028032487566080⟩, ⟨.privateRow 10 14, 11757083818368891265133270400⟩, ⟨.privateRow 10 15, 26603080921513518890307840000⟩, ⟨.privateRow 10 16, 47229969736015608001328668800⟩, ⟨.privateRow 10 17, 70614552921042446704460872800⟩, ⟨.privateRow 10 18, 37603454882559358951450131840⟩, ⟨.privateRow 11 10, 266030809215135188903078400⟩, ⟨.privateRow 11 11, 1798731039579607243151496000⟩, ⟨.privateRow 11 12, 5184275394579946993748740320⟩, ⟨.privateRow 11 13, 12725140374123966535863916800⟩, ⟨.privateRow 11 14, 24337662311790883297305063000⟩, ⟨.privateRow 11 15, 28707574644411820473951835200⟩, ⟨.privateRow 12 8, 40643595852312320526859200⟩, ⟨.privateRow 12 9, 609653937784684807902888000⟩, ⟨.privateRow 12 10, 2224313154826546996106294400⟩, ⟨.privateRow 12 11, 6519232774710896212508215680⟩, ⟨.privateRow 12 12, 13769147083744473920710411200⟩, ⟨.privateRow 12 13, 2392891705804887871018835400⟩, ⟨.privateRow 13 7, 168827244309605023726953600⟩, ⟨.privateRow 13 8, 919561356158566251920189400⟩, ⟨.privateRow 13 9, 3342012040765135810594922400⟩, ⟨.privateRow 13 10, 4078584843779541364870320720⟩, ⟨.privateRow 14 5, 24261738340410926028788400⟩, ⟨.privateRow 14 6, 261280259050579203386952000⟩, ⟨.privateRow 14 7, 1820978249883064503605173800⟩, ⟨.privateRow 14 8, 463178641044208587822324000⟩, ⟨.privateRow 15 4, 75480963725722880978452800⟩, ⟨.privateRow 15 5, 629975735710840968166317600⟩, ⟨.privateRow 16 3, 169832168382876482201518800⟩, ⟨.hall 7 24, 27200320088201497389395251008⟩, ⟨.hall 6 25, 597095066666320300860088507200⟩, ⟨.hall 5 26, 1837248590952831435727195848000⟩, ⟨.hall 4 27, 4258937897260187836328220787200⟩, ⟨.hall 3 28, 8552326347481536639988538169600⟩, ⟨.hall 2 29, 15467408124747681324342590870400⟩, ⟨.assumptionRow 18, 71137080746738548855378065⟩]
  caps := #[0, 297300957210485834137857274950, 0, 19389792061380409072236913080, 0, 2912379266965729044725481240, 58351893655713042173598810, 184761502920948650130296148, 170094227321864170467642500, 216348845944975202422743780, 733925102378892424363007190, 106956008288929021444971840, 0, 193366028707077315341512260, 1922897021335375590921641940, 71137080746738548855378065, 71137080746738548855378065, 7210487354734579523224707090, 1114232744891660892184621935, 91182294279876880080000000, 0] }

theorem case_52_32_18_checked :
    (Witness.linear .conditional case_52_32_18).check 52 32 18 = true := by
  change case_52_32_18.check 52 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_32_19 : Certificate := {
  objectiveScale := 12347602350399994177500000
  eta := 290552836420020686201609731812000
  rows := #[⟨.count 2, 54728755925718712142403836337600⟩, ⟨.count 3, 9786144687521834380296894746400⟩, ⟨.count 4, 1804900804609485529956763353600⟩, ⟨.count 5, 307773629591635047189641292000⟩, ⟨.count 6, 53497133040606091893478422000⟩, ⟨.count 7, 8453867937280962669586713600⟩, ⟨.count 8, 1219307875569369615805776000⟩, ⟨.count 9, 152413484446171201975722000⟩, ⟨.count 10, 27711542626576582177404000⟩, ⟨.path 8, 46745231813021611796326400⟩, ⟨.path 9, 73081788776625344647932000⟩, ⟨.privateRow 2 30, 5780068018742818195246490839200⟩, ⟨.privateRow 3 27, 575861045811034464069278289600⟩, ⟨.privateRow 3 28, 1747044645913718941686779282400⟩, ⟨.privateRow 4 24, 17330429271425973472652762880⟩, ⟨.privateRow 4 25, 305065750017974738834539297800⟩, ⟨.privateRow 4 26, 624881738364017823993617913600⟩, ⟨.privateRow 4 27, 1239812569676861181511576466400⟩, ⟨.privateRow 5 22, 25636794825426252678994083300⟩, ⟨.privateRow 5 23, 104365641519463884456882225240⟩, ⟨.privateRow 5 24, 218595229729809892153629885450⟩, ⟨.privateRow 5 25, 456927158953818698456438127000⟩, ⟨.privateRow 5 26, 669737873578106265241750541100⟩, ⟨.privateRow 6 20, 13536252828146303322135868800⟩, ⟨.privateRow 6 21, 35712455136091844471826164700⟩, ⟨.privateRow 6 22, 75252633810452569263492980280⟩, ⟨.privateRow 6 23, 160959223844909995619832968250⟩, ⟨.privateRow 6 24, 261314048071734201129612226200⟩, ⟨.privateRow 6 25, 333564531384667984083966383100⟩, ⟨.privateRow 7 17, 450789088917511650287982000⟩, ⟨.privateRow 7 18, 4853190089552338362911457375⟩, ⟨.privateRow 7 19, 12920723540621063161775866800⟩, ⟨.privateRow 7 20, 26511115988582542716994494900⟩, ⟨.privateRow 7 21, 57992024430472889455745286240⟩, ⟨.privateRow 7 22, 97721901443530413626760032850⟩, ⟨.privateRow 7 23, 139558011848551130022411022800⟩, ⟨.privateRow 7 24, 147574719204253947672997530600⟩, ⟨.privateRow 8 15, 270279912417876931503613680⟩, ⟨.privateRow 8 16, 1655097542208051719232655200⟩, ⟨.privateRow 8 17, 4660042286941684500407700150⟩, ⟨.privateRow 8 18, 9869861785635629407942111800⟩, ⟨.privateRow 8 19, 21754484679950169562001386800⟩, ⟨.privateRow 8 20, 38251720236403740463853536080⟩, ⟨.privateRow 8 21, 56734649472716845175446050150⟩, ⟨.privateRow 8 22, 69134756544783257216187499200⟩, ⟨.privateRow 8 23, 52953524946081414606431680200⟩, ⟨.privateRow 9 13, 102224801689149169809979200⟩, ⟨.privateRow 9 14, 576461667838629746139286320⟩, ⟨.privateRow 9 15, 1704020389067316549496467200⟩, ⟨.privateRow 9 16, 3812877335895049569425978700⟩, ⟨.privateRow 9 17, 8711761230010515846263094000⟩, ⟨.privateRow 9 18, 15879791596130526232514946600⟩, ⟨.privateRow 9 19, 24716048031055327317725193840⟩, ⟨.privateRow 9 20, 32065256902733651375658980100⟩, ⟨.privateRow 9 21, 21392079283600384703970225600⟩, ⟨.privateRow 10 11, 28866190236017273101462500⟩, ⟨.privateRow 10 12, 202294261174009049895049200⟩, ⟨.privateRow 10 13, 647341635756828959664157440⟩, ⟨.privateRow 10 14, 1537682709745816126599506400⟩, ⟨.privateRow 10 15, 3707804403435946695336655200⟩, ⟨.privateRow 10 16, 7148786239295998870850877600⟩, ⟨.privateRow 10 17, 11688728679890002362429007200⟩, ⟨.privateRow 10 18, 16262795905832733016631311440⟩, ⟨.privateRow 10 19, 1677241117473547636287377100⟩, ⟨.privateRow 11 9, 5542308525315316435480800⟩, ⟨.privateRow 11 10, 67893279435112626334639800⟩, ⟨.privateRow 11 11, 255198115279291615870093200⟩, ⟨.privateRow 11 12, 657594906528662295069796920⟩, ⟨.privateRow 11 13, 1686709227870961301864656800⟩, ⟨.privateRow 11 14, 3495811102342635841679514600⟩, ⟨.privateRow 11 15, 6112374545062034697415968000⟩, ⟨.privateRow 11 16, 4617666719675211143494753200⟩, ⟨.privateRow 12 8, 20061262055308004362616400⟩, ⟨.privateRow 12 9, 101044495243943130198719400⟩, ⟨.privateRow 12 10, 298668848308658719023132000⟩, ⟨.privateRow 12 11, 831500231811889557445327800⟩, ⟨.privateRow 12 12, 1867723761250241173840761200⟩, ⟨.privateRow 12 13, 3204916881270877774878376500⟩, ⟨.privateRow 13 6, 3628892486813600047041000⟩, ⟨.privateRow 13 7, 37517165402134449717100800⟩, ⟨.privateRow 13 8, 139288989952195348472257050⟩, ⟨.privateRow 13 9, 445232118200330420316957600⟩, ⟨.privateRow 13 10, 1104489717286587310317398760⟩, ⟨.privateRow 13 11, 569010341932372487376028800⟩, ⟨.privateRow 14 5, 10109057641837885845328500⟩, ⟨.privateRow 14 6, 62416950773193920809105200⟩, ⟨.privateRow 14 7, 251603212419076269928176000⟩, ⟨.privateRow 14 8, 455458997026805111358618600⟩, ⟨.privateRow 15 3, 1467685405777944907914360⟩, ⟨.privateRow 15 4, 20442761009049946931664300⟩, ⟨.privateRow 15 5, 138865619162067095133435600⟩, ⟨.privateRow 15 6, 84391910832231832205075700⟩, ⟨.privateRow 16 2, 4403056217333834723743080⟩, ⟨.privateRow 16 3, 61328283027149840794992900⟩, ⟨.privateRow 16 4, 5080449481539040065857400⟩, ⟨.privateRow 17 1, 17612224869335338894972320⟩, ⟨.hall 7 24, 22207254337744928812670598288⟩, ⟨.hall 6 25, 129414289643243967597585550200⟩, ⟨.hall 5 26, 347498981241358089363856636000⟩, ⟨.hall 4 27, 754658675329777364022571094400⟩, ⟨.hall 3 28, 1453728223667412437338338544800⟩, ⟨.hall 2 29, 2549158203137858280980503652160⟩, ⟨.assumptionRow 19, 4843071575430427254715800⟩]
  caps := #[0, 0, 15922750464893238779600587800, 1001088412713569333360287080, 0, 441121799067457253386410770, 7327417629158555623494800, 83683275149091638509993790, 0, 86470324909119857737311280, 527986930377887079699600, 40327924077238680099562800, 6786916098954597428545800, 0, 5766667889226333491722320, 279689271714451219743562440, 9246127792764261978458880, 0, 887805450500203997356194600, 143328156629369502875284200, 12347602350399994177500000] }

theorem case_52_32_19_checked :
    (Witness.linear .conditional case_52_32_19).check 52 32 19 = true := by
  change case_52_32_19.check 52 32 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_32_20 : Certificate := {
  objectiveScale := 41032032425944596036000000
  eta := 1265632795824301561745161686412800
  rows := #[⟨.count 2, 242196976002146619761657154604800⟩, ⟨.count 3, 43060833072032743477873624060800⟩, ⟨.count 4, 8014266804542352610768204492800⟩, ⟨.count 5, 1375074456673356584224963884000⟩, ⟨.count 6, 229046984425706082329115021600⟩, ⟨.count 7, 34475930181723925886908316400⟩, ⟨.count 8, 4145646776935856693739638400⟩, ⟨.count 9, 365792362670810884741732800⟩, ⟨.path 8, 130347281017079494432064000⟩, ⟨.path 9, 343294164503349468521112000⟩, ⟨.privateRow 2 30, 27970678803986225112661340284800⟩, ⟨.privateRow 6 20, 35872328010649799185009693200⟩, ⟨.privateRow 6 21, 101512461090631559555896709400⟩, ⟨.privateRow 6 25, 4643947422984168821479063906800⟩, ⟨.privateRow 7 17, 1490749033583026899324442800⟩, ⟨.privateRow 7 18, 15858078722751091525566817950⟩, ⟨.privateRow 7 19, 43784350458328251173286799200⟩, ⟨.privateRow 7 20, 96681679412185295173275730200⟩, ⟨.privateRow 7 21, 141504162696612684970305464160⟩, ⟨.privateRow 7 22, 265136320207067334796937766600⟩, ⟨.privateRow 7 23, 449923154528102662792312527600⟩, ⟨.privateRow 8 15, 1042508233611811021513938480⟩, ⟨.privateRow 8 16, 5629138025545256392969999200⟩, ⟨.privateRow 8 18, 68842993588843443772405402800⟩, ⟨.privateRow 8 19, 69962869810274120746922255400⟩, ⟨.privateRow 8 20, 132496090298745549301534649040⟩, ⟨.privateRow 8 21, 217867455341579424664195812900⟩, ⟨.privateRow 8 22, 300285047055846502132567484400⟩, ⟨.privateRow 9 12, 8467415802565066776429000⟩, ⟨.privateRow 9 13, 445232118200330420316957600⟩, ⟨.privateRow 9 14, 1995600556348534937868786720⟩, ⟨.privateRow 9 15, 4509181162059316894007656800⟩, ⟨.privateRow 9 16, 5524988811173706071619922500⟩, ⟨.privateRow 9 17, 52299598519957603877954892000⟩, ⟨.privateRow 9 18, 58147437799374826567093228800⟩, ⟨.privateRow 9 20, 343346936861371405730774806800⟩, ⟨.privateRow 9 21, 75495479295670135378640964000⟩, ⟨.privateRow 10 10, 6394971375363826656324000⟩, ⟨.privateRow 10 11, 157955792971486518411202800⟩, ⟨.privateRow 10 12, 728561647964177051427748800⟩, ⟨.privateRow 10 13, 2071714926762865283582723040⟩, ⟨.privateRow 10 14, 4470795543754355257954512000⟩, ⟨.privateRow 10 15, 7766852609663751569771906100⟩, ⟨.privateRow 10 16, 40823852839111861532832218400⟩, ⟨.privateRow 10 17, 49575949758945505515375756000⟩, ⟨.privateRow 10 19, 41205678308588048868690877800⟩, ⟨.privateRow 10 20, 158875816186688860939492612800⟩, ⟨.privateRow 10 22, 367554816781861155368215694400⟩, ⟨.privateRow 11 8, 2375275082277992758063200⟩, ⟨.privateRow 11 9, 54996753828128909244386400⟩, ⟨.privateRow 11 10, 272958694871779334447429400⟩, ⟨.privateRow 11 11, 861577052571744645879288000⟩, ⟨.privateRow 11 12, 2109956855587540966987540560⟩, ⟨.privateRow 11 13, 5152499492368139179518650400⟩, ⟨.privateRow 11 14, 8560788305915170649154530700⟩, ⟨.privateRow 11 15, 33460500084050083982836298400⟩, ⟨.privateRow 11 16, 43778695041465684523862839200⟩, ⟨.privateRow 11 18, 57961462557747579282258206400⟩, ⟨.privateRow 12 6, 1354786528410410684228640⟩, ⟨.privateRow 12 7, 20321797926156160263429600⟩, ⟨.privateRow 12 8, 107861850531136542936664800⟩, ⟨.privateRow 12 9, 370872812152349924807590200⟩, ⟨.privateRow 12 10, 984683481331021220037088800⟩, ⟨.privateRow 12 11, 2686541685837844386825393120⟩, ⟨.privateRow 12 12, 5904611286322039898763156000⟩, ⟨.privateRow 12 13, 9536003676848778203614339800⟩, ⟨.privateRow 12 14, 29884655407407359107392043200⟩, ⟨.privateRow 12 15, 42296435416973021561618140800⟩, ⟨.privateRow 13 5, 8128719170462464105371840⟩, ⟨.privateRow 13 6, 47901380825939520620941200⟩, ⟨.privateRow 13 7, 173516889984871829941591200⟩, ⟨.privateRow 13 8, 495343824450056406421096500⟩, ⟨.privateRow 13 9, 1454855987895270564313710000⟩, ⟨.privateRow 13 10, 3603054772307487214706068080⟩, ⟨.privateRow 13 11, 7441165007294180683125805200⟩, ⟨.privateRow 13 12, 11690114257021331191537877400⟩, ⟨.privateRow 13 13, 30399958140534890314071865200⟩, ⟨.privateRow 13 14, 29740951264929540545529219600⟩, ⟨.privateRow 14 3, 3538170174643260045864975⟩, ⟨.privateRow 14 4, 26418337304003008342458480⟩, ⟨.privateRow 14 5, 93003330304908549777022200⟩, ⟨.privateRow 14 6, 278698942987284483612748800⟩, ⟨.privateRow 14 7, 877466203311528491374513800⟩, ⟨.privateRow 14 8, 2372503928015335099845459600⟩, ⟨.privateRow 14 9, 5519545472443485671549361000⟩, ⟨.privateRow 14 11, 38474062479070809738735738150⟩, ⟨.privateRow 14 12, 26235026392097681345796523200⟩, ⟨.privateRow 14 14, 44541316694549072065384997280⟩, ⟨.privateRow 15 2, 16511460815001880214036550⟩, ⟨.privateRow 15 3, 61642787042673686132403120⟩, ⟨.privateRow 15 4, 188702409314307202446132000⟩, ⟨.privateRow 15 5, 609653937784684807902888000⟩, ⟨.privateRow 15 6, 1783237768020203063115947400⟩, ⟨.privateRow 15 7, 4551159017371427346268983600⟩, ⟨.privateRow 15 8, 10078595681477147682647910120⟩, ⟨.privateRow 15 9, 2861986541266992570433002000⟩, ⟨.privateRow 15 10, 51301108752210841825011560850⟩, ⟨.privateRow 15 11, 62385016519309961128691239200⟩, ⟨.privateRow 15 14, 129383806946354733357190405800⟩, ⟨.privateRow 16 0, 23310297621179125008051600⟩, ⟨.privateRow 16 1, 49534382445005640642109650⟩, ⟨.privateRow 16 2, 158510023824018050054750880⟩, ⟨.privateRow 16 3, 509496505148629446604556400⟩, ⟨.privateRow 16 4, 1585100238240180500547508800⟩, ⟨.privateRow 16 5, 4425071498420503897361795400⟩, ⟨.privateRow 16 6, 10771476618950317492356934800⟩, ⟨.privateRow 16 7, 22944325948526612745425189880⟩, ⟨.privateRow 16 8, 13209168652001504171229240000⟩, ⟨.privateRow 16 9, 84802862745849656779291720800⟩, ⟨.privateRow 16 11, 302291824601054422958581157400⟩, ⟨.privateRow 17 0, 297206294670033843852657900⟩, ⟨.privateRow 17 1, 528366746080060166849169600⟩, ⟨.privateRow 17 2, 1811543129417349143482867200⟩, ⟨.privateRow 17 3, 5364954652505226309545414400⟩, ⟨.privateRow 17 4, 14133810457641609463215286800⟩, ⟨.privateRow 17 5, 32998904959727394056852683200⟩, ⟨.privateRow 17 6, 68159310244327761523542878400⟩, ⟨.privateRow 17 7, 58296464317499971742358379200⟩, ⟨.privateRow 17 8, 189221340939921547252858863000⟩, ⟨.privateRow 17 9, 148320093721045461122659752000⟩, ⟨.privateRow 17 15, 7567268537358621709613807011200⟩, ⟨.privateRow 18 0, 5988156455574015224290588800⟩, ⟨.privateRow 18 1, 7057470108355089371485336800⟩, ⟨.privateRow 18 2, 24182939532125830713481224000⟩, ⟨.privateRow 18 3, 61378603669633656048978535200⟩, ⟨.privateRow 18 4, 139632920986794082275503275200⟩, ⟨.privateRow 18 5, 282042169057536117064086732480⟩, ⟨.privateRow 18 6, 311384135689848791663110617600⟩, ⟨.privateRow 18 7, 641107000524893004950611163400⟩, ⟨.privateRow 18 10, 1697642355155233316086381924800⟩, ⟨.privateRow 19 0, 144357343125445009871290980000⟩, ⟨.privateRow 19 1, 124369403308075700812189152000⟩, ⟨.privateRow 19 6, 191995266356841863128817003400⟩, ⟨.privateRow 19 8, 27997625508036308181170647934400⟩, ⟨.privateRow 20 1, 6399842211894728770960566780000⟩, ⟨.privateRow 20 6, 1974808453956087735039260606400⟩, ⟨.privateRow 20 9, 673903384912514939582147681934000⟩, ⟨.hall 15 10, 45866678273841093000982650⟩, ⟨.hall 17 12, 5823646662838465355491396800⟩, ⟨.hall 18 13, 392651973301210426849911465600⟩, ⟨.hall 8 14, 202822579676366136527040⟩, ⟨.hall 13 17, 678997616673059775819327600⟩, ⟨.hall 7 18, 2725016673054142515540492⟩, ⟨.hall 5 23, 1391450438835517423370577570⟩, ⟨.hall 4 27, 15321805345720761886935155419200⟩, ⟨.hall 3 28, 22567400043598878789157065028800⟩, ⟨.hall 2 29, 26714962395252354120127603813440⟩]
  caps := #[0, 536527697079057620512173998400, 32766050554452112714930713600, 6866011463338800152126947200, 0, 0, 0, 293338346059552273954219460, 244123356524438534349506300, 0, 168520067823655517726233260, 353194983224657286802929000, 0, 169558861383026954121989475, 34452483000278308361014905, 425301136764896522349158940, 8711562593971146489473643750, 1094473974022981774187565600, 0, 996956043911713028271216488400, 0] }

theorem case_52_32_20_checked :
    (Witness.linear .conditional case_52_32_20).check 52 32 20 = true := by
  change case_52_32_20.check 52 32 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_33_1_checked :
    (Witness.rising).check 52 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_33_2_checked :
    (Witness.rising).check 52 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_33_3_checked :
    (Witness.rising).check 52 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_33_4_checked :
    (Witness.rising).check 52 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_33_5_checked :
    (Witness.rising).check 52 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_33_6_checked :
    (Witness.rising).check 52 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_33_7_checked :
    (Witness.rising).check 52 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_33_8_checked :
    (Witness.rising).check 52 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_33_9_checked :
    (Witness.rising).check 52 33 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_33_10_checked :
    (Witness.linear .positive case_52_33_10).check 52 33 10 = true := by
  change case_52_33_10.check 52 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_33_11_checked :
    (Witness.linear .positive case_52_33_11).check 52 33 11 = true := by
  change case_52_33_11.check 52 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_33_12_checked :
    (Witness.linear .positive case_52_33_12).check 52 33 12 = true := by
  change case_52_33_12.check 52 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_33_13_checked :
    (Witness.linear .positive case_52_33_13).check 52 33 13 = true := by
  change case_52_33_13.check 52 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_52_33_14_checked :
    (Witness.linear .positive case_52_33_14).check 52 33 14 = true := by
  change case_52_33_14.check 52 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_15 : Certificate := {
  objectiveScale := 56548182501859048000000
  eta := 9794751025585808627093577628800
  rows := #[⟨.count 2, 748643390490635054300146060800⟩, ⟨.count 3, 97440062656827077723311776000⟩, ⟨.count 4, 17885102409737957123239910400⟩, ⟨.count 5, 3216365704581413279827932000⟩, ⟨.count 6, 616156240362434675152048800⟩, ⟨.count 7, 113566506593038552125072000⟩, ⟨.count 8, 22172508430069431605371200⟩, ⟨.count 9, 4424669088040463069808000⟩, ⟨.count 10, 884933817608092613961600⟩, ⟨.count 11, 540792888538278819643200⟩, ⟨.path 2, 229158210882306284681912409600⟩, ⟨.path 9, 380411850202390050244200⟩, ⟨.path 10, 149930166339577989997632⟩, ⟨.privateRow 2 31, 70633499964873134912417995200⟩, ⟨.privateRow 3 29, 41450693320681994968011993600⟩, ⟨.privateRow 5 22, 113790549361147267636067040⟩, ⟨.privateRow 5 23, 557503388794111635170174880⟩, ⟨.privateRow 6 20, 111135352848582986181408150⟩, ⟨.privateRow 6 21, 266111488371690700602692400⟩, ⟨.privateRow 6 22, 411942544833456054210592800⟩, ⟨.privateRow 6 23, 580000372957304034067332000⟩, ⟨.privateRow 6 24, 964407546549352725044425200⟩, ⟨.privateRow 6 27, 13035696694024809887752269600⟩, ⟨.privateRow 7 18, 72981287910356294041372800⟩, ⟨.privateRow 7 19, 103962604313550725586944100⟩, ⟨.privateRow 7 20, 190844706706202394883065600⟩, ⟨.privateRow 7 21, 288146039432235061080603600⟩, ⟨.privateRow 7 23, 1584948072115294160627152800⟩, ⟨.privateRow 8 14, 439394221937351540960100⟩, ⟨.privateRow 8 15, 4510704320307916518387600⟩, ⟨.privateRow 8 16, 27458758915531107067383480⟩, ⟨.privateRow 8 17, 52494465249917092645643400⟩, ⟨.privateRow 8 19, 285451732005410421961309800⟩, ⟨.privateRow 8 20, 138104983910462953566382200⟩, ⟨.privateRow 8 23, 1947688121107633597229136600⟩, ⟨.privateRow 9 12, 680718321236994318432000⟩, ⟨.privateRow 9 13, 3232466583762893853776400⟩, ⟨.privateRow 9 14, 11647159235791360363555200⟩, ⟨.privateRow 9 15, 24660155717345514175729920⟩, ⟨.privateRow 9 16, 32267309016117302905377600⟩, ⟨.privateRow 9 17, 13083500678386313716140600⟩, ⟨.privateRow 9 18, 148781253906427253445734400⟩, ⟨.privateRow 9 19, 208492046194795523724564000⟩, ⟨.privateRow 9 21, 55554178549841369654256000⟩, ⟨.privateRow 9 22, 613144421959384910210616000⟩, ⟨.privateRow 10 10, 562565069765144590304160⟩, ⟨.privateRow 10 11, 2008119047649133239374400⟩, ⟨.privateRow 10 12, 5718884796292298517726840⟩, ⟨.privateRow 10 13, 12308624917639833630556800⟩, ⟨.privateRow 10 14, 20450820524923020308652576⟩, ⟨.privateRow 10 15, 26189124702212829747630240⟩, ⟨.privateRow 10 16, 15613551044422784057584980⟩, ⟨.privateRow 10 17, 111274106608377588401285760⟩, ⟨.privateRow 10 18, 110926454037174409160086560⟩, ⟨.privateRow 10 19, 131713549412788504662044544⟩, ⟨.privateRow 10 21, 226897030834714946219754240⟩, ⟨.privateRow 10 22, 328177706259961145887659360⟩, ⟨.privateRow 11 8, 399858984252545551493760⟩, ⟨.privateRow 11 9, 1316865800012042580300000⟩, ⟨.privateRow 11 10, 3309047394902055714600000⟩, ⟨.privateRow 11 11, 6956563066196950270864800⟩, ⟨.privateRow 11 12, 12304155554924641243617600⟩, ⟨.privateRow 11 13, 18441037499155307749833120⟩, ⟨.privateRow 11 14, 25674005819494044972960000⟩, ⟨.privateRow 11 15, 11338214538103686616383000⟩, ⟨.privateRow 11 16, 81357724945810673334374400⟩, ⟨.privateRow 11 17, 83200166518449744464500800⟩, ⟨.privateRow 11 19, 106056859890836543970481200⟩, ⟨.privateRow 12 6, 287296222035960622935450⟩, ⟨.privateRow 12 7, 973427199368901875357760⟩, ⟨.privateRow 12 8, 2327340823887949920250200⟩, ⟨.privateRow 12 9, 4778737159294983031270200⟩, ⟨.privateRow 12 10, 8703385549912924753632750⟩, ⟨.privateRow 12 11, 14177377202929650419509800⟩, ⟨.privateRow 12 12, 23686728517976612300372160⟩, ⟨.privateRow 12 13, 30224313659417138475614400⟩, ⟨.privateRow 12 14, 17516619655310187392505525⟩, ⟨.privateRow 12 15, 80423628138335464464081600⟩, ⟨.privateRow 12 19, 789670282450999218099831000⟩, ⟨.privateRow 13 4, 218134946637288935654400⟩, ⟨.privateRow 13 5, 825674856607550697848100⟩, ⟨.privateRow 13 6, 2000933687591631632679840⟩, ⟨.privateRow 13 8, 15564138187711562952148800⟩, ⟨.privateRow 13 9, 8420917835810341620158400⟩, ⟨.privateRow 13 10, 22344578894604338502530400⟩, ⟨.privateRow 13 11, 33907714111350081991628640⟩, ⟨.privateRow 13 12, 42323481538698154289695200⟩, ⟨.privateRow 13 14, 145500878490702016709512800⟩, ⟨.privateRow 13 15, 17324686464958432186426800⟩, ⟨.privateRow 13 16, 115884190401059747066400⟩, ⟨.privateRow 14 2, 195286320861045129315600⟩, ⟨.privateRow 14 3, 812325452321154109338000⟩, ⟨.privateRow 14 4, 2102815204985896660309050⟩, ⟨.privateRow 14 5, 3012988950427553423726400⟩, ⟨.privateRow 14 6, 2600496415547590752621000⟩, ⟨.privateRow 14 7, 28546138902127717694023200⟩, ⟨.privateRow 14 8, 16864368708643111524468600⟩, ⟨.privateRow 14 10, 142187970218926958654688360⟩, ⟨.privateRow 14 12, 88632091625077196547951600⟩, ⟨.privateRow 15 0, 222009712136767094379840⟩, ⟨.privateRow 15 1, 976431604305225646578000⟩, ⟨.privateRow 15 2, 2729413519799077807375680⟩, ⟨.privateRow 15 3, 4218184530598574793216960⟩, ⟨.privateRow 15 4, 9561218269356769531291776⟩, ⟨.privateRow 15 5, 5021648250712589039544000⟩, ⟨.privateRow 15 6, 74250863596305681937011360⟩, ⟨.privateRow 15 9, 411905719412950828557636144⟩, ⟨.privateRow 15 13, 278165835434472682197140640⟩, ⟨.privateRow 16 1, 23882368298241930814537200⟩, ⟨.privateRow 16 2, 6920458995513286770121575⟩, ⟨.privateRow 16 3, 31109110913164489099975080⟩, ⟨.privateRow 16 4, 17701310083761876364392600⟩, ⟨.privateRow 16 5, 241328826510206923265778000⟩, ⟨.privateRow 16 7, 36909114642737529440648400⟩, ⟨.privateRow 16 9, 1735607176652538586792395000⟩, ⟨.privateRow 16 11, 20714299034189429788119000⟩, ⟨.privateRow 17 0, 137297770995953610916473600⟩, ⟨.privateRow 17 1, 16696980433619358556483800⟩, ⟨.privateRow 17 2, 155604140462080759038670080⟩, ⟨.privateRow 17 3, 79342042361258906824795200⟩, ⟨.privateRow 17 4, 1041567103324725006632803200⟩, ⟨.privateRow 17 5, 140606151019952493107232000⟩, ⟨.privateRow 17 6, 102259018923601813168896000⟩, ⟨.privateRow 17 8, 5141498255629596164621116800⟩, ⟨.privateRow 17 9, 3400911277795100927031174000⟩, ⟨.privateRow 18 0, 2397774269112127359019265700⟩, ⟨.privateRow 18 2, 631723349939643701174635200⟩, ⟨.privateRow 18 3, 6821561496021849030979324800⟩, ⟨.privateRow 18 4, 2330546953155712573252370400⟩, ⟨.privateRow 18 5, 695361328680492329548492800⟩, ⟨.privateRow 18 7, 22761011268996531911991811200⟩, ⟨.privateRow 18 8, 31059019971863631024305628600⟩, ⟨.privateRow 19 2, 227869573100266240002498038400⟩, ⟨.privateRow 19 11, 2134063917720430959384324403200⟩, ⟨.hall 16 4, 3343826952827441642802240⟩, ⟨.hall 17 4, 53978855888813630183529120⟩, ⟨.hall 18 5, 120350999194700595498777600⟩, ⟨.hall 14 8, 13384949546036863114320⟩, ⟨.hall 15 8, 160321955926956321197700⟩, ⟨.hall 10 10, 1417823523883791460800⟩, ⟨.hall 14 10, 3713860534853364255360⟩, ⟨.hall 13 12, 15122348685463369470120⟩, ⟨.hall 17 12, 51549150696738077486703600⟩, ⟨.hall 16 13, 6687653905654883285604480⟩, ⟨.hall 14 15, 283860457102974266915400⟩, ⟨.hall 12 17, 13248748083863848275720⟩, ⟨.hall 6 18, 1319656006385489572800⟩, ⟨.hall 11 20, 877910533341361720200000⟩, ⟨.hall 7 21, 53273607748982164051200⟩, ⟨.hall 9 22, 1123801822723320511570800⟩, ⟨.hall 8 24, 21415398386115841257870720⟩, ⟨.hall 6 25, 17577914881020007189275600⟩, ⟨.hall 2 29, 731998645998066656589219840⟩, ⟨.hall 3 29, 53331913081867980635573097600⟩]
  caps := #[0, 881318079426089504292693600, 0, 0, 0, 5592563042212357470899640, 0, 0, 0, 462029158855907870487848, 435599820932963088940972, 91589693311371980662840, 113096365003718096000000, 174105882932086305050620, 6151655031252649335078090, 1430027659365834810881600, 598045565761155329707890, 152540060561399143623070080, 0, 0] }

theorem case_52_33_15_checked :
    (Witness.linear .positive case_52_33_15).check 52 33 15 = true := by
  change case_52_33_15.check 52 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_16 : Certificate := {
  objectiveScale := 21161368712484000000
  eta := 4214864587826421275370624000
  rows := #[⟨.count 2, 343811086898266323268732800⟩, ⟨.count 3, 40789012140255689761651200⟩, ⟨.count 4, 6209438394989904841166400⟩, ⟨.count 5, 968257686517507522936800⟩, ⟨.count 6, 161067722231401825039200⟩, ⟨.count 7, 33324356323738308628800⟩, ⟨.count 8, 9114353866321588684800⟩, ⟨.count 9, 2796449481712305619200⟩, ⟨.count 10, 932149827237435206400⟩, ⟨.count 11, 284823558322549646400⟩, ⟨.path 2, 83516457923053651258963200⟩, ⟨.path 7, 3224805269653927159200⟩, ⟨.privateRow 2 31, 34179681469380925216939200⟩, ⟨.privateRow 3 30, 58450920991836993334915200⟩, ⟨.privateRow 4 25, 517360631926037241462120⟩, ⟨.privateRow 5 22, 33271460520049835123040⟩, ⟨.privateRow 5 23, 274802516128901274674160⟩, ⟨.privateRow 5 24, 490682633335755628832064⟩, ⟨.privateRow 5 27, 9054042477846788797174800⟩, ⟨.privateRow 6 20, 27902536445669774288400⟩, ⟨.privateRow 6 21, 104865930812398725169200⟩, ⟨.privateRow 6 22, 210767737780363389826200⟩, ⟨.privateRow 7 18, 14105547650259601536000⟩, ⟨.privateRow 7 19, 39854953625276768378400⟩, ⟨.privateRow 7 20, 81427567689008912685600⟩, ⟨.privateRow 7 21, 143724001983546569785200⟩, ⟨.privateRow 7 22, 141964199283910816612800⟩, ⟨.privateRow 8 17, 28320164639321290535800⟩, ⟨.privateRow 8 19, 110297922960407350568400⟩, ⟨.privateRow 8 21, 300260995183631837234880⟩, ⟨.privateRow 8 22, 34810779268734114595950⟩, ⟨.privateRow 8 23, 169173325995331050393000⟩, ⟨.privateRow 8 24, 254311834637246515529400⟩, ⟨.privateRow 8 25, 1612884604891018010151600⟩, ⟨.privateRow 9 14, 826223710505908478400⟩, ⟨.privateRow 9 15, 7073981466701869399680⟩, ⟨.privateRow 9 16, 16724033783121021156800⟩, ⟨.privateRow 9 17, 7004070229659061759200⟩, ⟨.privateRow 9 18, 82092067920160315617600⟩, ⟨.privateRow 9 19, 19221274678312668561600⟩, ⟨.privateRow 9 20, 166150528094921506456320⟩, ⟨.privateRow 9 21, 110401495163433732258000⟩, ⟨.privateRow 9 23, 358800004334142768196800⟩, ⟨.privateRow 10 12, 526276256627801960280⟩, ⟨.privateRow 10 13, 2455367385836789555040⟩, ⟨.privateRow 10 14, 7126285429230192152928⟩, ⟨.privateRow 10 15, 13816531883719317392640⟩, ⟨.privateRow 10 16, 9009810673891834666860⟩, ⟨.privateRow 10 17, 62547253407631902349440⟩, ⟨.privateRow 10 20, 286245734135355649975320⟩, ⟨.privateRow 11 10, 274864692646936022400⟩, ⟨.privateRow 11 11, 1109085674074170592800⟩, ⟨.privateRow 11 12, 3090688694855435419200⟩, ⟨.privateRow 11 13, 6980766483978125879040⟩, ⟨.privateRow 11 14, 14825210060970690180800⟩, ⟨.privateRow 11 15, 9515696153048817732000⟩, ⟨.privateRow 11 16, 51837887614704035644800⟩, ⟨.privateRow 11 17, 17054889431677518220800⟩, ⟨.privateRow 11 18, 4536462492555518004480⟩, ⟨.privateRow 11 19, 133472203387560253616400⟩, ⟨.privateRow 11 20, 165879514163669141035200⟩, ⟨.privateRow 12 9, 870902803332411418800⟩, ⟨.privateRow 12 10, 261088261795670509200⟩, ⟨.privateRow 12 11, 6117233241245668542000⟩, ⟨.privateRow 12 13, 32679547434758092068200⟩, ⟨.privateRow 12 14, 4121040859479390196350⟩, ⟨.privateRow 12 15, 48460693994593804123200⟩, ⟨.privateRow 12 16, 33187878368708753589900⟩, ⟨.privateRow 12 17, 12745854234934096676400⟩, ⟨.privateRow 12 18, 71944650685036524745350⟩, ⟨.privateRow 12 19, 166787928694379697104400⟩, ⟨.privateRow 12 20, 152060177199451192471800⟩, ⟨.privateRow 13 6, 16275631904145694080⟩, ⟨.privateRow 13 7, 274651288382458587600⟩, ⟨.privateRow 13 8, 1192503029899905662400⟩, ⟨.privateRow 13 9, 411976932573687881400⟩, ⟨.privateRow 13 10, 9643311903206323742400⟩, ⟨.privateRow 13 12, 41957222746228920530400⟩, ⟨.privateRow 13 13, 13877519265769226967900⟩, ⟨.privateRow 13 15, 104469212284735173876000⟩, ⟨.privateRow 13 16, 83616058907548503336000⟩, ⟨.privateRow 14 4, 16529938652647970550⟩, ⟨.privateRow 14 5, 105791607376947011520⟩, ⟨.privateRow 14 6, 604523470725411494400⟩, ⟨.privateRow 14 7, 1993764908257847524800⟩, ⟨.privateRow 14 8, 374678609460020665800⟩, ⟨.privateRow 14 9, 16782395897524775918400⟩, ⟨.privateRow 14 11, 60286522926057442814800⟩, ⟨.privateRow 14 12, 35357538778014009006450⟩, ⟨.privateRow 14 13, 3135965504388072127200⟩, ⟨.privateRow 14 14, 95763444594340576053000⟩, ⟨.privateRow 14 16, 71938293016323967833600⟩, ⟨.privateRow 14 18, 347591549987881524725400⟩, ⟨.privateRow 15 2, 21780625048194972960⟩, ⟨.privateRow 15 3, 69425742341121476310⟩, ⟨.privateRow 15 4, 370270625819314540320⟩, ⟨.privateRow 15 6, 8373812614682959604160⟩, ⟨.privateRow 15 8, 38339840255290841947680⟩, ⟨.privateRow 15 9, 9441900958392520778160⟩, ⟨.privateRow 15 10, 62534594582817566809600⟩, ⟨.privateRow 15 11, 214340408521155704527740⟩, ⟨.privateRow 15 13, 131014089769067461516560⟩, ⟨.privateRow 15 14, 139369863558389992976448⟩, ⟨.privateRow 16 1, 81677343930731148600⟩, ⟨.privateRow 16 2, 347128711705607381550⟩, ⟨.privateRow 16 3, 1203379533912772256040⟩, ⟨.privateRow 16 5, 2029367853048166230600⟩, ⟨.privateRow 16 7, 185051160494698335037200⟩, ⟨.privateRow 16 9, 150113882884247103221400⟩, ⟨.privateRow 16 10, 506981483446039580753775⟩, ⟨.privateRow 16 12, 57391947001993753749600⟩, ⟨.privateRow 16 14, 2125469101773433997230650⟩, ⟨.privateRow 17 0, 871225001927798918400⟩, ⟨.privateRow 17 1, 1388514846822429526200⟩, ⟨.privateRow 17 2, 5924330013109032645120⟩, ⟨.privateRow 17 4, 8544706749676489392000⟩, ⟨.privateRow 17 5, 617117709698857567200⟩, ⟨.privateRow 17 6, 675912196950166906329600⟩, ⟨.privateRow 17 8, 909220092289650149008000⟩, ⟨.privateRow 17 9, 1375555374918753517288800⟩, ⟨.privateRow 17 10, 1115043541753021501420800⟩, ⟨.privateRow 17 13, 2569678143186042909820800⟩, ⟨.privateRow 17 14, 7306673682834473595648000⟩, ⟨.privateRow 18 0, 23604752395981301945400⟩, ⟨.privateRow 18 1, 37767603833570083112640⟩, ⟨.privateRow 18 3, 53262005406316783876800⟩, ⟨.privateRow 18 4, 10491001064880578642400⟩, ⟨.privateRow 18 5, 17167092651622765051200⟩, ⟨.privateRow 18 6, 6294600638928347185440⟩, ⟨.privateRow 18 11, 1422579744397806463909440⟩, ⟨.privateRow 19 0, 981957699672822160928640⟩, ⟨.privateRow 19 7, 141628514375887811672400⟩, ⟨.privateRow 19 8, 161861159286728927625600⟩, ⟨.hall 17 2, 3147300319464173592720⟩, ⟨.hall 18 2, 410048270193046616651520⟩, ⟨.hall 17 4, 1798457325408099195840⟩, ⟨.hall 13 6, 13885830818633073300⟩, ⟨.hall 16 6, 534941725084788621600⟩, ⟨.hall 12 7, 419907943863408000⟩, ⟨.hall 18 8, 19720147456223073699840⟩, ⟨.hall 14 11, 31485397477451437520⟩, ⟨.hall 15 14, 580362904930028550330⟩, ⟨.hall 9 15, 611688034430272800⟩, ⟨.hall 10 16, 2036651601817123200⟩, ⟨.hall 16 16, 107160675237119266963200⟩, ⟨.hall 11 17, 11460432991515668160⟩, ⟨.hall 8 20, 18433922221869362208⟩, ⟨.hall 9 23, 31450346775229714932600⟩, ⟨.hall 3 26, 6143411866699989962080⟩, ⟨.hall 4 26, 11168411884147715397200⟩, ⟨.hall 6 26, 2125529711548493706456000⟩]
  caps := #[0, 291764849970904080170400, 93415114913453213680800, 4774520866488802228800, 1560456385193070925560, 0, 1268340714311300830200, 659455669524296330400, 78506291391177509860, 0, 411387613463935498572, 11435603652226353600, 793577453773853947660, 50352736203450741060, 1476390712092643478560, 41052988775301635132, 1342850274930726181620, 29124246011102043962160, 0, 0] }

theorem case_52_33_16_checked :
    (Witness.linear .positive case_52_33_16).check 52 33 16 = true := by
  change case_52_33_16.check 52 33 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_17 : Certificate := {
  objectiveScale := 1754882078658121006070400000
  eta := 142592538307924627548426450067017600
  rows := #[⟨.count 2, 15656338590153006124308446579462400⟩, ⟨.count 3, 2342061345529502604860664046435200⟩, ⟨.count 4, 398789373039360274204873181942400⟩, ⟨.count 5, 65914081455400708305501598672800⟩, ⟨.count 6, 11645782795940276357995507286400⟩, ⟨.count 7, 2118515581382066905040762760000⟩, ⟨.count 8, 451949990694840939742029388800⟩, ⟨.count 9, 138666474417735288329940835200⟩, ⟨.count 10, 46222158139245096109980278400⟩, ⟨.count 11, 28246874418427558733876836800⟩, ⟨.path 2, 1974905068600899458177644502812800⟩, ⟨.path 8, 38428742659530092923845792000⟩, ⟨.path 9, 5375896774412816494676433600⟩, ⟨.privateRow 2 31, 1323422560252167981799597557753600⟩, ⟨.privateRow 3 28, 238686088835712871301259270960000⟩, ⟨.privateRow 3 29, 416415422676459070854812328105600⟩, ⟨.privateRow 4 25, 33241627987466011806994608467160⟩, ⟨.privateRow 4 26, 94808868555800949167836735416900⟩, ⟨.privateRow 4 27, 155283661256003200694646175703400⟩, ⟨.privateRow 4 28, 256610496083856309040324991211900⟩, ⟨.privateRow 5 22, 3325867699381141986923041270080⟩, ⟨.privateRow 5 23, 17736212447330664129001265826720⟩, ⟨.privateRow 5 24, 34032964174298259864924168050112⟩, ⟨.privateRow 5 25, 55733201743138955448844039769160⟩, ⟨.privateRow 5 26, 95560117720021045448663134788960⟩, ⟨.privateRow 5 27, 111466403486277910897688079538320⟩, ⟨.privateRow 6 20, 2699972447200680625227843538950⟩, ⟨.privateRow 6 21, 7065033288849868427606347808400⟩, ⟨.privateRow 6 22, 12935387122067296450190955728400⟩, ⟨.privateRow 6 23, 20356513576417226309550254966160⟩, ⟨.privateRow 6 24, 34773415634499597706334558074200⟩, ⟨.privateRow 6 25, 43431250779904897003260272106000⟩, ⟨.privateRow 6 26, 40871714058049404582987610876200⟩, ⟨.privateRow 7 17, 125900354550705690356708186880⟩, ⟨.privateRow 7 18, 1269091714942209603114895024800⟩, ⟨.privateRow 7 19, 2870588612772700656330233539800⟩, ⟨.privateRow 7 20, 5109513702198625853830966183200⟩, ⟨.privateRow 7 21, 7938380528521659274174172456400⟩, ⟨.privateRow 7 22, 13316383654401563403113365920000⟩, ⟨.privateRow 7 23, 16931479171488533286072210372600⟩, ⟨.privateRow 7 24, 17113570629793039512910237838400⟩, ⟨.privateRow 7 25, 8767628056091211177004413879600⟩, ⟨.privateRow 8 15, 94691226743592384391973487000⟩, ⟨.privateRow 8 16, 546930105926803605984690252540⟩, ⟨.privateRow 8 17, 1234623802705437879659866741800⟩, ⟨.privateRow 8 18, 2164416752312011687983312619800⟩, ⟨.privateRow 8 19, 3337670857620270645393982662600⟩, ⟨.privateRow 8 20, 5566399690081380792994604151900⟩, ⟨.privateRow 8 21, 7203659148559488166106940304920⟩, ⟨.privateRow 8 22, 5584053986592898017203277174900⟩, ⟨.privateRow 9 13, 49860013177981978674191689200⟩, ⟨.privateRow 9 14, 243483388581983006276310254400⟩, ⟨.privateRow 9 15, 567248596275513429483035749920⟩, ⟨.privateRow 9 16, 1008898464076362097807964595200⟩, ⟨.privateRow 9 17, 1554862041850716983032947698400⟩, ⟨.privateRow 9 18, 2589908225897383956638577504000⟩, ⟨.privateRow 9 19, 2900012440291896030011355244800⟩, ⟨.privateRow 10 11, 23466634132232125717374602880⟩, ⟨.privateRow 10 12, 116133172324853303976325449480⟩, ⟨.privateRow 10 13, 283846071118727840202651618720⟩, ⟨.privateRow 10 14, 523928162508343164406626455664⟩, ⟨.privateRow 10 15, 824295153483204213961314964800⟩, ⟨.privateRow 10 16, 1200042780690150807755362977960⟩, ⟨.privateRow 11 9, 10821854484981986787654112800⟩, ⟨.privateRow 11 10, 59851768872612239834718052800⟩, ⟨.privateRow 11 11, 157711715502887202930812338800⟩, ⟨.privateRow 11 12, 307213939955790638791586092800⟩, ⟨.privateRow 11 13, 405727832555595843632049110400⟩, ⟨.privateRow 12 7, 5178593643378385767877420080⟩, ⟨.privateRow 12 8, 33543163371882725996478743700⟩, ⟨.privateRow 12 9, 98320851341065156362148220400⟩, ⟨.privateRow 12 10, 143294040018481469827062703350⟩, ⟨.privateRow 13 5, 2648144476727583631300953450⟩, ⟨.privateRow 13 6, 20579865647711507077538838240⟩, ⟨.privateRow 13 7, 53179064593876373330615065200⟩, ⟨.privateRow 14 3, 1542896501846883460253776800⟩, ⟨.privateRow 14 4, 13934284032304666250416921725⟩, ⟨.privateRow 14 5, 2622924053139701882431420560⟩, ⟨.privateRow 15 2, 2160055102585636844355287520⟩, ⟨.hall 5 27, 24766960371771635024858688637800⟩, ⟨.hall 4 28, 87484466194479587682779856926400⟩, ⟨.hall 3 29, 218856782993976725070077731526400⟩, ⟨.hall 2 30, 468796062122192188318542774566400⟩, ⟨.assumptionRow 17, 1930987977160349675460132240⟩]
  caps := #[0, 41209653258960204563476701739200, 14377909879525407896700916696800, 354772531160221703861079982080, 1209698917030840320942960674880, 0, 90765461254447801236266859150, 14698815863527878177124389360, 41533104775167209284159745820, 0, 0, 20046992211107639808519355440, 6427118164732084396386183990, 2702882956993894256628843720, 0, 382230161510548541347933055280, 177935159725750804915015484160, 24392243202711465415595867760, 1754882078658121006070400000, 0] }

theorem case_52_33_17_checked :
    (Witness.linear .conditional case_52_33_17).check 52 33 17 = true := by
  change case_52_33_17.check 52 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_18 : Certificate := {
  objectiveScale := 342842898982122000000
  eta := 26114598508741201818650491200
  rows := #[⟨.count 2, 3159197114671748168900481600⟩, ⟨.count 3, 438704042883240253661942400⟩, ⟨.count 4, 63016357808189141617060800⟩, ⟨.count 5, 8522704129796072431815600⟩, ⟨.count 6, 1180634338326728648563200⟩, ⟨.count 7, 218530875122976216200400⟩, ⟨.count 8, 75051007617991831826400⟩, ⟨.count 9, 28896644644360491398400⟩, ⟨.count 10, 10836241741635184274400⟩, ⟨.count 11, 4414765153999519519200⟩, ⟨.path 2, 199670040966141208677614400⟩, ⟨.path 7, 40533634303234130658600⟩, ⟨.privateRow 2 31, 280015309422727524544298400⟩, ⟨.privateRow 3 28, 46946612647630890567172800⟩, ⟨.privateRow 3 29, 85915744661984649363151200⟩, ⟨.privateRow 4 25, 6125155543787783368926060⟩, ⟨.privateRow 4 26, 18094604790722343174366075⟩, ⟨.privateRow 4 27, 31551222864346066123842600⟩, ⟨.privateRow 4 28, 55354532883422975491489200⟩, ⟨.privateRow 5 22, 539484301818741285246240⟩, ⟨.privateRow 5 23, 3027425204355170510291400⟩, ⟨.privateRow 5 24, 6307374975519113537081040⟩, ⟨.privateRow 5 25, 11139776913086987602797360⟩, ⟨.privateRow 5 26, 20661100920717751349856000⟩, ⟨.privateRow 5 27, 26325686089814534844941520⟩, ⟨.privateRow 6 20, 370997943120031051024200⟩, ⟨.privateRow 6 21, 1146960491871477211414200⟩, ⟨.privateRow 6 22, 2319591191330580880713000⟩, ⟨.privateRow 6 23, 4010467268003606378088120⟩, ⟨.privateRow 6 24, 7505534354805379564021350⟩, ⟨.privateRow 6 25, 10453533203934576575820000⟩, ⟨.privateRow 6 26, 11195529090174638677868400⟩, ⟨.privateRow 7 17, 1702837987971243243120⟩, ⟨.privateRow 7 18, 163241197241934614602800⟩, ⟨.privateRow 7 19, 439426803007023603571800⟩, ⟨.privateRow 7 20, 886151483105352535328400⟩, ⟨.privateRow 7 21, 1532869529542261741630800⟩, ⟨.privateRow 7 22, 2859064981803717405198480⟩, ⟨.privateRow 7 23, 4101001487697410810514000⟩, ⟨.privateRow 7 24, 4824392292217046366017200⟩, ⟨.privateRow 7 25, 3771786143356303783510800⟩, ⟨.privateRow 8 16, 62413742364668207202690⟩, ⟨.privateRow 8 17, 177387716535008471792300⟩, ⟨.privateRow 8 18, 359251514406710900874900⟩, ⟨.privateRow 8 19, 626108300947574714669400⟩, ⟨.privateRow 8 20, 1173867659593663908823950⟩, ⟨.privateRow 8 21, 1730146463852411699574480⟩, ⟨.privateRow 8 22, 2119915042386144279125850⟩, ⟨.privateRow 8 23, 1275499232409694514422200⟩, ⟨.privateRow 9 14, 21708969145700116644000⟩, ⟨.privateRow 9 15, 74770068017282771493360⟩, ⟨.privateRow 9 16, 157861299446043425232000⟩, ⟨.privateRow 9 17, 278330875845333344233200⟩, ⟨.privateRow 9 18, 527077091697630947272800⟩, ⟨.privateRow 9 19, 804624394506973034794800⟩, ⟨.privateRow 9 20, 943635984553060935776640⟩, ⟨.privateRow 10 12, 7284362504099207206680⟩, ⟨.privateRow 10 13, 32147517166851046680720⟩, ⟨.privateRow 10 14, 75384121715975431935576⟩, ⟨.privateRow 10 15, 137700538576112286094320⟩, ⟨.privateRow 10 16, 264313996481384869759740⟩, ⟨.privateRow 10 17, 419878566912788068765680⟩, ⟨.privateRow 10 18, 98670001191889261254120⟩, ⟨.privateRow 11 10, 2377181236768972048800⟩, ⟨.privateRow 11 11, 14080425226013619072600⟩, ⟨.privateRow 11 12, 38419402538524744245600⟩, ⟨.privateRow 11 13, 76295168706846241872720⟩, ⟨.privateRow 11 14, 151573603620650170159200⟩, ⟨.privateRow 11 15, 84031041283513581757500⟩, ⟨.privateRow 12 8, 748933374339204204150⟩, ⟨.privateRow 12 9, 6282550411460854700400⟩, ⟨.privateRow 12 10, 20694211659372747746250⟩, ⟨.privateRow 12 11, 46555705260358569475200⟩, ⟨.privateRow 12 12, 49114262338244654651100⟩, ⟨.privateRow 13 6, 189204220885693693680⟩, ⟨.privateRow 13 7, 2838063313285405405200⟩, ⟨.privateRow 13 8, 11716107524075647954800⟩, ⟨.privateRow 13 9, 23887032886818828827100⟩, ⟨.privateRow 14 5, 1366474928618898898800⟩, ⟨.privateRow 14 6, 7027585347182908622400⟩, ⟨.privateRow 14 7, 2838063313285405405200⟩, ⟨.privateRow 15 3, 358699668762460960935⟩, ⟨.privateRow 15 4, 2295677880079750149984⟩, ⟨.hall 6 26, 1213429736613582222134400⟩, ⟨.hall 5 27, 7898566706149390359788700⟩, ⟨.hall 4 28, 22409576271623319675296400⟩, ⟨.hall 3 29, 50619697255758490807147200⟩, ⟨.hall 2 30, 101846638337860657460419200⟩, ⟨.assumptionRow 18, 291136704329234288448⟩]
  caps := #[0, 14619467386178085597788160, 403528512761191546122240, 418853277022083514296840, 0, 0, 32190651250564279654830, 2334673151491455742968, 0, 3956066871344265957216, 0, 5058168456463427492712, 1112840622664049442240, 8340425795858853378528, 291136704329234288448, 10861672508455975941042, 151861269231095487674688, 31288610929202173673280, 4508663881420473711552, 342842898982122000000] }

theorem case_52_33_18_checked :
    (Witness.linear .conditional case_52_33_18).check 52 33 18 = true := by
  change case_52_33_18.check 52 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_19 : Certificate := {
  objectiveScale := 2243829393231872846400000
  eta := 233613326280176427304128775766400
  rows := #[⟨.count 2, 22847791490674838397518003395200⟩, ⟨.count 3, 2943684196837139867517921715200⟩, ⟨.count 4, 426145095191418989213338711200⟩, ⟨.count 5, 56342600940640191810560928000⟩, ⟨.count 6, 7104740063668639571716336800⟩, ⟨.count 7, 825135723834819377107327200⟩, ⟨.count 8, 116685859936237083631339200⟩, ⟨.count 9, 27277214011068409160572800⟩, ⟨.count 10, 27277214011068409160572800⟩, ⟨.path 2, 3499742327658996529771380720000⟩, ⟨.path 7, 188912035245430298507706000⟩, ⟨.path 8, 24183687006771878374588800⟩, ⟨.privateRow 2 31, 2092477518010852662010678156800⟩, ⟨.privateRow 3 28, 333143686587477646961932051200⟩, ⟨.privateRow 3 29, 632120642091720921197716257600⟩, ⟨.privateRow 4 25, 39168942769310441037534183600⟩, ⟨.privateRow 4 26, 126466114491160526690171313750⟩, ⟨.privateRow 4 27, 229894064511160244180880094200⟩, ⟨.privateRow 4 28, 420294132786044815448395845600⟩, ⟨.privateRow 5 22, 3148375008606103025897827680⟩, ⟨.privateRow 5 23, 19571830416495461501373696720⟩, ⟨.privateRow 5 24, 43102089719589746735079109920⟩, ⟨.privateRow 5 25, 79990240662360810777205009800⟩, ⟨.privateRow 5 26, 156307377148014501357529220640⟩, ⟨.privateRow 5 27, 211273918411835211560409141360⟩, ⟨.privateRow 6 20, 2261830374299738469318191100⟩, ⟨.privateRow 6 21, 7247365564479914782539774000⟩, ⟨.privateRow 6 22, 15433590207297616644078789000⟩, ⟨.privateRow 6 23, 28216188806234342211942724080⟩, ⟨.privateRow 6 24, 56139442523786921888167078500⟩, ⟨.privateRow 6 25, 84070177630658542615501809600⟩, ⟨.privateRow 6 26, 97678566823052178686962839600⟩, ⟨.privateRow 7 17, 57152257927952857288819200⟩, ⟨.privateRow 7 18, 954918976212878990534020800⟩, ⟨.privateRow 7 19, 2681244600448100843901244500⟩, ⟨.privateRow 7 20, 5702978880382152973748601600⟩, ⟨.privateRow 7 21, 10491011345899846366078874400⟩, ⟨.privateRow 7 22, 20997025159505780357196063840⟩, ⟨.privateRow 7 23, 32681268490457667471858066600⟩, ⟨.privateRow 7 24, 42337916404211410405746523200⟩, ⟨.privateRow 7 25, 38522407851500474339454416400⟩, ⟨.privateRow 8 15, 28413764594862926208930000⟩, ⟨.privateRow 8 16, 360475960160160990503958600⟩, ⟨.privateRow 8 17, 1033503330863814169306147200⟩, ⟨.privateRow 8 18, 2219896393385153267388178575⟩, ⟨.privateRow 8 19, 4136096999525546625146577000⟩, ⟨.privateRow 8 20, 8386101624226943736695175600⟩, ⟨.privateRow 8 21, 13518056873613066138690646320⟩, ⟨.privateRow 8 22, 18344163203815129018203615750⟩, ⟨.privateRow 8 23, 19510848163504975692190175400⟩, ⟨.privateRow 8 24, 3288040838917537820897379600⟩, ⟨.privateRow 9 13, 7324437095564665422746400⟩, ⟨.privateRow 9 14, 133079741084303450753097600⟩, ⟨.privateRow 9 15, 417189834291507391216982880⟩, ⟨.privateRow 9 16, 928603921426186892102216000⟩, ⟨.privateRow 9 17, 1759569728811211477031671800⟩, ⟨.privateRow 9 18, 3623972718613374359904672000⟩, ⟨.privateRow 9 19, 6080293056504267427144718400⟩, ⟨.privateRow 9 20, 8683852620501467325208131840⟩, ⟨.privateRow 9 21, 6443105259531117147136966800⟩, ⟨.privateRow 10 12, 48303399811266974555181000⟩, ⟨.privateRow 10 13, 177053916399116764914990720⟩, ⟨.privateRow 10 14, 421705728611117605622455488⟩, ⟨.privateRow 10 15, 824681103601301570287984320⟩, ⟨.privateRow 10 16, 1728522955363891252994047620⟩, ⟨.privateRow 10 17, 3024068847612805561294645920⟩, ⟨.privateRow 10 18, 4576434580707002346915101520⟩, ⟨.privateRow 10 19, 51553934480919293313482592⟩, ⟨.privateRow 11 10, 15154007783926893978096000⟩, ⟨.privateRow 11 11, 78674557078220457902948400⟩, ⟨.privateRow 11 12, 208712016296811312516504000⟩, ⟨.privateRow 11 13, 431737681764077209435955040⟩, ⟨.privateRow 11 14, 931634722982972270897835200⟩, ⟨.privateRow 11 15, 1698953697675503901119287800⟩, ⟨.privateRow 11 16, 801863497595217361355251200⟩, ⟨.privateRow 12 8, 4762688160662738107401600⟩, ⟨.privateRow 12 9, 34460796547102984863651000⟩, ⟨.privateRow 12 10, 111997588778084700806865750⟩, ⟨.privateRow 12 11, 253829630380775474133108000⟩, ⟨.privateRow 12 12, 576761536256257584806333760⟩, ⟨.privateRow 12 13, 538977543514999862487614400⟩, ⟨.privateRow 13 6, 1428806448198821432220480⟩, ⟨.privateRow 13 7, 15308640516415943916648000⟩, ⟨.privateRow 13 8, 62372896873294704829624800⟩, ⟨.privateRow 13 9, 166694085623195833759056000⟩, ⟨.privateRow 13 10, 281215087304586218250667200⟩, ⟨.privateRow 14 4, 483710516317309339032975⟩, ⟨.privateRow 14 5, 7223410377005152796225760⟩, ⟨.privateRow 14 6, 36485593230791333001344400⟩, ⟨.privateRow 14 7, 116685859936237083631339200⟩, ⟨.privateRow 14 8, 10319157681435932566036800⟩, ⟨.privateRow 15 3, 4063168337065398447876990⟩, ⟨.privateRow 15 4, 23114913206416488947922432⟩, ⟨.privateRow 15 5, 24765978435446238158488320⟩, ⟨.privateRow 16 1, 4780198043606351115149400⟩, ⟨.privateRow 16 2, 10157920842663496119692475⟩, ⟨.hall 6 26, 18402497865227413076098960000⟩, ⟨.hall 5 27, 75122178026143409589177149400⟩, ⟨.hall 4 28, 190111443213699925722597592800⟩, ⟨.hall 3 29, 403543044121769866113948308160⟩, ⟨.hall 2 30, 778618394934524457149816179200⟩, ⟨.assumptionRow 19, 1163731909404032730420120⟩]
  caps := #[0, 0, 4616997140966399066759758800, 591923549843384318902696200, 144437396981029318333767600, 235549509455561602444946880, 12727110941023760418558960, 13505137523301319559337960, 3705153666501867654634560, 1488696070390302513912480, 181004101465110815310300, 6284032042124056263997800, 1163731909404032730420120, 13277355981125337814141440, 38053504600182110316867315, 73103790036079922103384708, 0, 866256814444004648452307520, 185652398659212097950118320, 28006050202610314272779880] }

theorem case_52_33_19_checked :
    (Witness.linear .conditional case_52_33_19).check 52 33 19 = true := by
  change case_52_33_19.check 52 33 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_20 : Certificate := {
  objectiveScale := 53557285766208224000000
  eta := 10637903385482048721324466387200
  rows := #[⟨.count 2, 833758813181843460961835385600⟩, ⟨.count 3, 99984281076409173087906662400⟩, ⟨.count 4, 15611264103085547783581094400⟩, ⟨.count 5, 2263482897412692621800534400⟩, ⟨.count 6, 309389214264288312804249600⟩, ⟨.count 7, 33839445310156534212964800⟩, ⟨.count 8, 2313808226335489518835200⟩, ⟨.path 2, 229664645982589127717754547200⟩, ⟨.path 8, 2487490128672884720985600⟩, ⟨.privateRow 2 31, 79259500793122193467699776000⟩, ⟨.privateRow 4 26, 6248312578831611723531396300⟩, ⟨.privateRow 5 22, 87123143322339521418141120⟩, ⟨.privateRow 5 23, 494306564086138410873826560⟩, ⟨.privateRow 5 24, 1536611612150530266906050496⟩, ⟨.privateRow 5 25, 3060589831385268761039260800⟩, ⟨.privateRow 5 27, 10911341143341584698447094400⟩, ⟨.privateRow 6 20, 73889503102831876788428100⟩, ⟨.privateRow 6 21, 221567796673643974013460000⟩, ⟨.privateRow 6 22, 510277349915058849243120000⟩, ⟨.privateRow 6 23, 1005192665927411716287973440⟩, ⟨.privateRow 6 24, 1748975616833864205780793800⟩, ⟨.privateRow 6 25, 2861939754286757254640930400⟩, ⟨.privateRow 6 26, 4258264485041166096933836400⟩, ⟨.privateRow 7 17, 3755806567390999951109280⟩, ⟨.privateRow 7 19, 151533779822953710898716000⟩, ⟨.privateRow 7 20, 153331112998767885792811200⟩, ⟨.privateRow 7 21, 355252198750581051481161600⟩, ⟨.privateRow 7 22, 750839033046674689896018240⟩, ⟨.privateRow 7 23, 1107777006362157312312331200⟩, ⟨.privateRow 7 24, 1444931919342471499342603200⟩, ⟨.privateRow 7 25, 1124882660035423252683720000⟩, ⟨.privateRow 8 14, 138587471889886090971900⟩, ⟨.privateRow 8 15, 2471567878131091076937600⟩, ⟨.privateRow 8 16, 4685461658329366275641280⟩, ⟨.privateRow 8 17, 36627262860637141376283600⟩, ⟨.privateRow 8 18, 90907356017509193673611100⟩, ⟨.privateRow 8 19, 123076004539229275075542000⟩, ⟨.privateRow 8 20, 290190115052909310487248000⟩, ⟨.privateRow 8 21, 501358858742656788303109680⟩, ⟨.privateRow 8 23, 2247238035490295539137045600⟩, ⟨.privateRow 9 11, 3756182185609560907200⟩, ⟨.privateRow 9 12, 109218220473878001763200⟩, ⟨.privateRow 9 13, 1183197388467011685768000⟩, ⟨.privateRow 9 14, 2963969215553726243136000⟩, ⟨.privateRow 9 15, 11458609375420526503504320⟩, ⟨.privateRow 9 16, 32849065273884146653766400⟩, ⟨.privateRow 9 17, 67159598433152546630509200⟩, ⟨.privateRow 9 18, 14070658467293415158371200⟩, ⟨.privateRow 9 19, 411218061255434972478139200⟩, ⟨.privateRow 9 20, 233747217410482975255056000⟩, ⟨.privateRow 9 21, 162873693841308975277552800⟩, ⟨.privateRow 9 22, 591703867334702910589401600⟩, ⟨.privateRow 10 9, 3155193035912031162048⟩, ⟨.privateRow 10 10, 60850151406874886696640⟩, ⟨.privateRow 10 11, 557012924416777808992320⟩, ⟨.privateRow 10 12, 1597316474430465775786800⟩, ⟨.privateRow 10 13, 4599410939168129062130880⟩, ⟨.privateRow 10 14, 12456702105780699027765504⟩, ⟨.privateRow 10 16, 121206740474560677090073920⟩, ⟨.privateRow 10 18, 274635889828372972422563040⟩, ⟨.privateRow 10 19, 226530239206340189310398208⟩, ⟨.privateRow 10 22, 148017993297223161889576800⟩, ⟨.privateRow 11 7, 3286659412408365793800⟩, ⟨.privateRow 11 8, 35057700399022568467200⟩, ⟨.privateRow 11 9, 281713663920717068040000⟩, ⟨.privateRow 11 10, 889926240898265199552000⟩, ⟨.privateRow 11 11, 2296279376135978234601600⟩, ⟨.privateRow 11 12, 5612419127516249370067200⟩, ⟨.privateRow 11 13, 12699651969545925427243200⟩, ⟨.privateRow 11 14, 3353853338173159050028800⟩, ⟨.privateRow 11 16, 248516525764299768742166400⟩, ⟨.privateRow 11 17, 76706248473061379806233600⟩, ⟨.privateRow 12 6, 22595783460307514832375⟩, ⟨.privateRow 12 7, 163894749365430507584160⟩, ⟨.privateRow 12 8, 552628304057806648471800⟩, ⟨.privateRow 12 9, 1396071790409153531797200⟩, ⟨.privateRow 12 10, 3175460768955216084443100⟩, ⟨.privateRow 12 11, 6816531621334950656341200⟩, ⟨.privateRow 12 12, 16977567860736654344453280⟩, ⟨.privateRow 12 14, 14804757323193483718172100⟩, ⟨.privateRow 12 15, 214533406485543668824501200⟩, ⟨.privateRow 13 4, 14582824955895942345600⟩, ⟨.privateRow 13 6, 619770060625577549688000⟩, ⟨.privateRow 13 7, 920801232929429502393600⟩, ⟨.privateRow 13 8, 2297916686319449068843200⟩, ⟨.privateRow 13 9, 4689593458733536792639200⟩, ⟨.privateRow 13 10, 7640074565529846885244800⟩, ⟨.privateRow 13 11, 31818994912517151400981920⟩, ⟨.privateRow 13 13, 17957837506626109502209800⟩, ⟨.privateRow 13 14, 50466990650939886188880000⟩, ⟨.privateRow 14 2, 14920390348393533603600⟩, ⟨.privateRow 14 3, 15798060368887270874400⟩, ⟨.privateRow 14 4, 318923343696911780776950⟩, ⟨.privateRow 14 5, 1235408320846984582378080⟩, ⟨.privateRow 14 6, 1937519260955674577953200⟩, ⟨.privateRow 14 7, 4255754416295632507857600⟩, ⟨.privateRow 14 9, 33277896073407904857338400⟩, ⟨.privateRow 14 10, 45172973818796262338259360⟩, ⟨.privateRow 14 12, 45924961492355296431880800⟩, ⟨.privateRow 14 13, 32419876742723663730108000⟩, ⟨.privateRow 15 1, 83554185951003788180160⟩, ⟨.privateRow 15 2, 221172845164421792241600⟩, ⟨.privateRow 15 3, 1127981510338551140432160⟩, ⟨.privateRow 15 4, 3108215717377340920301952⟩, ⟨.privateRow 15 5, 4619352851862638003674560⟩, ⟨.privateRow 15 6, 11048434280751962452438080⟩, ⟨.privateRow 15 8, 46486510729103925787507200⟩, ⟨.privateRow 15 9, 156939827471770415338794528⟩, ⟨.privateRow 15 11, 72472812039251910772766280⟩, ⟨.privateRow 15 13, 96755747331262386712625280⟩, ⟨.privateRow 16 1, 1990555606479796130174400⟩, ⟨.privateRow 16 2, 3701189330798370929543025⟩, ⟨.privateRow 16 3, 10151833593046960263889440⟩, ⟨.privateRow 16 4, 16315446845968328995536600⟩, ⟨.privateRow 16 5, 36008640522346055636872800⟩, ⟨.privateRow 16 7, 134332343503954726724193600⟩, ⟨.privateRow 16 8, 424967034020049142157816280⟩, ⟨.privateRow 16 9, 157917411447397159660502400⟩, ⟨.privateRow 16 11, 401239137248998905668011200⟩, ⟨.privateRow 17 0, 13270370709865307534496000⟩, ⟨.privateRow 17 1, 15039753471180681872428800⟩, ⟨.privateRow 17 2, 50132511570602272908096000⟩, ⟨.privateRow 17 3, 76273035460987743781603200⟩, ⟨.privateRow 17 4, 161966575843484266318464000⟩, ⟨.privateRow 17 7, 391033590250697728683148800⟩, ⟨.privateRow 17 10, 122466563979614123818348800⟩, ⟨.privateRow 17 16, 44337193233040650159920102400⟩, ⟨.privateRow 18 0, 335574499325718964278567600⟩, ⟨.privateRow 18 2, 1095753467186021107848384000⟩, ⟨.privateRow 18 5, 3056488080438583120528598400⟩, ⟨.privateRow 18 7, 1178949563768663451222057600⟩, ⟨.privateRow 19 14, 1168949798794047317852656051200⟩, ⟨.hall 14 5, 4850281692202232286000⟩, ⟨.hall 10 12, 170701964366674910400⟩, ⟨.hall 11 12, 260982651262583804400⟩, ⟨.hall 15 13, 110586422582210896120800⟩, ⟨.hall 17 13, 50906879829683897302122840⟩, ⟨.hall 8 14, 82087588967693845536⟩, ⟨.hall 6 20, 11415009147226847104800⟩, ⟨.hall 7 21, 19358533860804753066144⟩, ⟨.hall 4 24, 662873762313223081036416⟩, ⟨.hall 5 27, 4272901387972940153398968000⟩, ⟨.hall 3 29, 45125276314930517890035371520⟩, ⟨.hall 2 30, 75498592118651462955600806400⟩]
  caps := #[0, 0, 271814083373600072642937600, 0, 0, 3681537632568531470839104, 187867733831755203926700, 1245792014982808322149120, 173681902337395202150400, 264993331693445202060416, 296832017116517207561208, 0, 0, 3748898037319514556433440, 1046121720627986990915070, 9059516395210344962698800, 2270477488641017460980175, 205656066836420404402598400, 139757554138379923307161600, 3481223574803534560000000] }

theorem case_52_33_20_checked :
    (Witness.linear .conditional case_52_33_20).check 52 33 20 = true := by
  change case_52_33_20.check 52 33 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_33_21 : Certificate := {
  objectiveScale := 199344736102512000000
  eta := 47766014447800955615835926400
  rows := #[⟨.count 2, 2820681505853047884074227200⟩, ⟨.count 3, 263195685745661932767504000⟩, ⟨.count 4, 40752880373521847654323200⟩, ⟨.count 5, 6205919779102781364026400⟩, ⟨.count 6, 805701078813250814594400⟩, ⟨.count 7, 88633782863657864632800⟩, ⟨.count 8, 6219914586923358921600⟩, ⟨.path 2, 1283529658899440240867779200⟩, ⟨.path 8, 6091201712916390470400⟩, ⟨.privateRow 2 31, 304474148901778804250702400⟩, ⟨.privateRow 3 30, 506500084642342963703731200⟩, ⟨.privateRow 4 25, 2671375566151246114840680⟩, ⟨.privateRow 5 23, 1570010106982571181127200⟩, ⟨.privateRow 6 21, 684825289723500436368000⟩, ⟨.privateRow 6 22, 1029025631124689511112800⟩, ⟨.privateRow 6 23, 2115326309070631618962000⟩, ⟨.privateRow 6 24, 4644332473123335564772200⟩, ⟨.privateRow 7 17, 399851652016501644960⟩, ⟨.privateRow 7 18, 25620124369946216510400⟩, ⟨.privateRow 7 19, 189346417715314216457100⟩, ⟨.privateRow 7 20, 474490627059581952019200⟩, ⟨.privateRow 7 22, 3971459891711899838291040⟩, ⟨.privateRow 7 23, 3242130478433800837884000⟩, ⟨.privateRow 8 15, 1095553137469455264600⟩, ⟨.privateRow 8 16, 12284331309173633870160⟩, ⟨.privateRow 8 17, 58873219319281515348200⟩, ⟨.privateRow 8 18, 165896784373096463737050⟩, ⟨.privateRow 8 20, 1113818246497911075221100⟩, ⟨.privateRow 8 21, 2095877968996162330619640⟩, ⟨.privateRow 8 23, 8795866296786889171651800⟩, ⟨.privateRow 9 12, 21747953101130625600⟩, ⟨.privateRow 9 13, 612567345681845954400⟩, ⟨.privateRow 9 14, 4831999761742113542400⟩, ⟨.privateRow 9 15, 20129905390406507055360⟩, ⟨.privateRow 9 16, 58335259534932714734400⟩, ⟨.privateRow 9 17, 136661418793367209942200⟩, ⟨.privateRow 9 18, 112160407843416673540800⟩, ⟨.privateRow 9 19, 847840326988727250578400⟩, ⟨.privateRow 9 20, 1510477985095306244297280⟩, ⟨.privateRow 9 21, 1141990454328644432912400⟩, ⟨.privateRow 10 11, 274024209074245882560⟩, ⟨.privateRow 10 12, 1887178630350610036440⟩, ⟨.privateRow 10 13, 7517871969731745804000⟩, ⟨.privateRow 10 14, 22060906146255895302384⟩, ⟨.privateRow 10 15, 53547810125603826352320⟩, ⟨.privateRow 10 16, 141983686616041402292160⟩, ⟨.privateRow 10 17, 151071224161870985132160⟩, ⟨.privateRow 10 18, 660894197199638355233280⟩, ⟨.privateRow 10 19, 1162688633733583483214688⟩, ⟨.privateRow 10 20, 1244774542877552939091840⟩, ⟨.privateRow 10 21, 791597220542123302026720⟩, ⟨.privateRow 11 9, 121167167277727771200⟩, ⟨.privateRow 11 10, 804674264741833147200⟩, ⟨.privateRow 11 11, 3133517575987904305200⟩, ⟨.privateRow 11 12, 9278467627600547812800⟩, ⟨.privateRow 11 13, 23013683971616428009920⟩, ⟨.privateRow 11 14, 63015902330142717155200⟩, ⟨.privateRow 11 15, 148147056524901821587200⟩, ⟨.privateRow 11 16, 176379006500612392276800⟩, ⟨.privateRow 11 17, 545279178786947798793600⟩, ⟨.privateRow 11 18, 957301399605567877660800⟩, ⟨.privateRow 11 19, 1127712923117752177206000⟩, ⟨.privateRow 12 7, 51832621557694657680⟩, ⟨.privateRow 12 8, 388744661682709932600⟩, ⟨.privateRow 12 9, 1495171775702730510000⟩, ⟨.privateRow 12 11, 20285403255079591028400⟩, ⟨.privateRow 12 12, 27017753986948340315700⟩, ⟨.privateRow 12 13, 77748932336541986520000⟩, ⟨.privateRow 12 14, 170270161817026950478800⟩, ⟨.privateRow 12 15, 216197566847255681087400⟩, ⟨.privateRow 12 16, 510292159235503904859600⟩, ⟨.privateRow 12 17, 904686576668002555146720⟩, ⟨.privateRow 12 18, 1155835065348117307102950⟩, ⟨.privateRow 13 5, 41651213751718921350⟩, ⟨.privateRow 13 6, 222139806675834247200⟩, ⟨.privateRow 13 7, 856824968606789239200⟩, ⟨.privateRow 13 8, 1947995227772700321600⟩, ⟨.privateRow 13 9, 222139806675834247200⟩, ⟨.privateRow 13 10, 32654551581347634338400⟩, ⟨.privateRow 13 11, 40718226563680417511760⟩, ⟨.privateRow 13 12, 108478272260032390716000⟩, ⟨.privateRow 13 13, 225249763969295926660800⟩, ⟨.privateRow 13 15, 1176896695768569841665600⟩, ⟨.privateRow 13 16, 712935495545422432963680⟩, ⟨.privateRow 14 4, 180488592924115325850⟩, ⟨.privateRow 14 5, 673824080250030549840⟩, ⟨.privateRow 14 6, 1753317759834263165400⟩, ⟨.privateRow 14 7, 3665306810151265078800⟩, ⟨.privateRow 14 8, 601628643080384419500⟩, ⟨.privateRow 14 9, 60512902791285211066800⟩, ⟨.privateRow 14 10, 74938863782092683292920⟩, ⟨.privateRow 14 11, 24706882942501120160800⟩, ⟨.privateRow 14 12, 668168771005074936296700⟩, ⟨.privateRow 14 14, 1177026277322464078309800⟩, ⟨.privateRow 14 18, 5333798898093456109519200⟩, ⟨.privateRow 15 2, 237820263617657841120⟩, ⟨.privateRow 15 3, 505368060187522912380⟩, ⟨.privateRow 15 4, 1617177792600073319616⟩, ⟨.privateRow 15 5, 4042944481500183299040⟩, ⟨.privateRow 15 6, 8707880421692702490240⟩, ⟨.privateRow 15 8, 130844385037642295859840⟩, ⟨.privateRow 15 9, 170612257119307735219488⟩, ⟨.privateRow 15 10, 84452618058003828913280⟩, ⟨.privateRow 15 11, 1080476912680923986668440⟩, ⟨.privateRow 15 12, 653224315510958187316320⟩, ⟨.privateRow 15 13, 1381339364512562627172000⟩, ⟨.privateRow 15 15, 1944656295601588166838240⟩, ⟨.privateRow 15 18, 9189612806449916638717920⟩, ⟨.privateRow 16 1, 891825988566216904200⟩, ⟨.privateRow 16 2, 1895130225703210921425⟩, ⟨.privateRow 16 3, 5053680601875229123800⟩, ⟨.privateRow 16 4, 12995178690536303461200⟩, ⟨.privateRow 16 5, 25657147671058855551600⟩, ⟨.privateRow 16 7, 358351897223879883324000⟩, ⟨.privateRow 16 8, 524572046474648783050440⟩, ⟨.privateRow 16 9, 362180443134391420539000⟩, ⟨.privateRow 16 11, 7320617329002117616476000⟩, ⟨.privateRow 16 14, 10536924054909852723123000⟩, ⟨.privateRow 17 0, 9512810544706313644800⟩, ⟨.privateRow 17 1, 10107361203750458247600⟩, ⟨.privateRow 17 2, 26952963210001221993600⟩, ⟨.privateRow 17 3, 63531984709288594699200⟩, ⟨.privateRow 17 4, 124398291738467178432000⟩, ⟨.privateRow 17 6, 1411355164450973078937600⟩, ⟨.privateRow 17 9, 11562821217090524235254400⟩, ⟨.privateRow 17 10, 10684924701107627290320000⟩, ⟨.privateRow 17 16, 304838013905113820747616000⟩, ⟨.privateRow 18 0, 171825140463757790209200⟩, ⟨.privateRow 18 1, 137460112371006232167360⟩, ⟨.privateRow 18 3, 1638947493654305075841600⟩, ⟨.privateRow 18 5, 7622788049664891056553600⟩, ⟨.privateRow 18 6, 3505232865460658920267680⟩, ⟨.privateRow 18 11, 265435476988413034315172160⟩, ⟨.privateRow 19 5, 256088189347184610527791680⟩, ⟨.privateRow 19 12, 6453752275818742600257552000⟩, ⟨.hall 15 4, 545004770790465885900⟩, ⟨.hall 14 5, 81707254313084199800⟩, ⟨.hall 14 12, 115379736532453433040⟩, ⟨.hall 10 14, 2690956240124967360⟩, ⟨.hall 11 14, 4729076317183418200⟩, ⟨.hall 15 14, 3354256634774049134130⟩, ⟨.hall 17 15, 8677169593419768405564600⟩, ⟨.hall 7 23, 8594247366739294971480⟩, ⟨.hall 8 24, 9149991950531214842387328⟩, ⟨.hall 6 26, 1531185005215783706588800⟩, ⟨.hall 5 27, 69570411074157797040837600⟩, ⟨.hall 4 28, 139793170160589182771133600⟩, ⟨.hall 3 29, 201338635178709128292192000⟩]
  caps := #[0, 3083221095479312957769600, 1058005543057923922862400, 0, 60348000026655711410040, 0, 3983075843524632897900, 0, 3659951001477346579850, 0, 2463078550516017268968, 0, 650889247932161046270, 11179386542326685032680, 669577289828286659820, 0, 289543594508732337548775, 0, 3869227321455075514814880, 0] }

theorem case_52_33_21_checked :
    (Witness.linear .conditional case_52_33_21).check 52 33 21 = true := by
  change case_52_33_21.check 52 33 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_34_1_checked :
    (Witness.rising).check 52 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_34_2_checked :
    (Witness.rising).check 52 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_34_3_checked :
    (Witness.rising).check 52 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_34_4_checked :
    (Witness.rising).check 52 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_34_5_checked :
    (Witness.rising).check 52 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_34_6_checked :
    (Witness.rising).check 52 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_34_7_checked :
    (Witness.rising).check 52 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_34_8_checked :
    (Witness.rising).check 52 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_34_9_checked :
    (Witness.rising).check 52 34 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_34_10_checked :
    (Witness.linear .positive case_52_34_10).check 52 34 10 = true := by
  change case_52_34_10.check 52 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_34_11_checked :
    (Witness.linear .positive case_52_34_11).check 52 34 11 = true := by
  change case_52_34_11.check 52 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_34_12_checked :
    (Witness.linear .positive case_52_34_12).check 52 34 12 = true := by
  change case_52_34_12.check 52 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_52_34_13_checked :
    (Witness.linear .positive case_52_34_13).check 52 34 13 = true := by
  change case_52_34_13.check 52 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_52_34_14_checked :
    (Witness.linear .positive case_52_34_14).check 52 34 14 = true := by
  change case_52_34_14.check 52 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_52_34_15_checked :
    (Witness.linear .positive case_52_34_15).check 52 34 15 = true := by
  change case_52_34_15.check 52 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_16 : Certificate := {
  objectiveScale := 43242643419237405000000
  eta := 10143776060813292329333773872000
  rows := #[⟨.count 2, 1401160769715372611573916288000⟩, ⟨.count 3, 188902717065101216892706992000⟩, ⟨.count 4, 25151752991114317020448195200⟩, ⟨.count 5, 3288222565959144831865848000⟩, ⟨.count 6, 436103788588745998921200000⟩, ⟨.count 7, 72926244647340303152934000⟩, ⟨.count 8, 18501372849219527226960000⟩, ⟨.count 9, 5550411854765858168088000⟩, ⟨.count 10, 1233424856614635148464000⟩, ⟨.path 6, 18818822527234697167200000⟩, ⟨.path 7, 11513008770200881103160000⟩, ⟨.privateRow 2 32, 139340006051755332721978080000⟩, ⟨.privateRow 4 26, 3165134694428796766703666640⟩, ⟨.privateRow 4 29, 66764146570557832048843990800⟩, ⟨.privateRow 5 23, 403513683244685424906580800⟩, ⟨.privateRow 5 24, 1441484541207505061989722000⟩, ⟨.privateRow 5 25, 2224400675271059814230782080⟩, ⟨.privateRow 6 20, 36718862199694416205464000⟩, ⟨.privateRow 6 21, 231922417570320615259621500⟩, ⟨.privateRow 6 22, 552744246330339174823140000⟩, ⟨.privateRow 6 23, 982929483502523620901838000⟩, ⟨.privateRow 6 24, 1599725608496540045376055200⟩, ⟨.privateRow 6 25, 1901897078012031161961900000⟩, ⟨.privateRow 6 26, 3197125330120606778757864000⟩, ⟨.privateRow 6 27, 5195692081269809970480630000⟩, ⟨.privateRow 6 28, 27535593211493422371884568000⟩, ⟨.privateRow 7 18, 28807078035112166262072600⟩, ⟨.privateRow 7 19, 104045749561450820112990000⟩, ⟨.privateRow 7 20, 221564952591337897785243000⟩, ⟨.privateRow 7 21, 394708540084607886642648000⟩, ⟨.privateRow 7 22, 641920548814379180078733000⟩, ⟨.privateRow 7 23, 1204276384199567145687620400⟩, ⟨.privateRow 7 24, 1517398904406286772913042000⟩, ⟨.privateRow 7 25, 2360855935521261441937674000⟩, ⟨.privateRow 7 27, 13981002902390098118748204000⟩, ⟨.privateRow 8 16, 16090587902200013073144000⟩, ⟨.privateRow 8 17, 47101411711971379731969000⟩, ⟨.privateRow 8 18, 96464102327736257236122000⟩, ⟨.privateRow 8 19, 168574487825128338181478250⟩, ⟨.privateRow 8 21, 1043682999505417108125288000⟩, ⟨.privateRow 8 22, 517699247942577737689052400⟩, ⟨.privateRow 8 24, 3448912862606314590761274000⟩, ⟨.privateRow 9 14, 8294782160733421373420400⟩, ⟨.privateRow 9 15, 23289303883532701848724800⟩, ⟨.privateRow 9 17, 174406274725309409992809600⟩, ⟨.privateRow 9 18, 81113102133119943950863800⟩, ⟨.privateRow 9 19, 43222731046795714559745600⟩, ⟨.privateRow 9 20, 693308111903086416951614400⟩, ⟨.privateRow 9 21, 464261116029748669881849600⟩, ⟨.privateRow 9 22, 253592150519968986524198400⟩, ⟨.privateRow 9 23, 1264096021382452409155804800⟩, ⟨.privateRow 10 12, 4316986998151223019624000⟩, ⟨.privateRow 10 13, 12879011211151148675211600⟩, ⟨.privateRow 10 14, 15686921585489768842737600⟩, ⟨.privateRow 10 15, 24187461438212995261379040⟩, ⟨.privateRow 10 16, 143515834427427325274611200⟩, ⟨.privateRow 10 17, 84304588949610312397514400⟩, ⟨.privateRow 10 18, 51610020071775233569300800⟩, ⟨.privateRow 10 19, 491663704927537147430224800⟩, ⟨.privateRow 10 21, 1165864010093568508206884400⟩, ⟨.privateRow 11 10, 2389760659690855600149000⟩, ⟨.privateRow 11 11, 8017261567995128465016000⟩, ⟨.privateRow 11 12, 14467045714042491428859000⟩, ⟨.privateRow 11 13, 18207032826618307475622000⟩, ⟨.privateRow 11 14, 26410709742260875116485400⟩, ⟨.privateRow 11 16, 365132302084701211293733500⟩, ⟨.privateRow 11 18, 332716355071797831298164000⟩, ⟨.privateRow 11 19, 184736207899456979361195600⟩, ⟨.privateRow 11 20, 578668980386109921371563500⟩, ⟨.privateRow 11 21, 722118860845509936294486000⟩, ⟨.privateRow 12 8, 1453679295295819996404000⟩, ⟨.privateRow 12 9, 5658965828115870700287000⟩, ⟨.privateRow 12 10, 12449458580225740482024000⟩, ⟨.privateRow 12 11, 19604480496281128007059500⟩, ⟨.privateRow 12 12, 24095835591721622364636000⟩, ⟨.privateRow 12 13, 38716325231378672570893200⟩, ⟨.privateRow 12 14, 1426759308345897403878000⟩, ⟨.privateRow 12 15, 419477331648800057712329250⟩, ⟨.privateRow 12 16, 107987604793403771161440000⟩, ⟨.privateRow 12 17, 291947258471910515944470000⟩, ⟨.privateRow 12 19, 1159975507675427031297208500⟩, ⟨.privateRow 12 22, 3688711211813143240875150000⟩, ⟨.privateRow 13 6, 999404515515876247527750⟩, ⟨.privateRow 13 7, 4587165776266809766430400⟩, ⟨.privateRow 13 8, 11733268597744832828118000⟩, ⟨.privateRow 13 9, 21805189429437299946060000⟩, ⟨.privateRow 13 10, 32061704457357807698466000⟩, ⟨.privateRow 13 11, 42376954002259964743656000⟩, ⟨.privateRow 13 12, 60376146731286390517312800⟩, ⟨.privateRow 13 14, 543554916499362026988729000⟩, ⟨.privateRow 13 16, 276279826067055567094338000⟩, ⟨.privateRow 13 17, 1166723002404425129113850400⟩, ⟨.privateRow 13 20, 1617460495899149049332184000⟩, ⟨.privateRow 14 4, 815200545989420625434400⟩, ⟨.privateRow 14 5, 4409493862397320655758800⟩, ⟨.privateRow 14 6, 12934515329698807256892480⟩, ⟨.privateRow 14 7, 27896797904962640883372000⟩, ⟨.privateRow 14 8, 48165240650801502547519200⟩, ⟨.privateRow 14 9, 3989542065978528212353200⟩, ⟨.privateRow 14 10, 242693960894023960248127200⟩, ⟨.privateRow 14 12, 155382164674953204060072000⟩, ⟨.privateRow 14 13, 829457291901667424781485700⟩, ⟨.privateRow 14 15, 1333976881324294196477888400⟩, ⟨.privateRow 14 16, 1118751585659663069232518400⟩, ⟨.privateRow 14 17, 1740805184104999376027063400⟩, ⟨.privateRow 15 2, 734915643732886775959800⟩, ⟨.privateRow 15 3, 5187639838114494889128000⟩, ⟨.privateRow 15 4, 17362382083189450082050275⟩, ⟨.privateRow 15 5, 42625107336507433005668400⟩, ⟨.privateRow 15 6, 83150455690920903794308800⟩, ⟨.privateRow 15 7, 153314709677199148954075200⟩, ⟨.privateRow 15 9, 636570568498813200122270400⟩, ⟨.privateRow 15 10, 50268230031329455475650320⟩, ⟨.privateRow 15 11, 208226099057651253188610000⟩, ⟨.privateRow 15 12, 530792823686077473936965550⟩, ⟨.privateRow 15 14, 5574335157713946195655083000⟩, ⟨.privateRow 15 16, 2398764661144142436732787200⟩, ⟨.privateRow 16 1, 9798875249771823679464000⟩, ⟨.privateRow 16 2, 29828929069158345612486000⟩, ⟨.privateRow 16 4, 352759508991785652460704000⟩, ⟨.privateRow 16 5, 303940112658101030914803000⟩, ⟨.privateRow 16 6, 666511956893133468351234000⟩, ⟨.privateRow 16 7, 67979697045292026776281500⟩, ⟨.privateRow 16 8, 2393152578046545846807276000⟩, ⟨.privateRow 16 9, 963474408933814563283297800⟩, ⟨.privateRow 16 13, 29767758149400578860251699000⟩, ⟨.privateRow 16 14, 8034097817287918234792533600⟩, ⟨.privateRow 16 16, 33063854811542576050431402000⟩, ⟨.privateRow 17 0, 117586502997261884153568000⟩, ⟨.privateRow 17 1, 176379754495892826230352000⟩, ⟨.privateRow 17 5, 217082774764175786129664000⟩, ⟨.privateRow 17 7, 7375880642555518187814720000⟩, ⟨.privateRow 17 12, 269273091863729714711670720000⟩, ⟨.privateRow 17 15, 88601430008436829709713488000⟩, ⟨.privateRow 18 1, 7121332587771672859050462000⟩, ⟨.privateRow 18 6, 80140546633679304136299936000⟩, ⟨.privateRow 18 9, 62217958398426194452756668000⟩, ⟨.hall 17 4, 105827852697535695738211200⟩, ⟨.hall 14 7, 567170579230697681354115⟩, ⟨.hall 12 8, 9725441950160607871200⟩, ⟨.hall 13 9, 4239094274060344910640⟩, ⟨.hall 10 12, 321622976640546850500⟩, ⟨.hall 16 12, 26869314033310973528304000⟩, ⟨.hall 13 15, 70417613806844177402100⟩, ⟨.hall 15 15, 7275209816829428687713500⟩, ⟨.hall 17 16, 1689894427825149168113002512000⟩, ⟨.hall 9 17, 2482245072371537430048⟩, ⟨.hall 13 17, 579407177765777544097200⟩, ⟨.hall 10 19, 21410240429377889434800⟩, ⟨.hall 7 20, 3203006453755865372000⟩, ⟨.hall 7 24, 2366805252637194334885920⟩, ⟨.hall 3 29, 736385475020352549511719600⟩, ⟨.hall 4 29, 50261762773664606072021873760⟩, ⟨.hall 2 31, 122198098661685748672715745000⟩]
  caps := #[0, 1655278730151382319460048000, 238065716717417283469632000, 32313831654701835682844400, 6111653886603386692290720, 3752336839267183016352360, 1553464361672671903026000, 423744212370067100226000, 261879137383346345458500, 157617076573479291912000, 2474028580994519531804640, 1066275146791514204295450, 4680353550868836217381950, 1949879679385578178738500, 43242643419237405000000, 24719871321363998272281360, 229897066819380564530569500, 451947424544545895649684000, 0] }

theorem case_52_34_16_checked :
    (Witness.linear .positive case_52_34_16).check 52 34 16 = true := by
  change case_52_34_16.check 52 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_17 : Certificate := {
  objectiveScale := 135561912232189656259200000
  eta := 15486837202803211467281087614185600
  rows := #[⟨.count 2, 2341495580125430907958206822595200⟩, ⟨.count 3, 355418719421930587223071620148800⟩, ⟨.count 4, 53496772053777129795273927090720⟩, ⟨.count 5, 8252105730441156787048542496800⟩, ⟨.count 6, 1225079880609343707239445554400⟩, ⟨.count 7, 191039684352447162267537301800⟩, ⟨.count 8, 36020950584973202313071006400⟩, ⟨.count 9, 9262530150421680594789687360⟩, ⟨.count 10, 5145850083567600330438715200⟩, ⟨.path 7, 4153132538479851996256387200⟩, ⟨.path 8, 6546516849204627978008726400⟩, ⟨.privateRow 2 32, 186907566735342379202195013494400⟩, ⟨.privateRow 3 28, 3265363493653865384684017214100⟩, ⟨.privateRow 3 29, 36700846027264571506730221645800⟩, ⟨.privateRow 3 30, 59604381517963514627471638161600⟩, ⟨.privateRow 4 25, 554958490470750830636438606340⟩, ⟨.privateRow 4 26, 7086298691580106739043850314768⟩, ⟨.privateRow 4 27, 14634347375783943174738792641220⟩, ⟨.privateRow 4 28, 22186075342797530444669998649040⟩, ⟨.privateRow 4 29, 34622051239755350163241241672880⟩, ⟨.privateRow 5 23, 1229931682116707444693859200160⟩, ⟨.privateRow 5 24, 3209736241649299200397649650560⟩, ⟨.privateRow 5 25, 5372804125896146794726764420528⟩, ⟨.privateRow 5 26, 8018208466106996610600351324120⟩, ⟨.privateRow 5 27, 12844201084896840850499546718480⟩, ⟨.privateRow 5 28, 13505595970935383671542184678680⟩, ⟨.privateRow 6 20, 133873782332814237168080225600⟩, ⟨.privateRow 6 21, 650444639580951052482329384700⟩, ⟨.privateRow 6 22, 1284283410907532170224850160400⟩, ⟨.privateRow 6 23, 2076840589679866504792063365600⟩, ⟨.privateRow 6 24, 2988709728536062271918805788160⟩, ⟨.privateRow 6 25, 4737076617554199079189489761300⟩, ⟨.privateRow 6 26, 5293180672269744125613776034000⟩, ⟨.privateRow 6 27, 4090675145896051141252505081400⟩, ⟨.privateRow 7 17, 6983653684841743305595399200⟩, ⟨.privateRow 7 18, 98956534910606228497311649980⟩, ⟨.privateRow 7 19, 291445021102057840143597471000⟩, ⟨.privateRow 7 20, 540647360677328973110312244975⟩, ⟨.privateRow 7 21, 850653651186898135236630570600⟩, ⟨.privateRow 7 22, 1205537902315795320270279481200⟩, ⟨.privateRow 7 23, 1872593223446262501676400028120⟩, ⟨.privateRow 7 24, 2143131697080825903691777588050⟩, ⟨.privateRow 7 25, 1001020991554004442851593163400⟩, ⟨.privateRow 8 15, 6914736049793962944027023550⟩, ⟨.privateRow 8 16, 54265328153985603484626451200⟩, ⟨.privateRow 8 17, 135464503449917078698799177640⟩, ⟨.privateRow 8 18, 246857863731145715851879476400⟩, ⟨.privateRow 8 19, 383607042948453455883173597175⟩, ⟨.privateRow 8 20, 537649443552750527382087904200⟩, ⟨.privateRow 8 21, 828481863454383653200633147200⟩, ⟨.privateRow 8 22, 590743589593560517934364504960⟩, ⟨.privateRow 9 13, 4512514688666972597461642560⟩, ⟨.privateRow 9 14, 28902524636038021855964117040⟩, ⟨.privateRow 9 15, 69422195672857444457918666880⟩, ⟨.privateRow 9 16, 125918951544899180085835360944⟩, ⟨.privateRow 9 17, 196056888183925572589715049120⟩, ⟨.privateRow 9 18, 274788394462509857645427391680⟩, ⟨.privateRow 9 19, 234430227378529677910986611040⟩, ⟨.privateRow 10 11, 2683193257860248743728758640⟩, ⟨.privateRow 10 12, 16347969880872453357470687520⟩, ⟨.privateRow 10 13, 40266276903916472585682946440⟩, ⟨.privateRow 10 14, 74006680292763124752309522240⟩, ⟨.privateRow 10 15, 116656421394477499491045673584⟩, ⟨.privateRow 10 16, 49171456354090403157525500800⟩, ⟨.privateRow 11 9, 1672401277159470107392582440⟩, ⟨.privateRow 11 10, 10245755077103347086498513300⟩, ⟨.privateRow 11 11, 26867274955550067109886753400⟩, ⟨.privateRow 11 12, 51297693020564515794060942150⟩, ⟨.privateRow 11 13, 994084675234650063834751800⟩, ⟨.privateRow 12 7, 1137140978288375965878198225⟩, ⟨.privateRow 12 8, 7345088393092324757376213720⟩, ⟨.privateRow 12 9, 17761059089456538895621381800⟩, ⟨.privateRow 13 5, 951333628894850481257577600⟩, ⟨.privateRow 13 6, 5938402886617074488475035175⟩, ⟨.privateRow 14 3, 876019716607341484824686040⟩, ⟨.privateRow 14 4, 618366858781652812817425440⟩, ⟨.hall 5 28, 1040348932412304853012489214400⟩, ⟨.hall 4 29, 7809890977497770805509040983808⟩, ⟨.hall 3 30, 23597851762861600549197627354600⟩, ⟨.hall 2 31, 57028883551137930662087061204000⟩, ⟨.assumptionRow 17, 156290781061551085304691600⟩]
  caps := #[0, 0, 173351366909368466648918774400, 0, 43444299533583266918237571120, 44381355452424363779881054272, 2720652219418439024846899200, 12210437556271097990858132550, 3608519661151954593282266275, 1613638379193386291972426640, 3449578079797717450039859016, 1374699461468577256710482400, 3793170363282682676772611595, 156290781061551085304691600, 5279387316762647643858292440, 84422207239931580728528476800, 15643914873299235144812242800, 2012699814653483414842508400, 135561912232189656259200000] }

theorem case_52_34_17_checked :
    (Witness.linear .conditional case_52_34_17).check 52 34 17 = true := by
  change case_52_34_17.check 52 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_18 : Certificate := {
  objectiveScale := 376277747692000000
  eta := 47646853745607303246259200
  rows := #[⟨.count 2, 6748383625876990979481600⟩, ⟨.count 3, 938787238277242696742400⟩, ⟨.count 4, 128232894503811774156480⟩, ⟨.count 5, 17007015186181932912000⟩, ⟨.count 6, 2214649779739075879200⟩, ⟨.count 7, 376116682002100439400⟩, ⟨.count 8, 107037158514431745600⟩, ⟨.count 9, 32111147554329523680⟩, ⟨.count 10, 11893017612714638400⟩, ⟨.path 7, 78302602963956571200⟩, ⟨.privateRow 2 32, 571435710255712945843200⟩, ⟨.privateRow 3 28, 7281128376584140027950⟩, ⟨.privateRow 3 29, 104451418268467371301200⟩, ⟨.privateRow 3 30, 179530304059133029302300⟩, ⟨.privateRow 4 25, 744056914395459564900⟩, ⟨.privateRow 4 26, 18044443112539030819632⟩, ⟨.privateRow 4 27, 40965647829715730901780⟩, ⟨.privateRow 4 28, 66568291941247115739720⟩, ⟨.privateRow 4 29, 110694410093061655840980⟩, ⟨.privateRow 5 23, 2410484091184357634160⟩, ⟨.privateRow 5 24, 8039863964801006618280⟩, ⟨.privateRow 5 25, 14791244064782229652608⟩, ⟨.privateRow 5 26, 23998113214501720334040⟩, ⟨.privateRow 5 27, 41691482942125995538560⟩, ⟨.privateRow 5 28, 48506436884588898655440⟩, ⟨.privateRow 6 20, 168720388751804890000⟩, ⟨.privateRow 6 21, 1320496611811722194850⟩, ⟨.privateRow 6 22, 3117730295708626712400⟩, ⟨.privateRow 6 23, 5628512168760211130400⟩, ⟨.privateRow 6 24, 8920272910290809427360⟩, ⟨.privateRow 6 25, 15534086192378676222300⟩, ⟨.privateRow 6 26, 19617249385086779025600⟩, ⟨.privateRow 6 27, 18170407159082839861200⟩, ⟨.privateRow 7 18, 122880356977083746040⟩, ⟨.privateRow 7 19, 578840718333115238000⟩, ⟨.privateRow 7 20, 1266473641182538513725⟩, ⟨.privateRow 7 21, 2257367557286785600800⟩, ⟨.privateRow 7 22, 3564153319924666068600⟩, ⟨.privateRow 7 23, 6158501845303957629480⟩, ⟨.privateRow 7 24, 8041538190197082220650⟩, ⟨.privateRow 7 25, 8198253474364624070400⟩, ⟨.privateRow 7 26, 1928474043433129892700⟩, ⟨.privateRow 8 16, 61762602829665792600⟩, ⟨.privateRow 8 17, 252875286990344998980⟩, ⟨.privateRow 8 18, 554346765392643423200⟩, ⟨.privateRow 8 19, 984333035852334993825⟩, ⟨.privateRow 8 20, 1552251173773773072600⟩, ⟨.privateRow 8 21, 2684848726070329618800⟩, ⟨.privateRow 8 22, 3621423863071607392800⟩, ⟨.privateRow 8 23, 2303157192062269192650⟩, ⟨.privateRow 9 14, 27849482909773444920⟩, ⟨.privateRow 9 15, 117200282656206072960⟩, ⟨.privateRow 9 16, 265808943644172168240⟩, ⟨.privateRow 9 17, 478760031231834832480⟩, ⟨.privateRow 9 18, 758179872810558198000⟩, ⟨.privateRow 9 19, 1314858047211408379680⟩, ⟨.privateRow 9 20, 1424387076082789859040⟩, ⟨.privateRow 10 12, 12533410868783888160⟩, ⟨.privateRow 10 13, 58870437182937460080⟩, ⟨.privateRow 10 14, 142175619642906813600⟩, ⟨.privateRow 10 15, 264738572059027850784⟩, ⟨.privateRow 10 16, 427091476936596792320⟩, ⟨.privateRow 10 17, 643114927407544071480⟩, ⟨.privateRow 11 10, 5946508806357319200⟩, ⟨.privateRow 11 11, 32248374680630077200⟩, ⟨.privateRow 11 12, 85852720891783795950⟩, ⟨.privateRow 11 13, 169340353053766385400⟩, ⟨.privateRow 11 14, 231467855287458649860⟩, ⟨.privateRow 12 8, 3114837946187167200⟩, ⟨.privateRow 12 9, 19690225588397449800⟩, ⟨.privateRow 12 10, 59122020247821808200⟩, ⟨.privateRow 12 11, 87799494608150775450⟩, ⟨.privateRow 13 6, 1752096344730281550⟩, ⟨.privateRow 13 7, 13705286963223535680⟩, ⟨.privateRow 13 8, 35709392168788595400⟩, ⟨.privateRow 14 4, 1429160940015288480⟩, ⟨.privateRow 14 5, 11388626240746830075⟩, ⟨.privateRow 14 6, 1619715732017326944⟩, ⟨.privateRow 15 2, 2362085442525268460⟩, ⟨.privateRow 15 3, 2501031645026754840⟩, ⟨.hall 5 28, 7544244913870359895200⟩, ⟨.hall 4 29, 31298576947636817202384⟩, ⟨.hall 3 30, 81633672893673277977600⟩, ⟨.hall 2 31, 181656180957405770916300⟩, ⟨.assumptionRow 18, 344564506218603264⟩]
  caps := #[0, 15191594131424952046080, 0, 231614010270344527320, 166837814005649836104, 0, 61938899699519471750, 2866779745500839762, 0, 9234707547525910912, 1008000642957901120, 6510063641108515260, 1346544783401016320, 44107638181404732264, 30627973324307103327, 0, 202955938380284559360, 39264019875850347776, 5299601709161396736] }

theorem case_52_34_18_checked :
    (Witness.linear .conditional case_52_34_18).check 52 34 18 = true := by
  change case_52_34_18.check 52 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_19 : Certificate := {
  objectiveScale := 131054811507452833000000
  eta := 17772447374416951313753220364800
  rows := #[⟨.count 2, 2467787938403535162730931616000⟩, ⟨.count 3, 332713949893327432759624495200⟩, ⟨.count 4, 43632823667193967352864477760⟩, ⟨.count 5, 5259476298348956561211734400⟩, ⟨.count 6, 570811403286158651921304000⟩, ⟨.count 7, 70099646017598430937704000⟩, ⟨.count 8, 15294468222021475840953600⟩, ⟨.count 9, 4588340466606442752286080⟩, ⟨.count 10, 2549078037003579306825600⟩, ⟨.path 6, 17492598332032935913401600⟩, ⟨.path 7, 25125712323905778789204000⟩, ⟨.privateRow 2 32, 221627040849239199252644966400⟩, ⟨.privateRow 3 28, 1526419792033205833668504600⟩, ⟨.privateRow 3 29, 38213653699060157985173707200⟩, ⟨.privateRow 3 30, 68688890641494262515082707000⟩, ⟨.privateRow 4 26, 5989033357159539545593678944⟩, ⟨.privateRow 4 27, 14781211359270805147524265440⟩, ⟨.privateRow 4 28, 25294522603503492491457985680⟩, ⟨.privateRow 4 29, 44193270337104666808211421240⟩, ⟨.privateRow 5 23, 659852259778716332361359040⟩, ⟨.privateRow 5 24, 2652737509225014146756380560⟩, ⟨.privateRow 5 25, 5226148923785161192903065984⟩, ⟨.privateRow 5 26, 9019871666611570676820668760⟩, ⟨.privateRow 5 27, 16684516891000056259527125760⟩, ⟨.privateRow 5 28, 20910323837643797100540316320⟩, ⟨.privateRow 6 20, 44730250315991379741201600⟩, ⟨.privateRow 6 21, 373530970922345924853765600⟩, ⟨.privateRow 6 22, 997417820478971960199331200⟩, ⟨.privateRow 6 23, 1941259482930207976753417200⟩, ⟨.privateRow 6 24, 3301092473320163824900678080⟩, ⟨.privateRow 6 25, 6184290914023987289368443600⟩, ⟨.privateRow 6 26, 8541141155487100249538248800⟩, ⟨.privateRow 6 27, 8865602374197127272735621600⟩, ⟨.privateRow 7 18, 31244413653558157789376640⟩, ⟨.privateRow 7 19, 160227762325939270714752000⟩, ⟨.privateRow 7 20, 388677501579719871538519500⟩, ⟨.privateRow 7 21, 754787208956835350259849600⟩, ⟨.privateRow 7 22, 1289082419087908288922278200⟩, ⟨.privateRow 7 23, 2419739638176044123925345360⟩, ⟨.privateRow 7 24, 3484953830589179138045856000⟩, ⟨.privateRow 7 25, 4039241745885475302674701200⟩, ⟨.privateRow 7 26, 2864071251576164464026192000⟩, ⟨.privateRow 8 16, 14541331529270418318482400⟩, ⟨.privateRow 8 17, 67136342799581769993519240⟩, ⟨.privateRow 8 18, 162326705550852932247158000⟩, ⟨.privateRow 8 19, 315846700522474748486359500⟩, ⟨.privateRow 8 20, 543181218135066283363390800⟩, ⟨.privateRow 8 21, 1028659199515819399441914000⟩, ⟨.privateRow 8 22, 1538750957037210648565273440⟩, ⟨.privateRow 8 23, 1900815628718106544358514600⟩, ⟨.privateRow 8 24, 460745855188396959708727200⟩, ⟨.privateRow 9 14, 5947848753008351715926400⟩, ⟨.privateRow 9 15, 29407091172341292185106240⟩, ⟨.privateRow 9 16, 73821299951623656725669376⟩, ⟨.privateRow 9 17, 145977202252404974970879360⟩, ⟨.privateRow 9 18, 253219039500843059391788040⟩, ⟨.privateRow 9 19, 420415799102947472818593600⟩, ⟨.privateRow 9 20, 882023485437188499816771360⟩, ⟨.privateRow 9 21, 552487173740155778961380544⟩, ⟨.privateRow 10 12, 2372603403672562277891520⟩, ⟨.privateRow 10 13, 13743779082844298429301360⟩, ⟨.privateRow 10 14, 37147019030152160262194880⟩, ⟨.privateRow 10 15, 76089979404556842308744160⟩, ⟨.privateRow 10 16, 134364735639388669239784960⟩, ⟨.privateRow 10 17, 258954465084101112832145640⟩, ⟨.privateRow 10 18, 371327839190364259881437760⟩, ⟨.privateRow 11 10, 1001423514537120441967200⟩, ⟨.privateRow 11 11, 6936433504538585998381200⟩, ⟨.privateRow 11 12, 20950235116623167427972900⟩, ⟨.privateRow 11 13, 45535803115563939435566400⟩, ⟨.privateRow 11 14, 83131807481779230143849880⟩, ⟨.privateRow 11 15, 162609936443853329947916400⟩, ⟨.privateRow 11 16, 7846380832651642553822550⟩, ⟨.privateRow 12 8, 467330973450656206251360⟩, ⟨.privateRow 12 9, 3862633556071750276159200⟩, ⟨.privateRow 12 10, 13326636001147833573871200⟩, ⟨.privateRow 12 11, 31628292667464053958797400⟩, ⟨.privateRow 12 12, 60995795885442790556184000⟩, ⟨.privateRow 12 13, 5257473451319882320327800⟩, ⟨.privateRow 13 6, 250355878634280110491800⟩, ⟨.privateRow 13 7, 2470178002524897090185760⟩, ⟨.privateRow 13 8, 9728114141217741436252800⟩, ⟨.privateRow 13 9, 25651848487758546705775200⟩, ⟨.privateRow 13 10, 500711757268560220983600⟩, ⟨.privateRow 14 4, 153158890458618420536160⟩, ⟨.privateRow 14 5, 1952775853347384861836040⟩, ⟨.privateRow 14 6, 8331843640948842077167104⟩, ⟨.privateRow 14 7, 1859786526997509392224800⟩, ⟨.privateRow 15 3, 1608168349815493415629680⟩, ⟨.privateRow 15 4, 1708678871678961754106535⟩, ⟨.hall 5 28, 4481957268924204703579545600⟩, ⟨.hall 4 29, 14566145645288813161407389568⟩, ⟨.hall 3 30, 34596888844369377865083544800⟩, ⟨.hall 2 31, 72607460853878014804500360600⟩, ⟨.assumptionRow 19, 82117735153848337900880⟩]
  caps := #[0, 5704349793245485437590488800, 89141051146921922095701600, 22199804251642205046658800, 5500647141371155189992576, 19095259623179120042152656, 0, 148576958548513081838680, 1613884332496831365042800, 980830925683748302449440, 4301484303060023477560680, 443769334569485532306160, 1662595886230875260285280, 12451670315035061403672720, 0, 3490645408557973543312050, 239642938615722709223716560, 61521806976746388941795280, 12397934369467369563486800] }

theorem case_52_34_19_checked :
    (Witness.linear .conditional case_52_34_19).check 52 34 19 = true := by
  change case_52_34_19.check 52 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_20 : Certificate := {
  objectiveScale := 77450855873022487856000000
  eta := 16273152500429961184059725803689600
  rows := #[⟨.count 2, 2282416810437431798221629996057600⟩, ⟨.count 3, 310478907959973969051565226296800⟩, ⟨.count 4, 39946499077294771708005683424000⟩, ⟨.count 5, 4715488988823518164027738569600⟩, ⟨.count 6, 464386715704814870636734665600⟩, ⟨.count 7, 30323759421023359090085286000⟩, ⟨.path 7, 26185580831419298493770966400⟩, ⟨.path 8, 389795840571963013053465600⟩, ⟨.privateRow 2 32, 205198858418103669405334458009600⟩, ⟨.privateRow 3 28, 1596545933516879856092990307900⟩, ⟨.privateRow 3 29, 35154671227452613786014650785200⟩, ⟨.privateRow 3 30, 63349365806459899475097170982600⟩, ⟨.privateRow 4 25, 192724337653615126661430928800⟩, ⟨.privateRow 4 26, 5544153582464542789158473009952⟩, ⟨.privateRow 4 27, 13501653882210650634860473591500⟩, ⟨.privateRow 4 28, 23161961307098108858764698897600⟩, ⟨.privateRow 4 29, 40853179483983370144799233475400⟩, ⟨.privateRow 5 23, 752804861773508882510160811680⟩, ⟨.privateRow 5 24, 2428076363087948498366936935440⟩, ⟨.privateRow 5 25, 4724499477337193676443078197440⟩, ⟨.privateRow 5 26, 8171762207860883468011764148560⟩, ⟨.privateRow 5 27, 15313825811686737545003883048960⟩, ⟨.privateRow 5 28, 19574535421917244429624063180080⟩, ⟨.privateRow 6 20, 76948545070491021267750810400⟩, ⟨.privateRow 6 21, 382512565268051801093504393400⟩, ⟨.privateRow 6 22, 912023164300873981014184125600⟩, ⟨.privateRow 6 23, 1732593720824058466359857071200⟩, ⟨.privateRow 6 24, 2951281545479256297270471949440⟩, ⟨.privateRow 6 25, 5614660655084053673808505597800⟩, ⟨.privateRow 6 26, 7957147003882377192597681175200⟩, ⟨.privateRow 6 27, 8561408076535595049767412414000⟩, ⟨.privateRow 7 17, 6589838627425855525204681200⟩, ⟨.privateRow 7 18, 47507223092936595907800281400⟩, ⟨.privateRow 7 19, 160764057882885745017277548000⟩, ⟨.privateRow 7 20, 354824084939569757733866995350⟩, ⟨.privateRow 7 21, 666751395922664634360365043600⟩, ⟨.privateRow 7 22, 1135600723841593827003781194600⟩, ⟨.privateRow 7 23, 2167195766164223726512552411440⟩, ⟨.privateRow 7 24, 3214101900346897325269825421100⟩, ⟨.privateRow 7 25, 3890393934862911145738465597200⟩, ⟨.privateRow 7 26, 3059089730163713630111698971000⟩, ⟨.privateRow 8 13, 13127168580529592679690600⟩, ⟨.privateRow 8 14, 353423769475796725991670000⟩, ⟨.privateRow 8 15, 4609824033195975296018015700⟩, ⟨.privateRow 8 16, 23507178790842901509504130800⟩, ⟨.privateRow 8 17, 68678720579614722981605281080⟩, ⟨.privateRow 8 18, 148555791102993223825165290000⟩, ⟨.privateRow 8 19, 277324563432268174951143615600⟩, ⟨.privateRow 8 20, 472473051550421099727424075200⟩, ⟨.privateRow 8 21, 907078597468874501104833999600⟩, ⟨.privateRow 8 22, 1399009613433928598408274128160⟩, ⟨.privateRow 8 23, 1807663622213247030364114382400⟩, ⟨.privateRow 8 24, 876816098167893613447253936400⟩, ⟨.privateRow 9 11, 19603238413590858401671296⟩, ⟨.privateRow 9 12, 273045106475015527737564480⟩, ⟨.privateRow 9 13, 2680365867704442369920825280⟩, ⟨.privateRow 9 14, 11712934952120537894998599360⟩, ⟨.privateRow 9 15, 32064660650593956344733708480⟩, ⟨.privateRow 9 16, 68822069260514106133667502432⟩, ⟨.privateRow 9 17, 128417547641031448246281714880⟩, ⟨.privateRow 9 18, 218625116407572048324639128640⟩, ⟨.privateRow 9 19, 420615484789896996805574328960⟩, ⟨.privateRow 9 20, 674326897379508540444490493280⟩, ⟨.privateRow 9 21, 816984564124812614748052932096⟩, ⟨.privateRow 10 9, 9189018006370714875783420⟩, ⟨.privateRow 10 10, 186230764929113154815877312⟩, ⟨.privateRow 10 11, 1606765434256822143994129440⟩, ⟨.privateRow 10 12, 6412520873368855796392860480⟩, ⟨.privateRow 10 13, 17054817419824046809454027520⟩, ⟨.privateRow 10 14, 36462023449278996627108610560⟩, ⟨.privateRow 10 15, 68189864821675800950213603136⟩, ⟨.privateRow 10 16, 116279875856616441752580237440⟩, ⟨.privateRow 10 17, 223035845050629991465015170240⟩, ⟨.privateRow 10 18, 368988956196390214714887137280⟩, ⟨.privateRow 10 19, 96227396562714126179203974240⟩, ⟨.privateRow 11 7, 10810609419259664559745200⟩, ⟨.privateRow 11 8, 137835270095560723136751300⟩, ⟨.privateRow 11 9, 1078178112747497212091921280⟩, ⟨.privateRow 11 10, 4069422259964173730704086000⟩, ⟨.privateRow 11 11, 10687534788948092993988100800⟩, ⟨.privateRow 11 12, 22865339805852462182574410100⟩, ⟨.privateRow 11 13, 42904360437018174183657859200⟩, ⟨.privateRow 11 14, 73438631906914753287261092640⟩, ⟨.privateRow 11 15, 140224414777217109004454989200⟩, ⟨.privateRow 11 16, 59384028866170744884750351750⟩, ⟨.privateRow 12 5, 16044317153980613275177400⟩, ⟨.privateRow 12 6, 118916703611856310157197200⟩, ⟨.privateRow 12 7, 848343269516724926925005025⟩, ⟨.privateRow 12 8, 3099762074149054484764273680⟩, ⟨.privateRow 12 9, 8127592661145036381968437200⟩, ⟨.privateRow 12 10, 17483368984868412896627926800⟩, ⟨.privateRow 12 11, 33019204702892102120315089200⟩, ⟨.privateRow 12 12, 56893148628015254673779060400⟩, ⟨.privateRow 12 13, 8866089659289686895863031240⟩, ⟨.privateRow 13 4, 128354537231844906201419200⟩, ⟨.privateRow 13 5, 815428824767014698220780800⟩, ⟨.privateRow 13 6, 2924076801312966769401081150⟩, ⟨.privateRow 13 7, 7701272233910694372085152000⟩, ⟨.privateRow 13 8, 16750267108755760259285205600⟩, ⟨.privateRow 13 9, 16750267108755760259285205600⟩, ⟨.privateRow 14 2, 158078745853956358163853120⟩, ⟨.privateRow 14 3, 1001165390408390268371069760⟩, ⟨.privateRow 14 4, 3445186784640637099982798880⟩, ⟨.privateRow 14 5, 9292066279727872178318991210⟩, ⟨.privateRow 14 6, 1101281929449229295208176736⟩, ⟨.privateRow 15 1, 2213102441955389014293943680⟩, ⟨.privateRow 15 2, 2628059149822024454474058120⟩, ⟨.privateRow 16 0, 1383189026222118133933714800⟩, ⟨.hall 6 27, 214122872646409841738153244000⟩, ⟨.hall 5 28, 4552368076075944232370728065600⟩, ⟨.hall 4 29, 13962352651174451521729775979936⟩, ⟨.hall 3 30, 32459921544366288495921681082800⟩, ⟨.hall 2 31, 67501699263178698113166182812200⟩, ⟨.assumptionRow 20, 5232274487676515248589620⟩]
  caps := #[0, 619739862499254319110007519800, 239236871227071437847442114800, 0, 0, 271730133044725233792033120, 6870696750132533535783566000, 914503775810554268507808640, 2910991228093367096620487580, 0, 22161749309482312347477660, 57258332317863650942363395, 5958864818010953136332867075, 199535671849969422682314600, 5711439851863135452243479298, 0, 15116461620069622186169315520, 128820097662842205059967246720, 33534220037411537070786679520] }

theorem case_52_34_20_checked :
    (Witness.linear .conditional case_52_34_20).check 52 34 20 = true := by
  change case_52_34_20.check 52 34 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_21 : Certificate := {
  objectiveScale := 81528820107380932000000
  eta := 20201596387935586221351289536000
  rows := #[⟨.count 2, 2592453148881232212310544409600⟩, ⟨.count 3, 313440052220788744173302780400⟩, ⟨.count 4, 34556321500835322515050563840⟩, ⟨.count 5, 3241607916556658870647826400⟩, ⟨.count 6, 222316020227240738116718400⟩, ⟨.count 7, 7009964601759843093770400⟩, ⟨.path 6, 105679994946884654917420800⟩, ⟨.path 7, 7513387281367122232677600⟩, ⟨.privateRow 2 32, 270472474194301785930037113600⟩, ⟨.privateRow 4 26, 4899124060877919141374257152⟩, ⟨.privateRow 4 29, 123790366895397421161510247680⟩, ⟨.privateRow 5 23, 530411117499689678662512960⟩, ⟨.privateRow 5 24, 2107696071046277394208365840⟩, ⟨.privateRow 5 27, 39288114368590852411375048320⟩, ⟨.privateRow 6 20, 47178174462637674154899200⟩, ⟨.privateRow 6 21, 267630434260045438115734200⟩, ⟨.privateRow 6 23, 2763261284446094339534827200⟩, ⟨.privateRow 6 24, 1263195621237123725497426080⟩, ⟨.privateRow 6 26, 22550388508185057152364732000⟩, ⟨.privateRow 6 27, 2754415376734349775630783600⟩, ⟨.privateRow 7 16, 83451959544760036830600⟩, ⟨.privateRow 7 17, 3004270543611361325901600⟩, ⟨.privateRow 7 18, 27288790771136532043606200⟩, ⟨.privateRow 7 19, 108265008849402021114898400⟩, ⟨.privateRow 7 20, 149963171301933786184588200⟩, ⟨.privateRow 7 21, 493630262415762012143974800⟩, ⟨.privateRow 7 22, 1513735094182402308070253400⟩, ⟨.privateRow 7 23, 1736468374207366846371124800⟩, ⟨.privateRow 7 24, 2256457534130766635862593400⟩, ⟨.privateRow 8 14, 122551828702095158982000⟩, ⟨.privateRow 8 15, 1938361423971471764565300⟩, ⟨.privateRow 8 16, 12774356980892937208069200⟩, ⟨.privateRow 8 17, 43812278760999019336065000⟩, ⟨.privateRow 8 18, 85004671761744359940114800⟩, ⟨.privateRow 8 19, 173496623893556116570817400⟩, ⟨.privateRow 8 20, 396654750258021251422826400⟩, ⟨.privateRow 8 21, 1183993642395725013451599000⟩, ⟨.privateRow 8 22, 1454121566208691815578663520⟩, ⟨.privateRow 8 23, 2054317921758915835741418700⟩, ⟨.privateRow 8 24, 1813669023328046676806414400⟩, ⟨.privateRow 9 12, 91038501321556403815200⟩, ⟨.privateRow 9 13, 1058847799986102173604480⟩, ⟨.privateRow 9 14, 6032818020908471026153920⟩, ⟨.privateRow 9 15, 19210779024326974957803840⟩, ⟨.privateRow 9 16, 41957824489078915390349376⟩, ⟨.privateRow 9 17, 80635835237213225405916480⟩, ⟨.privateRow 9 18, 154537855993341995476302000⟩, ⟨.privateRow 9 19, 385784753200227416807291520⟩, ⟨.privateRow 9 20, 915883738695386044942438080⟩, ⟨.privateRow 9 21, 1188737051776249173945050304⟩, ⟨.privateRow 9 22, 1597507205790143151587603520⟩, ⟨.privateRow 9 23, 1664462988895437168046889280⟩, ⟨.privateRow 10 10, 50981560740071586136512⟩, ⟨.privateRow 10 11, 619061808986583545943360⟩, ⟨.privateRow 10 12, 3117718522181300844502080⟩, ⟨.privateRow 10 13, 9580284955738452228152880⟩, ⟨.privateRow 10 14, 21875724244830716960394240⟩, ⟨.privateRow 10 16, 162942732743128797246307520⟩, ⟨.privateRow 10 17, 127645082702954233789291920⟩, ⟨.privateRow 10 18, 364117589885696992699273920⟩, ⟨.privateRow 10 19, 761579548188769377569261760⟩, ⟨.privateRow 10 20, 1016062505549626711700684160⟩, ⟨.privateRow 10 22, 2684094203696868890777129280⟩, ⟨.privateRow 11 8, 39829344328180926669150⟩, ⟨.privateRow 11 9, 403604022525566723580720⟩, ⟨.privateRow 11 10, 1889048902422295379165400⟩, ⟨.privateRow 11 11, 5637384120296377313172000⟩, ⟨.privateRow 11 12, 13090577835862131231927300⟩, ⟨.privateRow 11 13, 20711259050654081867958000⟩, ⟨.privateRow 11 14, 4365296138368629562938840⟩, ⟨.privateRow 11 15, 193517507642521729043176800⟩, ⟨.privateRow 11 16, 148045672867848504429230550⟩, ⟨.privateRow 11 17, 369525276864197443085896800⟩, ⟨.privateRow 11 18, 711776936040811946862156600⟩, ⟨.privateRow 11 19, 970179100883562284177823360⟩, ⟨.privateRow 11 21, 1848187788412470146586344400⟩, ⟨.privateRow 12 6, 29453632780503542410800⟩, ⟨.privateRow 12 7, 312944848292850138114750⟩, ⟨.privateRow 12 8, 1368612136534064604021840⟩, ⟨.privateRow 12 9, 4041459183667664640796200⟩, ⟨.privateRow 12 10, 9475007099081985720151200⟩, ⟨.privateRow 12 11, 18317705120074828084316700⟩, ⟨.privateRow 12 12, 27903300655057037769358800⟩, ⟨.privateRow 12 13, 9463452212375788176590040⟩, ⟨.privateRow 12 15, 719460206225262467525810250⟩, ⟨.privateRow 12 16, 173031677261806739222761200⟩, ⟨.privateRow 12 17, 785116035397102426502284800⟩, ⟨.privateRow 13 4, 55634639696506691220400⟩, ⟨.privateRow 13 5, 294536327805035424108000⟩, ⟨.privateRow 13 6, 1251779393171400552459000⟩, ⟨.privateRow 13 7, 3605124652333633591081920⟩, ⟨.privateRow 13 8, 8583630124603889502576000⟩, ⟨.privateRow 13 9, 17332330059296315341740000⟩, ⟨.privateRow 13 10, 30960676991105973664152600⟩, ⟨.privateRow 13 11, 52165061257251819386109600⟩, ⟨.privateRow 13 12, 18025623261668167955409600⟩, ⟨.privateRow 13 13, 5563463969650669122040000⟩, ⟨.privateRow 13 14, 965121912135149825945889000⟩, ⟨.privateRow 13 15, 567377951236317096120273600⟩, ⟨.privateRow 13 16, 900446643487960797402174000⟩, ⟨.privateRow 14 3, 289300126421834794346080⟩, ⟨.privateRow 14 4, 1378430014127565784825440⟩, ⟨.privateRow 14 5, 4068283027807051795491750⟩, ⟨.privateRow 14 6, 9894064323626749966635936⟩, ⟨.privateRow 14 7, 20643630449672354253695280⟩, ⟨.privateRow 14 8, 38254378255318000883147040⟩, ⟨.privateRow 14 9, 74639432616833376941288640⟩, ⟨.privateRow 14 10, 115509650476790765160725760⟩, ⟨.privateRow 14 11, 47908100935455841943710848⟩, ⟨.privateRow 14 12, 19383108470262931221187360⟩, ⟨.privateRow 14 13, 1549527639631149887866897740⟩, ⟨.privateRow 14 14, 1565940255731902908253281600⟩, ⟨.privateRow 14 15, 1637294065484374018601639760⟩, ⟨.privateRow 15 1, 959258313925031160200160⟩, ⟨.privateRow 15 2, 2025100884952843560422560⟩, ⟨.privateRow 15 3, 6432673399261973662518720⟩, ⟨.privateRow 15 4, 15378109845110655786958815⟩, ⟨.privateRow 15 5, 32199104070750212610718704⟩, ⟨.privateRow 15 7, 248152746902298445519472160⟩, ⟨.privateRow 15 8, 161754933185608379388751980⟩, ⟨.privateRow 15 9, 337179297344648452810356240⟩, ⟨.privateRow 15 10, 178613898052840802029269792⟩, ⟨.privateRow 15 11, 81004035398113742416902400⟩, ⟨.privateRow 15 12, 3118908500437998188495795220⟩, ⟨.privateRow 15 13, 4674945392913639359235479760⟩, ⟨.privateRow 15 19, 47633410465418309806479245040⟩, ⟨.privateRow 16 1, 25313761061910544505282000⟩, ⟨.privateRow 16 2, 26802805830258223593828000⟩, ⟨.privateRow 16 3, 71194952986623406421105625⟩, ⟨.privateRow 16 4, 127581355752029144306621280⟩, ⟨.privateRow 16 5, 22782384955719490054753800⟩, ⟨.privateRow 16 6, 1065514619467496150253100800⟩, ⟨.privateRow 16 7, 732833382742310263427913900⟩, ⟨.privateRow 16 8, 1346231838292515321417270000⟩, ⟨.privateRow 16 9, 934077783184499092244905800⟩, ⟨.privateRow 16 10, 480961460176300345600358000⟩, ⟨.privateRow 16 14, 51497302953908335319765489520⟩, ⟨.privateRow 17 0, 263263115043869662854932800⟩, ⟨.privateRow 17 2, 341735774335792350821307000⟩, ⟨.privateRow 17 3, 801939950441326049927333760⟩, ⟨.privateRow 17 8, 39513768467199883550964990720⟩, ⟨.privateRow 17 13, 121894872467081559588954731520⟩, ⟨.privateRow 17 14, 257167561380161603738060894400⟩, ⟨.privateRow 18 6, 189284338715737785007641753600⟩, ⟨.privateRow 18 10, 1108343500337219717315154009600⟩, ⟨.privateRow 18 16, 18788724002521686326115677875200⟩, ⟨.hall 16 2, 164390542425583771375478400⟩, ⟨.hall 13 14, 40394537775928016176496⟩, ⟨.hall 12 17, 49238367381433263015840⟩, ⟨.hall 15 17, 94726758500096827069765800⟩, ⟨.hall 16 17, 1458072637166047363504243200⟩, ⟨.hall 7 20, 6461669919144285815200⟩, ⟨.hall 10 21, 396299352261426031891200⟩, ⟨.hall 8 22, 140923946326652728902432⟩, ⟨.hall 5 23, 281434539430259710414920⟩, ⟨.hall 3 28, 113491248927357246119254080⟩, ⟨.hall 4 29, 56361797789653560836256520896⟩, ⟨.hall 2 30, 7521861613606096151948553000⟩]
  caps := #[0, 0, 49175489173722574260998400, 0, 846111235293818553126496, 0, 9964376868748657185344800, 503422679607279138907200, 2520282818392905381682248, 0, 474476435651050278354944, 569881388117944760302500, 5310920097701018153062380, 0, 88380374920429566990749162, 0, 120925694279666760198690690, 1012989291658737675734474880, 0] }

theorem case_52_34_21_checked :
    (Witness.linear .conditional case_52_34_21).check 52 34 21 = true := by
  change case_52_34_21.check 52 34 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_34_22 : Certificate := {
  objectiveScale := 16284537583105033968000000
  eta := 3701214413066011380160473876024000
  rows := #[⟨.count 2, 422000850420986800623011207856000⟩, ⟨.count 3, 43656403435623137025071147943000⟩, ⟨.count 4, 3889408759640431342147568736000⟩, ⟨.count 5, 268343948514153136430635830000⟩, ⟨.count 6, 11656569709212081944498208000⟩, ⟨.path 5, 82502560740457297475229694500⟩, ⟨.path 6, 7763958545496600707035776000⟩, ⟨.path 7, 244393598779899570311310000⟩, ⟨.privateRow 2 32, 49324774724530924748144167152000⟩, ⟨.privateRow 3 27, 4419782681409581070622237200⟩, ⟨.privateRow 3 31, 81821226889594869569894166165000⟩, ⟨.privateRow 4 26, 628935075564583386349544353560⟩, ⟨.privateRow 5 23, 55202183694340073780016513600⟩, ⟨.privateRow 5 24, 256663094284713529315419917400⟩, ⟨.privateRow 5 25, 496152175864521257899279141680⟩, ⟨.privateRow 5 28, 11233193383565408118205746003600⟩, ⟨.privateRow 6 19, 48569040455050341435409200⟩, ⟨.privateRow 6 20, 3615695233875969862413796000⟩, ⟨.privateRow 6 21, 26075503594305152058135314250⟩, ⟨.privateRow 6 23, 370096088267483601737818104000⟩, ⟨.privateRow 6 24, 333329324643010493271213339600⟩, ⟨.privateRow 6 27, 8514638482174875357041586852000⟩, ⟨.privateRow 7 17, 165576274278580709438895000⟩, ⟨.privateRow 7 18, 1942761618202013657416368000⟩, ⟨.privateRow 7 19, 9862213492400499885912257000⟩, ⟨.privateRow 7 20, 14859090814216963832895502125⟩, ⟨.privateRow 7 21, 62393870898862885051131033000⟩, ⟨.privateRow 7 22, 207531462444392188091717227500⟩, ⟨.privateRow 7 23, 341513207959686475803079789800⟩, ⟨.privateRow 7 24, 446258414831059418401219155750⟩, ⟨.privateRow 8 15, 90147082662782830694509500⟩, ⟨.privateRow 8 16, 856982655963078338550402000⟩, ⟨.privateRow 8 17, 3693454758240873691883617800⟩, ⟨.privateRow 8 18, 7907186964992665435204119000⟩, ⟨.privateRow 8 19, 19230304455171494562082330125⟩, ⟨.privateRow 8 20, 51317606608074781212094857000⟩, ⟨.privateRow 8 21, 170571158552651227506968332500⟩, ⟨.privateRow 8 23, 1023407634083908197292375457250⟩, ⟨.privateRow 8 25, 1186271217068891492774963227500⟩, ⟨.privateRow 9 13, 47550109536412921685016000⟩, ⟨.privateRow 9 14, 381193378116910255508211600⟩, ⟨.privateRow 9 15, 1489182975935841047317092000⟩, ⟨.privateRow 9 16, 3628548858723670053783570960⟩, ⟨.privateRow 9 17, 7932943274324889101116836000⟩, ⟨.privateRow 9 18, 17740945868035661080679469600⟩, ⟨.privateRow 9 19, 52198472387236830586309778400⟩, ⟨.privateRow 9 20, 140217348004625637228831348000⟩, ⟨.privateRow 9 21, 95961827057625645510964489920⟩, ⟨.privateRow 10 11, 26492203884572913510223200⟩, ⟨.privateRow 10 12, 185445427192010394571562400⟩, ⟨.privateRow 10 13, 685117828237149513278272200⟩, ⟨.privateRow 10 14, 1747682662324704021568360800⟩, ⟨.privateRow 10 15, 3783086714717012049259872960⟩, ⟨.privateRow 10 16, 7740629497977619062301882400⟩, ⟨.privateRow 10 18, 90938905201110621109426171200⟩, ⟨.privateRow 10 19, 100140530683685613068643696000⟩, ⟨.privateRow 10 20, 121763467494274025075687871840⟩, ⟨.privateRow 10 21, 87236619708241556446372479000⟩, ⟨.privateRow 10 22, 58023813663633474568168857600⟩, ⟨.privateRow 11 9, 15453785599334199547630200⟩, ⟨.privateRow 11 10, 104864973709767782644633500⟩, ⟨.privateRow 11 11, 374457112599251758269501000⟩, ⟨.privateRow 11 12, 972300677291443388205066750⟩, ⟨.privateRow 11 13, 2114358847908906392653041000⟩, ⟨.privateRow 11 14, 4203429683018902276955414400⟩, ⟨.privateRow 11 15, 10019204330235006040046913000⟩, ⟨.privateRow 11 16, 3409491447853107775195912875⟩, ⟨.privateRow 11 17, 87247658126526795160335072000⟩, ⟨.privateRow 11 18, 112864147493804104029525894000⟩, ⟨.privateRow 11 19, 138883171181216451334552607400⟩, ⟨.privateRow 11 20, 138098891562050240707510374750⟩, ⟨.privateRow 12 7, 15177825142203231698565375⟩, ⟨.privateRow 12 8, 72853560682575512153113800⟩, ⟨.privateRow 12 9, 251518245213653553861940500⟩, ⟨.privateRow 12 10, 653814006125677673168970000⟩, ⟨.privateRow 12 11, 1436834113461905934130855500⟩, ⟨.privateRow 12 12, 2825835081021110774423808000⟩, ⟨.privateRow 12 13, 6362544299611594728038605200⟩, ⟨.privateRow 12 14, 13882650730068555926954463000⟩, ⟨.privateRow 12 17, 350749420486221882399380106000⟩, ⟨.privateRow 12 18, 66393878302053816742204376400⟩, ⟨.privateRow 12 19, 187537207457063130867473773500⟩, ⟨.privateRow 13 5, 14285011898544218069238000⟩, ⟨.privateRow 13 6, 60711300568812926794261500⟩, ⟨.privateRow 13 7, 210465841971884812886773200⟩, ⟨.privateRow 13 8, 555074748057718187833248000⟩, ⟨.privateRow 13 9, 1232906411551277897975772000⟩, ⟨.privateRow 13 10, 2408214922562912762839039500⟩, ⟨.privateRow 13 11, 5276363940344105274119454000⟩, ⟨.privateRow 13 12, 10903749582158801652249365400⟩, ⟨.privateRow 13 13, 22638569412104020257949066000⟩, ⟨.privateRow 13 15, 15091094712819213231716430000⟩, ⟨.privateRow 13 16, 77953309930355798003831766000⟩, ⟨.privateRow 13 17, 83781594784961838976080870000⟩, ⟨.privateRow 13 21, 4451595402907639044262430226000⟩, ⟨.privateRow 14 4, 74282061872429933960037600⟩, ⟨.privateRow 14 5, 236774072218370414497619850⟩, ⟨.privateRow 14 6, 589304357521277476082964960⟩, ⟨.privateRow 14 7, 1352994698390688082843542000⟩, ⟨.privateRow 14 8, 2719866265482819120382915200⟩, ⟨.privateRow 14 9, 5787810654226832354386263000⟩, ⟨.privateRow 14 10, 11652154341897986458913170800⟩, ⟨.privateRow 14 11, 23109149448512952454967697360⟩, ⟨.privateRow 14 12, 45671087707899004396429784400⟩, ⟨.privateRow 14 14, 51594197831964905559100401600⟩, ⟨.privateRow 14 15, 95446259334249762644151646200⟩, ⟨.privateRow 14 16, 176538748246016981049425360160⟩, ⟨.privateRow 15 2, 122771741150266140850617700⟩, ⟨.privateRow 15 3, 259987216553504768860131600⟩, ⟨.privateRow 15 4, 828709252764296450741669475⟩, ⟨.privateRow 15 5, 2062565251324471166290377360⟩, ⟨.privateRow 15 6, 4104083918451753851292077400⟩, ⟨.privateRow 15 7, 8839565362819162141244474400⟩, ⟨.privateRow 15 8, 17494973113912925071213022250⟩, ⟨.privateRow 15 10, 131046556503794078743949332980⟩, ⟨.privateRow 15 13, 443556761955747243158874519000⟩, ⟨.privateRow 15 14, 736630446901596845103706200⟩, ⟨.privateRow 15 16, 1104945670352395267655559300⟩, ⟨.privateRow 16 1, 1227717411502661408506177000⟩, ⟨.privateRow 16 2, 1299936082767523844300658000⟩, ⟨.privateRow 16 3, 4143546263821482253708347375⟩, ⟨.privateRow 16 4, 8839565362819162141244474400⟩, ⟨.privateRow 16 5, 18941925777469633159809588000⟩, ⟨.privateRow 16 8, 271213937268315202060910010000⟩, ⟨.privateRow 16 9, 288390819961975164858100977300⟩, ⟨.privateRow 16 11, 350820250336885497480640077750⟩, ⟨.privateRow 16 12, 860279129060079172674685455000⟩, ⟨.privateRow 16 13, 1034965777896743567370707211000⟩, ⟨.privateRow 17 0, 9821739292021291268049416000⟩, ⟨.privateRow 17 1, 10399488662140190754405264000⟩, ⟨.privateRow 17 2, 27623641758809881691388982500⟩, ⟨.privateRow 17 8, 185630872619202404966133962400⟩, ⟨.privateRow 17 14, 38054328886936493018057462292000⟩, ⟨.privateRow 18 5, 2629770695438700737020231134000⟩, ⟨.privateRow 18 8, 1168786975750533660897880504000⟩, ⟨.privateRow 18 14, 659696763027194070601075124472000⟩, ⟨.hall 9 14, 164488132986676484797812⟩, ⟨.hall 10 16, 942707585906349621813000⟩, ⟨.hall 11 16, 2094560547775587622731000⟩, ⟨.hall 13 16, 55913231200550852546360800⟩, ⟨.hall 14 16, 848379338227226087859376800⟩, ⟨.hall 15 17, 35086871286628691832571269000⟩, ⟨.hall 7 23, 181687647702257762288399330⟩, ⟨.hall 5 24, 231557619036491786556643840⟩, ⟨.hall 8 25, 2437846565822354081869085304000⟩, ⟨.hall 4 26, 2451322272070240010323761880⟩, ⟨.hall 3 30, 29570484743153360062980809886000⟩]
  caps := #[0, 280945392234244560555191316000, 1800389948301268084367521200, 39601952945578780893240003900, 3067937441952765866006402880, 1033653726382965713518604100, 98332191536651208402659250, 244393598779899570311310000, 760093457139134733465536725, 679287279091613166928800, 0, 872724360345973496055137550, 2048720193449413208334338025, 0, 11469139799993507083675255890, 3010951159327682510634329635, 0, 1096115333405093985287838934400, 0] }

theorem case_52_34_22_checked :
    (Witness.linear .conditional case_52_34_22).check 52 34 22 = true := by
  change case_52_34_22.check 52 34 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_35_1_checked :
    (Witness.rising).check 52 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_35_2_checked :
    (Witness.rising).check 52 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_35_3_checked :
    (Witness.rising).check 52 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_35_4_checked :
    (Witness.rising).check 52 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_35_5_checked :
    (Witness.rising).check 52 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_35_6_checked :
    (Witness.rising).check 52 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_35_7_checked :
    (Witness.rising).check 52 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_35_8_checked :
    (Witness.rising).check 52 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_35_9_checked :
    (Witness.rising).check 52 35 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_35_10_checked :
    (Witness.linear .positive case_52_35_10).check 52 35 10 = true := by
  change case_52_35_10.check 52 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_35_11_checked :
    (Witness.linear .positive case_52_35_11).check 52 35 11 = true := by
  change case_52_35_11.check 52 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_52_35_12_checked :
    (Witness.linear .positive case_52_35_12).check 52 35 12 = true := by
  change case_52_35_12.check 52 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_52_35_13_checked :
    (Witness.linear .positive case_52_35_13).check 52 35 13 = true := by
  change case_52_35_13.check 52 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_52_35_14_checked :
    (Witness.linear .positive case_52_35_14).check 52 35 14 = true := by
  change case_52_35_14.check 52 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_52_35_15_checked :
    (Witness.linear .positive case_52_35_15).check 52 35 15 = true := by
  change case_52_35_15.check 52 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_52_35_16_checked :
    (Witness.linear .positive case_52_35_16).check 52 35 16 = true := by
  change case_52_35_16.check 52 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_17 : Certificate := {
  objectiveScale := 606946513484081232000000
  eta := 183215377020930479806111032902400
  rows := #[⟨.count 2, 23064347107244794443677098113600⟩, ⟨.count 3, 2828105527648906029547813190400⟩, ⟨.count 4, 339591049845100299300915020160⟩, ⟨.count 5, 38637616356355710531392755200⟩, ⟨.count 6, 4409727953714510441082868800⟩, ⟨.count 7, 601326539142887787420391200⟩, ⟨.count 8, 160353743771436743312104320⟩, ⟨.count 9, 53451247923812247770701440⟩, ⟨.path 6, 471178611434124099009504000⟩, ⟨.path 7, 149541529820242895610715440⟩, ⟨.privateRow 2 33, 1576477743452937482687125596000⟩, ⟨.privateRow 3 29, 118156210670917132540792645680⟩, ⟨.privateRow 3 30, 332068847240457134400358846080⟩, ⟨.privateRow 3 31, 492689104873069552670097635760⟩, ⟨.privateRow 4 26, 32052772590551066567188455480⟩, ⟨.privateRow 4 27, 80584628548451453660474368128⟩, ⟨.privateRow 4 28, 128711559487109960707702115760⟩, ⟨.privateRow 4 29, 178803969170852649551526799200⟩, ⟨.privateRow 4 30, 261040145831492894860530537000⟩, ⟨.privateRow 5 22, 228652560562974615463556160⟩, ⟨.privateRow 5 23, 5743145692099612407791260080⟩, ⟨.privateRow 5 24, 18724844821146921206285215680⟩, ⟨.privateRow 5 25, 32275008880281916894973187360⟩, ⟨.privateRow 5 26, 47532667600134123021119913408⟩, ⟨.privateRow 5 27, 64245536544712117592823986160⟩, ⟨.privateRow 5 28, 95236124663872427081545258560⟩, ⟨.privateRow 5 29, 86514662710970395320292473600⟩, ⟨.privateRow 6 20, 894194835058775728330692840⟩, ⟨.privateRow 6 21, 3768100870502081673200440800⟩, ⟨.privateRow 6 22, 8228867342199398948092139100⟩, ⟨.privateRow 6 23, 12989198666383557965910763200⟩, ⟨.privateRow 6 24, 18601352439676684916155117200⟩, ⟨.privateRow 6 25, 24407494245400790330247561120⟩, ⟨.privateRow 6 26, 35514059055807932302292389800⟩, ⟨.privateRow 6 27, 34128727853417461098909874800⟩, ⟨.privateRow 6 28, 7244553066816695724636141600⟩, ⟨.privateRow 7 17, 55678383253971091427814000⟩, ⟨.privateRow 7 18, 674214604493540852562256800⟩, ⟨.privateRow 7 19, 1959560928349759726308036720⟩, ⟨.privateRow 7 20, 3695984107430271497636796000⟩, ⟨.privateRow 7 21, 5705443472581923411595854600⟩, ⟨.privateRow 7 22, 7964508651096615796649671200⟩, ⟨.privateRow 7 23, 10265503061082155799533821200⟩, ⟨.privateRow 7 24, 14651368850544964344290484000⟩, ⟨.privateRow 7 25, 5476366695765585206864277000⟩, ⟨.privateRow 8 15, 50881476389013582012494640⟩, ⟨.privateRow 8 16, 424269280395259716679942680⟩, ⟨.privateRow 8 17, 1042299334514338831528678080⟩, ⟨.privateRow 8 18, 1854090162357237344546206200⟩, ⟨.privateRow 8 19, 2821780463311254913561613520⟩, ⟨.privateRow 8 20, 3890248637954960158061364180⟩, ⟨.privateRow 8 21, 4954739785223381753173413840⟩, ⟨.privateRow 8 22, 1841840918041363704432087120⟩, ⟨.privateRow 9 13, 37755246549359444853908160⟩, ⟨.privateRow 9 14, 269997329256179815662261120⟩, ⟨.privateRow 9 15, 621123297633188619928058400⟩, ⟨.privateRow 9 16, 1080903013570425454918629120⟩, ⟨.privateRow 9 17, 1632044769940400631932083968⟩, ⟨.privateRow 9 18, 1796225887019962202862337280⟩, ⟨.privateRow 10 11, 28952759292064967542463280⟩, ⟨.privateRow 10 12, 188511097588444980977027400⟩, ⟨.privateRow 10 13, 433777435074014779985307840⟩, ⟨.privateRow 10 14, 754998876923847999761157840⟩, ⟨.privateRow 10 15, 298841067937677567081648960⟩, ⟨.privateRow 11 9, 24458718357994443734361150⟩, ⟨.privateRow 11 10, 150808878070755984781621920⟩, ⟨.privateRow 11 11, 332024971159394957453209200⟩, ⟨.privateRow 12 7, 24704358284114904431836800⟩, ⟨.privateRow 12 8, 118117713045924386814719700⟩, ⟨.privateRow 13 5, 27998272721996891689415040⟩, ⟨.privateRow 13 6, 7411307485234471329551040⟩, ⟨.privateRow 14 3, 7183767343143939315047280⟩, ⟨.hall 4 30, 30538890178996158022393249920⟩, ⟨.hall 3 31, 135732345108656321899539260595⟩, ⟨.hall 2 32, 395205164336686806954623772000⟩, ⟨.assumptionRow 17, 726679719265533771038400⟩]
  caps := #[0, 42880655854560934188863631360, 3882844381678716903813793440, 1467325650772424264404286880, 692291021939165941322231124, 293678865948383695430359632, 0, 149454900795821132643309360, 0, 67114611036056470593175744, 18493070660675427745843200, 64680269430849387330638700, 2299772363578053852153600, 128326870576908348678527040, 193961596875583664690030160, 453063635534736429323472000, 79175635102800739385308800, 9591411009963847172961600] }

theorem case_52_35_17_checked :
    (Witness.linear .conditional case_52_35_17).check 52 35 17 = true := by
  change case_52_35_17.check 52 35 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_18 : Certificate := {
  objectiveScale := 714149880280122000000
  eta := 206465034122396913583601481600
  rows := #[⟨.count 2, 23950608099843791543574196800⟩, ⟨.count 3, 2650340255069369306858253840⟩, ⟨.count 4, 276923346933078748473611040⟩, ⟨.count 5, 27368474412756917984544000⟩, ⟨.count 6, 3078953371435153273261200⟩, ⟨.count 7, 725679245792797067772000⟩, ⟨.count 8, 232217358653695061687040⟩, ⟨.count 9, 58054339663423765421760⟩, ⟨.path 5, 1324170191787120387309600⟩, ⟨.path 6, 1001523065720736560601600⟩, ⟨.privateRow 2 32, 448814471541700166490287700⟩, ⟨.privateRow 2 33, 2158460348686095598381036800⟩, ⟨.privateRow 3 29, 181774184813228082844428660⟩, ⟨.privateRow 3 30, 448756820357173294278792480⟩, ⟨.privateRow 3 31, 656185782284859511238594040⟩, ⟨.privateRow 4 26, 36023754445791293297156040⟩, ⟨.privateRow 4 27, 98731771444020581629242480⟩, ⟨.privateRow 4 28, 162514571239500844761346950⟩, ⟨.privateRow 4 29, 241344330196494755093703840⟩, ⟨.privateRow 4 30, 372986692121855530599360480⟩, ⟨.privateRow 5 23, 4983343049322822149685720⟩, ⟨.privateRow 5 24, 19659687453163719418897440⟩, ⟨.privateRow 5 25, 37639254671544305817077040⟩, ⟨.privateRow 5 26, 59663274219810081206305920⟩, ⟨.privateRow 5 27, 87179994535636099163266200⟩, ⟨.privateRow 5 28, 140597934941535122557265760⟩, ⟨.privateRow 5 29, 144254667217239588543534000⟩, ⟨.privateRow 6 20, 372515346173635828122960⟩, ⟨.privateRow 6 21, 3188765151486338438014000⟩, ⟨.privateRow 6 22, 8414855587672309331706150⟩, ⟨.privateRow 6 23, 14808299548330975266637200⟩, ⟨.privateRow 6 24, 23269538545846333277136600⟩, ⟨.privateRow 6 25, 33454158792593560441940520⟩, ⟨.privateRow 6 26, 53558583954964579778086800⟩, ⟨.privateRow 6 27, 59767173057858510246802800⟩, ⟨.privateRow 6 28, 43095844257587716340245500⟩, ⟨.privateRow 7 18, 278019970790746928562000⟩, ⟨.privateRow 7 19, 1627594879849559137717200⟩, ⟨.privateRow 7 20, 3674471101712734359036000⟩, ⟨.privateRow 7 21, 6371722949219969968276650⟩, ⟨.privateRow 7 22, 9860351874466209953522400⟩, ⟨.privateRow 7 23, 14055715867915247967441000⟩, ⟨.privateRow 7 24, 22315673492765356686942960⟩, ⟨.privateRow 7 25, 25974133576197900761467800⟩, ⟨.privateRow 7 26, 4395542860230656524790400⟩, ⟨.privateRow 8 16, 160858899484070016689460⟩, ⟨.privateRow 8 17, 824635506582723940650000⟩, ⟨.privateRow 8 18, 1775011435209181627770312⟩, ⟨.privateRow 8 19, 3061560106972500518144760⟩, ⟨.privateRow 8 20, 4699680215565602010158415⟩, ⟨.privateRow 8 21, 6644111837551480581929640⟩, ⟨.privateRow 8 22, 10507835479079701541338560⟩, ⟨.privateRow 8 23, 4708206946703667375704736⟩, ⟨.privateRow 9 14, 91795323399430740196800⟩, ⟨.privateRow 9 15, 448846052027396704881200⟩, ⟨.privateRow 9 16, 980473292093379149345280⟩, ⟨.privateRow 9 17, 1693251573516526491468000⟩, ⟨.privateRow 9 18, 2597394159756144764055040⟩, ⟨.privateRow 9 19, 3667099122072934515807840⟩, ⟨.privateRow 9 20, 1923165188532784102146240⟩, ⟨.privateRow 10 12, 55980970389730059513840⟩, ⟨.privateRow 10 13, 273525254183438894775600⟩, ⟨.privateRow 10 14, 630131478430078787182020⟩, ⟨.privateRow 10 15, 1111608662873511871996200⟩, ⟨.privateRow 10 16, 1718408454037343456484096⟩, ⟨.privateRow 10 17, 58860649936526873274840⟩, ⟨.privateRow 11 10, 38702893108949176947840⟩, ⟨.privateRow 11 11, 193267635869306157845400⟩, ⟨.privateRow 11 12, 479267282111506634869200⟩, ⟨.privateRow 11 13, 564993127081534859908200⟩, ⟨.privateRow 12 8, 30884563139395827586725⟩, ⟨.privateRow 12 9, 163450611076187149074360⟩, ⟨.privateRow 12 10, 207707171882530181132700⟩, ⟨.privateRow 13 6, 32198205191478727040640⟩, ⟨.privateRow 13 7, 88377365291194214325090⟩, ⟨.privateRow 14 4, 32943534015355549425840⟩, ⟨.hall 5 29, 182456496085046119896960⟩, ⟨.hall 4 30, 62741491879567472196825600⟩, ⟨.hall 3 31, 212992301234529385369090290⟩, ⟨.hall 2 32, 557224903536095775106526400⟩, ⟨.assumptionRow 18, 693659272176700038000⟩]
  caps := #[0, 25875034953426175710996000, 119681226060095451420900, 103453754170396839383460, 522631926207232129781460, 0, 0, 0, 89217157481034216793341, 22722878622029957028240, 67943275291234732212564, 8874136281573146760000, 289424015156551982539635, 693659272176700038000, 0, 1986948997869986973900000, 464455395092678950224000, 84618026210812569354000] }

theorem case_52_35_18_checked :
    (Witness.linear .conditional case_52_35_18).check 52 35 18 = true := by
  change case_52_35_18.check 52 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_19 : Certificate := {
  objectiveScale := 3101014453408872000000
  eta := 971058103791586931317807209600
  rows := #[⟨.count 2, 106096627908493468258883270400⟩, ⟨.count 3, 10783999972858608393449872320⟩, ⟨.count 4, 992654566950693415299410880⟩, ⟨.count 5, 80052787657313985104791200⟩, ⟨.count 6, 7184224533348690970942800⟩, ⟨.count 7, 1741630189902712962652800⟩, ⟨.count 8, 522489056970813888795840⟩, ⟨.count 9, 174163018990271296265280⟩, ⟨.path 5, 18510922934498754354394800⟩, ⟨.path 6, 2395572564898811893795200⟩, ⟨.privateRow 2 32, 2280392603960430325693427100⟩, ⟨.privateRow 2 33, 10413533461088927562381588600⟩, ⟨.privateRow 3 29, 792300228952804802578808460⟩, ⟨.privateRow 3 30, 2055380030752048084227583440⟩, ⟨.privateRow 3 31, 3135993833523740816493987120⟩, ⟨.privateRow 4 26, 140759484964110423809257860⟩, ⟨.privateRow 4 27, 418231341738544842180809136⟩, ⟨.privateRow 4 28, 733261298055535738564024950⟩, ⟨.privateRow 4 29, 1154094355392943285260739800⟩, ⟨.privateRow 4 30, 1885020780475140699259208340⟩, ⟨.privateRow 5 23, 16900032949877396855455920⟩, ⟨.privateRow 5 24, 74989619890953955277650560⟩, ⟨.privateRow 5 25, 156479252454937678576630320⟩, ⟨.privateRow 5 26, 265611044175805889039999520⟩, ⟨.privateRow 5 27, 415795547515809476480184720⟩, ⟨.privateRow 5 28, 719562806435400635343636000⟩, ⟨.privateRow 5 29, 811201581594115049061884160⟩, ⟨.privateRow 6 20, 917984245927888290731580⟩, ⟨.privateRow 6 21, 10440566164866527971881600⟩, ⟨.privateRow 6 22, 31324074230225691286997625⟩, ⟨.privateRow 6 23, 60096608398012065741061200⟩, ⟨.privateRow 6 24, 101966573072528378463249000⟩, ⟨.privateRow 6 25, 158360835070814716688067720⟩, ⟨.privateRow 6 26, 275038913434450381516550250⟩, ⟨.privateRow 6 27, 342676106709727243931478000⟩, ⟨.privateRow 6 28, 297546632756191617713214300⟩, ⟨.privateRow 7 18, 579600956055285969714000⟩, ⟨.privateRow 7 19, 5144029168034084357549520⟩, ⟨.privateRow 7 20, 13228095966165843692529600⟩, ⟨.privateRow 7 21, 25094247490674134316794250⟩, ⟨.privateRow 7 22, 42234532105140789344330400⟩, ⟨.privateRow 7 23, 65430350854589124189185400⟩, ⟨.privateRow 7 24, 113660030214615264166266480⟩, ⟨.privateRow 7 25, 148543949902193442640543500⟩, ⟨.privateRow 7 26, 120545689572552061486468800⟩, ⟨.privateRow 8 16, 277572311515744878422790⟩, ⟨.privateRow 8 17, 2487760396258761584152920⟩, ⟨.privateRow 8 18, 6119653079770657672521276⟩, ⟨.privateRow 8 19, 11615705794323371731470480⟩, ⟨.privateRow 8 20, 19468159966506263335653330⟩, ⟨.privateRow 8 21, 30027570506269095811451400⟩, ⟨.privateRow 8 22, 52216250131020713011534260⟩, ⟨.privateRow 8 23, 71489565220031610334490808⟩, ⟨.privateRow 8 24, 13595600669928053064708420⟩, ⟨.privateRow 9 14, 128017261821908816058240⟩, ⟨.privateRow 9 15, 1267519749318085545041760⟩, ⟨.privateRow 9 16, 3208821683214695397857280⟩, ⟨.privateRow 9 17, 6132473413112997087385248⟩, ⟨.privateRow 9 18, 10292819406252206113850560⟩, ⟨.privateRow 9 19, 15846415797295378636581240⟩, ⟨.privateRow 9 20, 27467996137894215868124160⟩, ⟨.privateRow 9 21, 14590990702073839709335680⟩, ⟨.privateRow 10 12, 63756105166081456668540⟩, ⟨.privateRow 10 13, 706699942441293144461040⟩, ⟨.privateRow 10 14, 1939377784381250163620670⟩, ⟨.privateRow 10 15, 3807836915196386068345440⟩, ⟨.privateRow 10 16, 6441854664902659570612044⟩, ⟨.privateRow 10 17, 9953900321457866446272600⟩, ⟨.privateRow 10 18, 5978689886275406842106565⟩, ⟨.privateRow 11 10, 37320646926486706342560⟩, ⟨.privateRow 11 11, 444293415791508408840000⟩, ⟨.privateRow 11 12, 1368423720637845899227200⟩, ⟨.privateRow 11 13, 2840515904960377093850400⟩, ⟨.privateRow 11 14, 4919539822127793108792000⟩, ⟨.privateRow 11 15, 556699649986760036276520⟩, ⟨.privateRow 12 8, 28508827513288456233900⟩, ⟨.privateRow 12 9, 326901222152374298148720⟩, ⟨.privateRow 12 10, 1136280410886782755608300⟩, ⟨.privateRow 12 11, 2008775846320940454634800⟩, ⟨.privateRow 13 6, 24148653893609045280480⟩, ⟨.privateRow 13 7, 290790040635542253585780⟩, ⟨.privateRow 13 8, 830177057186959845531168⟩, ⟨.privateRow 14 4, 24707650511516662069380⟩, ⟨.privateRow 14 5, 313932500616917588646240⟩, ⟨.hall 5 29, 56470285538321774108109120⟩, ⟨.hall 4 30, 401755961569071834923758560⟩, ⟨.hall 3 31, 1159653576758034534226350300⟩, ⟨.hall 2 32, 2795243886869275025350966800⟩, ⟨.assumptionRow 19, 2204002219021709715180⟩]
  caps := #[0, 179256777705079857729203400, 0, 0, 0, 0, 409903931802802948966455, 207759400732348932121200, 57595541658353503344372, 0, 54137348241761317289466, 23294556567690741839220, 2204002219021709715180, 238437183052748291127516, 0, 24887884837409732153258100, 7255855245280266551286360, 1758432283042151324450700] }

theorem case_52_35_19_checked :
    (Witness.linear .conditional case_52_35_19).check 52 35 19 = true := by
  change case_52_35_19.check 52 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_20 : Certificate := {
  objectiveScale := 8295632468323200000
  eta := 2716793772637556309002905600
  rows := #[⟨.count 2, 324764854131609332811770400⟩, ⟨.count 3, 36505889719993766002170240⟩, ⟨.count 4, 3766154780690341920840960⟩, ⟨.count 5, 318133132085632764700800⟩, ⟨.count 6, 17486040947969176783200⟩, ⟨.path 6, 17064618384521740032000⟩, ⟨.privateRow 2 32, 12242202894008033171425200⟩, ⟨.privateRow 2 33, 38446163386213907108584800⟩, ⟨.privateRow 3 29, 2929231496092488160654080⟩, ⟨.privateRow 3 30, 7678966679008812421153920⟩, ⟨.privateRow 3 31, 11496207022339619130510960⟩, ⟨.privateRow 4 26, 498023128612186634457000⟩, ⟨.privateRow 4 27, 1496049256924539639193872⟩, ⟨.privateRow 4 28, 2645694402011439573674880⟩, ⟨.privateRow 4 29, 4229102415336467803374240⟩, ⟨.privateRow 4 30, 7032942075856906028579760⟩, ⟨.privateRow 5 22, 5590519184798747559360⟩, ⟨.privateRow 5 23, 62075445365290577580360⟩, ⟨.privateRow 5 24, 263628256061640362967360⟩, ⟨.privateRow 5 25, 550152213051159260942400⟩, ⟨.privateRow 5 26, 942621701579685506643264⟩, ⟨.privateRow 5 27, 1505153279534224236396480⟩, ⟨.privateRow 5 28, 2681268154133544608592960⟩, ⟨.privateRow 5 29, 3140718580590076655769600⟩, ⟨.privateRow 6 19, 1393071688425696879600⟩, ⟨.privateRow 6 20, 7596086605354352064960⟩, ⟨.privateRow 6 21, 38074443999610304286000⟩, ⟨.privateRow 6 22, 108629679114937547166600⟩, ⟨.privateRow 6 23, 207495647193643457220000⟩, ⟨.privateRow 6 24, 355831532193888893142000⟩, ⟨.privateRow 6 25, 565043551148784624396480⟩, ⟨.privateRow 6 26, 1015271501169855508979400⟩, ⟨.privateRow 6 27, 1328124350281056721192800⟩, ⟨.privateRow 6 28, 1240474786604587568034000⟩, ⟨.privateRow 7 16, 193281300800922549600⟩, ⟨.privateRow 7 17, 918743598194861439000⟩, ⟨.privateRow 7 18, 5015990418559006723200⟩, ⟨.privateRow 7 19, 18578277523311532986960⟩, ⟨.privateRow 7 20, 45290498369308239247200⟩, ⟨.privateRow 7 21, 85122662679263441232000⟩, ⟨.privateRow 7 22, 144693875494045739347200⟩, ⟨.privateRow 7 23, 229480784698885809289200⟩, ⟨.privateRow 7 24, 413706396363711801910560⟩, ⟨.privateRow 7 25, 570129544779349852697400⟩, ⟨.privateRow 7 26, 611874689945701487104800⟩, ⟨.privateRow 7 27, 20921714682614147001600⟩, ⟨.privateRow 8 13, 14358039488068532256⟩, ⟨.privateRow 8 14, 99993489291905849640⟩, ⟨.privateRow 8 15, 629544808323004875840⟩, ⟨.privateRow 8 16, 2880581672293749283860⟩, ⟨.privateRow 8 17, 9198934844742089188560⟩, ⟨.privateRow 8 18, 20786851668851217573624⟩, ⟨.privateRow 8 19, 38830520126620897234560⟩, ⟨.privateRow 8 20, 65504068276972657001670⟩, ⟨.privateRow 8 21, 103265071146687179489760⟩, ⟨.privateRow 8 22, 186457090301929977009480⟩, ⟨.privateRow 8 23, 269320925697445493791920⟩, ⟨.privateRow 8 24, 171470886586258446467280⟩, ⟨.privateRow 9 10, 1876867906937063040⟩, ⟨.privateRow 9 11, 7976688604482517920⟩, ⟨.privateRow 9 12, 76576210603032172032⟩, ⟨.privateRow 9 13, 428462130755060962560⟩, ⟨.privateRow 9 14, 1749962761537241623680⟩, ⟨.privateRow 9 15, 5057220575241916361280⟩, ⟨.privateRow 9 16, 10987525975919919229440⟩, ⟨.privateRow 9 17, 20334174590546834681664⟩, ⟨.privateRow 9 18, 34111865667702572189440⟩, ⟨.privateRow 9 19, 53411906895614939992320⟩, ⟨.privateRow 9 20, 95797751085948045214080⟩, ⟨.privateRow 9 21, 116480924795056715013120⟩, ⟨.privateRow 10 8, 1994172151120629480⟩, ⟨.privateRow 10 9, 8445905581216783680⟩, ⟨.privateRow 10 10, 65059866430310536785⟩, ⟨.privateRow 10 11, 330234908225576241888⟩, ⟨.privateRow 10 12, 1215305485240086480240⟩, ⟨.privateRow 10 13, 3263692822095577908960⟩, ⟨.privateRow 10 14, 6927754052993066813520⟩, ⟨.privateRow 10 15, 12697075374562422501840⟩, ⟨.privateRow 10 16, 21174518735029067944536⟩, ⟨.privateRow 10 17, 32991584068139694117120⟩, ⟨.privateRow 10 18, 49790988812217657014010⟩, ⟨.privateRow 11 6, 2698879603020400800⟩, ⟨.privateRow 11 7, 8546452076231269200⟩, ⟨.privateRow 11 8, 66360686709560443200⟩, ⟨.privateRow 11 9, 301262435687152239300⟩, ⟨.privateRow 11 10, 1008481344995289765600⟩, ⟨.privateRow 11 11, 2574923918395963820400⟩, ⟨.privateRow 11 12, 5376375775339947655200⟩, ⟨.privateRow 11 13, 9789960853322918868600⟩, ⟨.privateRow 11 14, 16255351848991874018400⟩, ⟨.privateRow 11 15, 11829998963919322826640⟩, ⟨.privateRow 12 5, 9895891877741469600⟩, ⟨.privateRow 12 6, 78342477365453301000⟩, ⟨.privateRow 12 7, 331803433547802216000⟩, ⟨.privateRow 12 8, 1039996387026392570775⟩, ⟨.privateRow 12 9, 2563365859397632008720⟩, ⟨.privateRow 12 10, 5284759687423864104600⟩, ⟨.privateRow 12 11, 7426866854244972934800⟩, ⟨.privateRow 13 2, 10744111181547881280⟩, ⟨.privateRow 13 3, 22562633481250550688⟩, ⟨.privateRow 13 4, 118750702532897635200⟩, ⟨.privateRow 13 5, 463787466003483541920⟩, ⟨.privateRow 13 6, 1380302283558857218560⟩, ⟨.privateRow 13 7, 3299785146632893038120⟩, ⟨.privateRow 13 8, 466294425279178047552⟩, ⟨.privateRow 14 1, 69836722680061228320⟩, ⟨.privateRow 14 2, 219985676442192869208⟩, ⟨.privateRow 14 3, 849067523110218091680⟩, ⟨.privateRow 14 4, 774023676370678613880⟩, ⟨.privateRow 15 0, 651809411680571464320⟩, ⟨.hall 5 29, 308318386521288775151520⟩, ⟨.hall 4 30, 1636220345253695177296320⟩, ⟨.hall 3 31, 4461217857549153807176070⟩, ⟨.hall 2 32, 10446430930202395118390400⟩, ⟨.assumptionRow 20, 2329927908118530720⟩]
  caps := #[0, 122405351570793656164800, 0, 0, 0, 47233632459212559360, 1455296917711271572080, 21860320916688038400, 86116622844435753066, 322579929739639187168, 944607861057140280, 0, 2835373824040466342205, 0, 0, 0, 57534642465540877596960, 17070657055834674932640] }

theorem case_52_35_20_checked :
    (Witness.linear .conditional case_52_35_20).check 52 35 20 = true := by
  change case_52_35_20.check 52 35 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_21 : Certificate := {
  objectiveScale := 584467012984670816000000
  eta := 1035971088554787488622968248800000
  rows := #[⟨.count 2, 49921795209343020285092310540000⟩, ⟨.count 3, 2705263106081144667260504702400⟩, ⟨.count 4, 278052846278774131145558577600⟩, ⟨.count 5, 23698537982547369037112016000⟩, ⟨.count 6, 1349916720524850135025368000⟩, ⟨.path 2, 26378362657983956528494709323200⟩, ⟨.path 6, 1196734610238562008117504000⟩, ⟨.path 7, 8190633363715494653761800⟩, ⟨.privateRow 2 33, 4142519438423952606022014012000⟩, ⟨.privateRow 4 26, 35926533609301636510216807800⟩, ⟨.privateRow 4 27, 88895015861495881058387205840⟩, ⟨.privateRow 4 30, 1847608516770353632306970758800⟩, ⟨.privateRow 5 23, 4207240445635782920829063600⟩, ⟨.privateRow 5 24, 19203101030704296682694203200⟩, ⟨.privateRow 5 25, 39252578417928142259570978400⟩, ⟨.privateRow 5 28, 561385366842267676152549705600⟩, ⟨.privateRow 5 29, 231105742553854343116343001600⟩, ⟨.privateRow 6 19, 28407338394883209912150000⟩, ⟨.privateRow 6 20, 377476712591208093312649200⟩, ⟨.privateRow 6 21, 2534565859010135284384050000⟩, ⟨.privateRow 6 22, 7821392480263194185112259500⟩, ⟨.privateRow 6 24, 53282129569234709727691107000⟩, ⟨.privateRow 6 25, 16463984298845672202364951200⟩, ⟨.privateRow 6 26, 58312027596560713818769426500⟩, ⟨.privateRow 6 27, 112488893634106261714660218000⟩, ⟨.privateRow 6 29, 1152391406316940813879017162000⟩, ⟨.privateRow 7 16, 7342204385139045023448000⟩, ⟨.privateRow 7 17, 34088806073859851894580000⟩, ⟨.privateRow 7 18, 261554112057615590900232000⟩, ⟨.privateRow 7 19, 1214243272350887924484939600⟩, ⟨.privateRow 7 20, 3186924603393964376011068000⟩, ⟨.privateRow 7 21, 3481319320292937374733982500⟩, ⟨.privateRow 7 22, 9474740156757389692299264000⟩, ⟨.privateRow 7 23, 28786860435838849596576324000⟩, ⟨.privateRow 7 24, 24638025477942946555326640800⟩, ⟨.privateRow 7 25, 48343040333644348964298627000⟩, ⟨.privateRow 7 26, 69041195234924153370489360000⟩, ⟨.privateRow 7 27, 32138926366435068366210024000⟩, ⟨.privateRow 8 13, 954486570068075853048240⟩, ⟨.privateRow 8 14, 4431544789601780746295400⟩, ⟨.privateRow 8 15, 24963494909472753079723200⟩, ⟨.privateRow 8 16, 151127040260778676732638000⟩, ⟨.privateRow 8 17, 585707667996319273461420000⟩, ⟨.privateRow 8 18, 1421707746116398983115353480⟩, ⟨.privateRow 8 19, 2236680195859524415643042400⟩, ⟨.privateRow 8 20, 3699232013120086477970085150⟩, ⟨.privateRow 8 22, 37699037895788769275895319200⟩, ⟨.privateRow 8 23, 13502167020183001017220403040⟩, ⟨.privateRow 8 25, 112336706053212074064757526400⟩, ⟨.privateRow 9 11, 530270316704486585026800⟩, ⟨.privateRow 9 12, 3393730026908714144171520⟩, ⟨.privateRow 9 13, 16665638524998149815128000⟩, ⟨.privateRow 9 14, 88432772816563608949084800⟩, ⟨.privateRow 9 15, 302254080521557353465276000⟩, ⟨.privateRow 9 16, 699571166910500847446265600⟩, ⟨.privateRow 9 17, 1218773295913591967025597120⟩, ⟨.privateRow 9 18, 1871736380118681092570153600⟩, ⟨.privateRow 9 19, 2913835390291153784722266000⟩, ⟨.privateRow 9 20, 762983232835369840627132800⟩, ⟨.privateRow 9 21, 26113338502884676708506441600⟩, ⟨.privateRow 9 23, 25054211923653582169346246400⟩, ⟨.privateRow 10 9, 561462688275338737087200⟩, ⟨.privateRow 10 10, 2982770531462737040775750⟩, ⟨.privateRow 10 11, 13044649790930369991659280⟩, ⟨.privateRow 10 12, 59996298689993339334460800⟩, ⟨.privateRow 10 13, 187960432259559552600268800⟩, ⟨.privateRow 10 14, 428325848318049039055397700⟩, ⟨.privateRow 10 15, 787885277838011704152547200⟩, ⟨.privateRow 10 16, 1265649191910268581141966240⟩, ⟨.privateRow 10 17, 1897837463485357487810917200⟩, ⟨.privateRow 10 18, 3416465366737419006504544050⟩, ⟨.privateRow 10 19, 1508770556829037044854110800⟩, ⟨.privateRow 10 20, 20842805068386549711063400800⟩, ⟨.privateRow 10 21, 7625393208273857990002389360⟩, ⟨.privateRow 11 7, 757529023863552264324000⟩, ⟨.privateRow 11 8, 3208358218716221354784000⟩, ⟨.privateRow 11 9, 11931082125850948163103000⟩, ⟨.privateRow 11 10, 48633363332040055369600800⟩, ⟨.privateRow 11 11, 142686002566299094358742000⟩, ⟨.privateRow 11 12, 322008106605383831742648000⟩, ⟨.privateRow 11 13, 606212601346807699525281000⟩, ⟨.privateRow 11 14, 1009028659786251616079568000⟩, ⟨.privateRow 11 15, 1546268243510282881938148800⟩, ⟨.privateRow 11 16, 2655896757665614238719944000⟩, ⟨.privateRow 11 18, 11360338115585751785668032000⟩, ⟨.privateRow 11 19, 3065719959575796013719228000⟩, ⟨.privateRow 11 20, 30324038331062769851342584800⟩, ⟨.privateRow 12 5, 657854152302558545334000⟩, ⟨.privateRow 12 6, 3472008026041281211485000⟩, ⟨.privateRow 12 7, 13234477652204413088484000⟩, ⟨.privateRow 12 8, 48434511963275872900215750⟩, ⟨.privateRow 12 9, 135824953978734920993293200⟩, ⟨.privateRow 12 10, 304445503769162629658499000⟩, ⟨.privateRow 12 11, 580733403986473989711768000⟩, ⟨.privateRow 12 12, 987439082606140376546334000⟩, ⟨.privateRow 12 13, 1540814034538465305635016000⟩, ⟨.privateRow 12 14, 2632337605023457763299467600⟩, ⟨.privateRow 12 17, 26801917956452381649114780000⟩, ⟨.privateRow 12 19, 26835844434878270739809862000⟩, ⟨.privateRow 13 3, 1499907467249833483361520⟩, ⟨.privateRow 13 4, 6315399862104562035206400⟩, ⟨.privateRow 13 5, 19998766229997779778153600⟩, ⟨.privateRow 13 6, 61760895710287261079592000⟩, ⟨.privateRow 13 8, 705956447918921626168822080⟩, ⟨.privateRow 13 9, 552823037929224341010388800⟩, ⟨.privateRow 13 10, 1246076972792169355408032000⟩, ⟨.privateRow 13 11, 1982377702548529920509475600⟩, ⟨.privateRow 13 12, 3408880607385985189458000000⟩, ⟨.privateRow 13 15, 17102694895316226294029731800⟩, ⟨.privateRow 13 17, 139991363609984458447075200⟩, ⟨.privateRow 13 18, 44673244004569040468439511680⟩, ⟨.privateRow 13 20, 112193078550287544555441696000⟩, ⟨.privateRow 14 1, 4642570731963770305642800⟩, ⟨.privateRow 14 2, 9749398537123917641849880⟩, ⟨.privateRow 14 3, 35918836715719696575236400⟩, ⟨.privateRow 14 4, 108326650412487973798332000⟩, ⟨.privateRow 14 5, 108963866003149667761851600⟩, ⟨.privateRow 14 6, 530123545456113021775587225⟩, ⟨.privateRow 14 7, 1865384920103042908807277040⟩, ⟨.privateRow 14 8, 1699180887898739931865264800⟩, ⟨.privateRow 14 10, 3387915991650561380542833300⟩, ⟨.privateRow 14 11, 19108821132762878578025764800⟩, ⟨.privateRow 14 14, 31368689793196205012651988900⟩, ⟨.privateRow 14 15, 17033592015575073251403433200⟩, ⟨.privateRow 14 17, 55552072864532082723260616240⟩, ⟨.privateRow 14 18, 77142115924992998341137175500⟩, ⟨.privateRow 14 19, 82219927663078372112933988000⟩, ⟨.privateRow 14 20, 249048385630830476161055184600⟩, ⟨.privateRow 15 0, 64995990247492784278999200⟩, ⟨.privateRow 15 1, 90994386346489897990598880⟩, ⟨.privateRow 15 2, 263404802581944441551733600⟩, ⟨.privateRow 15 3, 429695713302868962733383600⟩, ⟨.privateRow 15 4, 856417753849316686970342400⟩, ⟨.privateRow 15 5, 3014189047727477870938587900⟩, ⟨.privateRow 15 9, 63544413131965445430101551200⟩, ⟨.privateRow 15 12, 131790202891832868923050711200⟩, ⟨.privateRow 15 15, 217779897989265822524166652800⟩, ⟨.privateRow 15 18, 773452283945164132920090480000⟩, ⟨.privateRow 16 0, 2388602641595359822253220600⟩, ⟨.privateRow 16 1, 1257159285050189380133274000⟩, ⟨.privateRow 16 2, 3412289487993371174647458000⟩, ⟨.privateRow 16 5, 36852726470328408686192546400⟩, ⟨.privateRow 16 13, 3186590911858952481238633278000⟩, ⟨.privateRow 16 18, 6225722170843905708144287121000⟩, ⟨.privateRow 17 0, 109193263615787877588718656000⟩, ⟨.privateRow 17 4, 549606093532798983863217235200⟩, ⟨.privateRow 17 12, 22306623852939523564552525440000⟩, ⟨.privateRow 17 15, 39500663113011264717718973808000⟩, ⟨.hall 8 12, 9451479538505933630240⟩, ⟨.hall 9 12, 11334509488621232716572⟩, ⟨.hall 16 15, 26270051166594993769731720000⟩, ⟨.hall 14 17, 234821770613456386710910560⟩, ⟨.hall 15 19, 61421210783880681143654244000⟩, ⟨.hall 11 20, 7654101488012631341547000⟩, ⟨.hall 10 21, 1847667184548775292610180⟩, ⟨.hall 6 22, 189646218581086743616800⟩, ⟨.hall 12 22, 1741196929372632782858808000⟩, ⟨.hall 4 25, 3361552598294027993856000⟩, ⟨.hall 3 29, 1273646224214730074193009525⟩, ⟨.hall 5 29, 4419727336829509330971945600⟩, ⟨.hall 2 32, 3646806838259097411741410568000⟩]
  caps := #[0, 0, 2895885229559302468247760000, 246167518406808344342756760, 34363972782994996518903240, 0, 0, 83947127808706389485665200, 0, 1351507942005338824855456, 174950623358275547614206620, 0, 100884427221362260315019400, 181191425326315357117948960, 950860111101941743874058745, 0, 64966680286138064072292654000, 0] }

theorem case_52_35_21_checked :
    (Witness.linear .conditional case_52_35_21).check 52 35 21 = true := by
  change case_52_35_21.check 52 35 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_35_22 : Certificate := {
  objectiveScale := 1534336734784236514560000
  eta := 2856948577751836689711194001196800
  rows := #[⟨.count 2, 118675678223254580578332910728000⟩, ⟨.count 3, 4143197846385247979486221384320⟩, ⟨.count 4, 366278861499784895047468642560⟩, ⟨.count 5, 26031524437693742540999025600⟩, ⟨.count 6, 1020844095595833040823491200⟩, ⟨.path 2, 77243699759402100783470696884800⟩, ⟨.path 3, 114436349431548756307133518080⟩, ⟨.path 5, 5974784050845918199191300000⟩, ⟨.path 6, 1054862065951867291044326400⟩, ⟨.privateRow 2 33, 11136005422319094204953156691600⟩, ⟨.privateRow 3 32, 20536388727374413004448894036480⟩, ⟨.privateRow 4 26, 63534784399645658878252033560⟩, ⟨.privateRow 4 27, 168806779647726951630572504832⟩, ⟨.privateRow 5 23, 5614642525777081724529201600⟩, ⟨.privateRow 5 24, 31602416502231002849492934720⟩, ⟨.privateRow 5 25, 71833396193426784972612997440⟩, ⟨.privateRow 5 26, 125808826341230463951087055488⟩, ⟨.privateRow 5 29, 2297205468319303091765102247360⟩, ⟨.privateRow 6 19, 15467334781755046073083200⟩, ⟨.privateRow 6 20, 370055984653489477298515560⟩, ⟨.privateRow 6 21, 3237399099459007560018942000⟩, ⟨.privateRow 6 22, 12239495354487539895706649700⟩, ⟨.privateRow 6 23, 26870074944790319681675464800⟩, ⟨.privateRow 6 24, 53799901676922062130621352200⟩, ⟨.privateRow 6 25, 104619505730312956133727456480⟩, ⟨.privateRow 7 16, 3569384949635779863019200⟩, ⟨.privateRow 7 17, 19334168477193807591354000⟩, ⟨.privateRow 7 18, 244665113820488910610588800⟩, ⟨.privateRow 7 19, 1489504339483010936837912160⟩, ⟨.privateRow 7 20, 4712381330174704036932681600⟩, ⟨.privateRow 7 21, 10353447219537283965170067000⟩, ⟨.privateRow 7 22, 20870958668723898240472480800⟩, ⟨.privateRow 7 23, 40377477447771547773783693600⟩, ⟨.privateRow 7 25, 277483985984685526551112608000⟩, ⟨.privateRow 7 26, 72650071469903451405271790400⟩, ⟨.privateRow 8 14, 2320100217263256910962480⟩, ⟨.privateRow 8 15, 13742132056097752472623920⟩, ⟨.privateRow 8 16, 133985787546953086608083220⟩, ⟨.privateRow 8 17, 677680181642440404992949840⟩, ⟨.privateRow 8 18, 1927771270524040167318724632⟩, ⟨.privateRow 8 19, 4170251246074189672071115440⟩, ⟨.privateRow 8 20, 8104110058900556389991942640⟩, ⟨.privateRow 8 21, 14946085599609901020420296160⟩, ⟨.privateRow 8 22, 33837501618675970417932289560⟩, ⟨.privateRow 8 23, 18036923109048011877204512016⟩, ⟨.privateRow 8 24, 139942064829722182912751646780⟩, ⟨.privateRow 8 25, 113094831823975633629473395920⟩, ⟨.privateRow 9 12, 962411941975869533436288⟩, ⟨.privateRow 9 13, 9280400869053027643849920⟩, ⟨.privateRow 9 14, 77733272236512539239084800⟩, ⟨.privateRow 9 15, 344062269256373358203472960⟩, ⟨.privateRow 9 16, 930477363901215680735902080⟩, ⟨.privateRow 9 17, 2008072516932651781514814912⟩, ⟨.privateRow 9 18, 3905788464518737189862268800⟩, ⟨.privateRow 9 19, 7248766445469502342150441680⟩, ⟨.privateRow 9 20, 16036532701723631768572661760⟩, ⟨.privateRow 9 21, 32094032235040309266266614080⟩, ⟨.privateRow 9 22, 32550696701507859359882132736⟩, ⟨.privateRow 9 23, 99840614860576705398680517120⟩, ⟨.privateRow 10 10, 1015043845052674898546085⟩, ⟨.privateRow 10 11, 7578994043059972575810768⟩, ⟨.privateRow 10 12, 51042204779791652041174560⟩, ⟨.privateRow 10 13, 203633411376721241185245360⟩, ⟨.privateRow 10 14, 533236366601005213369543320⟩, ⟨.privateRow 10 15, 1135372679048010177428275440⟩, ⟨.privateRow 10 16, 2166509582880429303456763824⟩, ⟨.privateRow 10 17, 3894159320219862099666580320⟩, ⟨.privateRow 10 18, 8380201984754883962396477760⟩, ⟨.privateRow 10 19, 16377587433661330534484146320⟩, ⟨.privateRow 10 20, 30286201552785011839552386840⟩, ⟨.privateRow 10 21, 34647912624566026056931483824⟩, ⟨.privateRow 10 22, 68742829362347354829135060540⟩, ⟨.privateRow 11 8, 1364764833684268771154400⟩, ⟨.privateRow 11 9, 5800250543158142277406200⟩, ⟨.privateRow 11 10, 40215070432563119790016320⟩, ⟨.privateRow 11 11, 145834870799404720117641600⟩, ⟨.privateRow 11 12, 376570112186574775548525600⟩, ⟨.privateRow 11 13, 792700907564946111245514000⟩, ⟨.privateRow 11 14, 1491191685095566032773157600⟩, ⟨.privateRow 11 15, 2614752944855690538654714960⟩, ⟨.privateRow 11 16, 5362009391008415972002176000⟩, ⟨.privateRow 11 17, 10359247470080442107447473200⟩, ⟨.privateRow 11 18, 19061280499258557849921746400⟩, ⟨.privateRow 11 19, 33018892925351584604514361200⟩, ⟨.privateRow 11 20, 40662076407755840621528424480⟩, ⟨.privateRow 11 21, 60618418426545744941172196200⟩, ⟨.privateRow 12 6, 2363065036101465372276600⟩, ⟨.privateRow 12 7, 7506206585263478241349200⟩, ⟨.privateRow 12 8, 37218274318598079613356450⟩, ⟨.privateRow 12 9, 130441189992800888549668320⟩, ⟨.privateRow 12 11, 1374213205609775247262392000⟩, ⟨.privateRow 12 12, 981853522500158862180927300⟩, ⟨.privateRow 12 13, 2273698212917991772743230400⟩, ⟨.privateRow 12 14, 4470446435296752191272871880⟩, ⟨.privateRow 12 15, 8299084406788346387435419200⟩, ⟨.privateRow 12 16, 15232907988969071156038032750⟩, ⟨.privateRow 12 17, 26627016826791311814812728800⟩, ⟨.privateRow 12 18, 44052258403003517469980377200⟩, ⟨.privateRow 12 19, 58086029039402900022856649280⟩, ⟨.privateRow 12 23, 535687939163913388172127007200⟩, ⟨.privateRow 13 5, 11342712173287033786927680⟩, ⟨.privateRow 13 6, 42034756877475478151555520⟩, ⟨.privateRow 13 7, 146746338741900999618376860⟩, ⟨.privateRow 13 8, 183751937207249947348228416⟩, ⟨.privateRow 13 9, 546880765497767700441156000⟩, ⟨.privateRow 13 11, 7324556385900102067908549360⟩, ⟨.privateRow 13 12, 2366502221608522049181729600⟩, ⟨.privateRow 13 13, 9024261805067164080879662208⟩, ⟨.privateRow 13 14, 16015909588681291707141884160⟩, ⟨.privateRow 13 16, 102857334374820149098972620480⟩, ⟨.privateRow 13 17, 46618547032209708864272764800⟩, ⟨.privateRow 13 19, 195517165408991923143719152080⟩, ⟨.privateRow 14 3, 17461806898349775698296560⟩, ⟨.privateRow 14 4, 73727629126365719615029920⟩, ⟨.privateRow 14 5, 234193645460220521130095040⟩, ⟨.privateRow 14 6, 435453809527597531476270465⟩, ⟨.privateRow 14 7, 685666950875201192419778256⟩, ⟨.privateRow 14 8, 1042719326215743748841137440⟩, ⟨.privateRow 14 9, 663548662137291476535269280⟩, ⟨.privateRow 14 10, 21648275102229134421963160260⟩, ⟨.privateRow 14 12, 36296111818909843766479229616⟩, ⟨.privateRow 14 13, 34099028470944145321951338000⟩, ⟨.privateRow 14 14, 12192706666772730881335573020⟩, ⟨.privateRow 14 15, 180153461770274635879325609520⟩, ⟨.privateRow 14 21, 3461733370370249633084499833760⟩, ⟨.privateRow 15 1, 77414010582684005595781416⟩, ⟨.privateRow 15 2, 162976864384597906517434560⟩, ⟨.privateRow 15 3, 516093403884560037305209440⟩, ⟨.privateRow 15 4, 1092903678814362431940443520⟩, ⟨.privateRow 15 5, 1935350264567100139894535400⟩, ⟨.privateRow 15 7, 9842638488369823568606494320⟩, ⟨.privateRow 15 10, 6756131832670604124722741760⟩, ⟨.privateRow 15 11, 2167592296315152156681879648⟩, ⟨.privateRow 15 13, 1161210158740260083936721240⟩, ⟨.privateRow 15 16, 1954548939191605773282289191168⟩, ⟨.privateRow 16 1, 3666979448653452896642277600⟩, ⟨.privateRow 16 3, 13661295985179530399255544000⟩, ⟨.privateRow 16 4, 8709076190551950629525409300⟩, ⟨.privateRow 16 7, 102722437119330699732863802000⟩, ⟨.privateRow 16 10, 17418152381103901259050818600⟩, ⟨.privateRow 16 15, 4891017188613975473541469862880⟩, ⟨.privateRow 16 17, 11132134721789960004673367620800⟩, ⟨.privateRow 17 0, 68450283041531120737322515200⟩, ⟨.privateRow 17 3, 394811453971688428538485221600⟩, ⟨.privateRow 17 6, 1271971743112407968866070035200⟩, ⟨.privateRow 17 8, 439148569123589268106978214400⟩, ⟨.privateRow 17 10, 144506153087676810445458643200⟩, ⟨.privateRow 17 11, 69672609524415605036203274400⟩, ⟨.privateRow 17 12, 79625839456474977184232313600⟩, ⟨.privateRow 17 17, 339073366352155944509522602080000⟩, ⟨.hall 15 6, 36250368732603578471708790⟩, ⟨.hall 14 8, 2115199266989646032299104⟩, ⟨.hall 16 9, 364033061953256533274236800⟩, ⟨.hall 15 14, 71302378168261584101377620⟩, ⟨.hall 7 15, 18534759124129954506801⟩, ⟨.hall 9 15, 22893323496212726260011⟩, ⟨.hall 10 15, 60324195555869566705020⟩, ⟨.hall 14 20, 34946896205897351097524182080⟩, ⟨.hall 12 21, 391390819260062470197148800⟩, ⟨.hall 4 26, 58950861125500069428084096⟩, ⟨.hall 5 29, 2153470619659409799617154686400⟩, ⟨.hall 3 31, 5805034734812402692110161568915⟩]
  caps := #[0, 0, 0, 0, 412822282528798864163112528, 1302294352139594144334432, 34017970356034250220835200, 8980650740075455042618320, 0, 78115909008549614680801408, 28416536695220704364553156, 52227545770422912457664280, 437718143132891995773486780, 892808583263646537380277528, 538026936714959935613931990, 1590521450632300248504135408, 10495415738300935133025502740, 0] }

theorem case_52_35_22_checked :
    (Witness.linear .conditional case_52_35_22).check 52 35 22 = true := by
  change case_52_35_22.check 52 35 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_36_1_checked :
    (Witness.rising).check 52 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_36_2_checked :
    (Witness.rising).check 52 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_36_3_checked :
    (Witness.rising).check 52 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_36_4_checked :
    (Witness.rising).check 52 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_36_5_checked :
    (Witness.rising).check 52 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_36_6_checked :
    (Witness.rising).check 52 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_36_7_checked :
    (Witness.rising).check 52 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_36_8_checked :
    (Witness.rising).check 52 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_36_9_checked :
    (Witness.rising).check 52 36 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_36_10_checked :
    (Witness.linear .positive case_52_36_10).check 52 36 10 = true := by
  change case_52_36_10.check 52 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_52_36_11_checked :
    (Witness.linear .positive case_52_36_11).check 52 36 11 = true := by
  change case_52_36_11.check 52 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_52_36_12_checked :
    (Witness.linear .positive case_52_36_12).check 52 36 12 = true := by
  change case_52_36_12.check 52 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_52_36_13_checked :
    (Witness.linear .positive case_52_36_13).check 52 36 13 = true := by
  change case_52_36_13.check 52 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_52_36_14_checked :
    (Witness.linear .positive case_52_36_14).check 52 36 14 = true := by
  change case_52_36_14.check 52 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_52_36_15_checked :
    (Witness.linear .positive case_52_36_15).check 52 36 15 = true := by
  change case_52_36_15.check 52 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_52_36_16_checked :
    (Witness.linear .positive case_52_36_16).check 52 36 16 = true := by
  change case_52_36_16.check 52 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_17 : Certificate := {
  objectiveScale := 2
  eta := 17206875
  rows := #[⟨.assumptionRow 17, 5⟩]
  caps := #[0, 0, 4828850, 1366936, 390830, 113050, 33592, 10166, 3146, 1001, 330, 114, 24794, 14168, 5005, 1295, 245] }

theorem case_52_36_17_checked :
    (Witness.linear .conditional case_52_36_17).check 52 36 17 = true := by
  change case_52_36_17.check 52 36 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_18 : Certificate := {
  objectiveScale := 1905825430080000
  eta := 952908660871662721426200
  rows := #[⟨.count 2, 108649991835650121816960⟩, ⟨.count 3, 12330105882550414358400⟩, ⟨.count 4, 1297171772711751736800⟩, ⟨.count 5, 122045731303525029000⟩, ⟨.count 6, 10144060783669612800⟩, ⟨.count 7, 2219013296427727800⟩, ⟨.count 8, 788982505396525440⟩, ⟨.count 9, 443802659285545560⟩, ⟨.path 6, 5056434808122297600⟩, ⟨.privateRow 2 33, 3141457123752734246460⟩, ⟨.privateRow 2 34, 10217668624731115427880⟩, ⟨.privateRow 3 30, 1210344952441529644740⟩, ⟨.privateRow 3 31, 2340100977546128476680⟩, ⟨.privateRow 3 32, 3266873641920832823880⟩, ⟨.privateRow 3 33, 5080124507001776111880⟩, ⟨.privateRow 4 26, 44733496616557337160⟩, ⟨.privateRow 4 27, 210732296050753216740⟩, ⟨.privateRow 4 28, 578845468468147280400⟩, ⟨.privateRow 4 29, 835315855250269162770⟩, ⟨.privateRow 4 30, 1154436384101533893360⟩, ⟨.privateRow 4 31, 1693297346314050116640⟩, ⟨.privateRow 5 23, 11985019962928172160⟩, ⟨.privateRow 5 24, 40071681777990717855⟩, ⟨.privateRow 5 25, 119289324310819565760⟩, ⟨.privateRow 5 26, 217396380426691726260⟩, ⟨.privateRow 5 27, 314854739957131998624⟩, ⟨.privateRow 5 28, 423789272697764053080⟩, ⟨.privateRow 5 29, 634405334718704388840⟩, ⟨.privateRow 5 30, 561526598026028014380⟩, ⟨.privateRow 6 20, 1546585024782961800⟩, ⟨.privateRow 6 21, 7555211937837263700⟩, ⟨.privateRow 6 22, 24761370593471311800⟩, ⟨.privateRow 6 23, 53190277051871784825⟩, ⟨.privateRow 6 24, 87432142944961900800⟩, ⟨.privateRow 6 25, 127399541161572880200⟩, ⟨.privateRow 6 26, 168919745508065031480⟩, ⟨.privateRow 6 27, 249586162198204431600⟩, ⟨.privateRow 6 28, 221689995043112996400⟩, ⟨.privateRow 7 18, 961572428452015380⟩, ⟨.privateRow 7 19, 5095085075434055520⟩, ⟨.privateRow 7 20, 13104858524903181036⟩, ⟨.privateRow 7 21, 24923393786543812560⟩, ⟨.privateRow 7 22, 39641087531183908770⟩, ⟨.privateRow 7 23, 57005998725371913360⟩, ⟨.privateRow 7 24, 75372484968661820940⟩, ⟨.privateRow 7 25, 110633662921896714600⟩, ⟨.privateRow 7 26, 16182946968947929170⟩, ⟨.privateRow 8 16, 663807396367269000⟩, ⟨.privateRow 8 17, 3246334266996120300⟩, ⟨.privateRow 8 18, 7419125263813918200⟩, ⟨.privateRow 8 19, 13309148637907638516⟩, ⟨.privateRow 8 20, 20776539308775169920⟩, ⟨.privateRow 8 21, 29537532545782421160⟩, ⟨.privateRow 8 22, 38913744284021486880⟩, ⟨.privateRow 8 23, 6796755541280484780⟩, ⟨.privateRow 9 14, 489591822545165340⟩, ⟨.privateRow 9 15, 2245565592282418560⟩, ⟨.privateRow 9 16, 4861282832729633310⟩, ⟨.privateRow 9 17, 8463630512435454720⟩, ⟨.privateRow 9 18, 13037935901677582896⟩, ⟨.privateRow 9 19, 12075815568707931040⟩, ⟨.privateRow 10 12, 414215815333175856⟩, ⟨.privateRow 10 13, 1788796432834596900⟩, ⟨.privateRow 10 14, 3857669269174357560⟩, ⟨.privateRow 10 15, 6641189794308699630⟩, ⟨.privateRow 10 16, 916423673070152520⟩, ⟨.privateRow 11 10, 409460786840830725⟩, ⟨.privateRow 11 11, 1711810257244247160⟩, ⟨.privateRow 11 12, 2279394610616237400⟩, ⟨.privateRow 12 8, 478610710994215800⟩, ⟨.privateRow 12 9, 871755223596607350⟩, ⟨.privateRow 13 6, 387446766042936600⟩, ⟨.privateRow 14 4, 159057093428152920⟩, ⟨.hall 4 31, 111584668620365740800⟩, ⟨.hall 3 32, 653319781388255021040⟩, ⟨.assumptionRow 18, 1959679343402352⟩]
  caps := #[0, 85013089469618567400, 13776930469841518980, 351093502034383680, 4199711994381914010, 1796367602797603836, 300506094105230520, 338969365290926136, 78675025625507052, 98149164748863368, 537153253097292594, 25852808857487040, 363139434973095066, 2723022417078715752, 0, 6676776512411765760, 1477388670197600160] }

theorem case_52_36_18_checked :
    (Witness.linear .conditional case_52_36_18).check 52 36 18 = true := by
  change case_52_36_18.check 52 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_19 : Certificate := {
  objectiveScale := 2371761392000000
  eta := 1716007930982479980846000
  rows := #[⟨.count 2, 166655554549289670664800⟩, ⟨.count 3, 15144702391060410168000⟩, ⟨.count 4, 1148908457252858702400⟩, ⟨.count 5, 73647978029029404000⟩, ⟨.count 7, 1704250731250267200⟩, ⟨.count 8, 378722384722281600⟩, ⟨.path 5, 48671779072160244000⟩, ⟨.privateRow 2 33, 2792485833600698235000⟩, ⟨.privateRow 2 34, 14439690383200701418800⟩, ⟨.privateRow 3 30, 1541307115948437337500⟩, ⟨.privateRow 3 31, 3031841762195043798000⟩, ⟨.privateRow 3 32, 4610140248926243631600⟩, ⟨.privateRow 3 33, 7511424231888008031600⟩, ⟨.privateRow 4 26, 65613653153135287200⟩, ⟨.privateRow 4 27, 241922449040811739200⟩, ⟨.privateRow 4 28, 721348468440693453360⟩, ⟨.privateRow 4 29, 1101706798606980766200⟩, ⟨.privateRow 4 30, 1622487273548617476000⟩, ⟨.privateRow 4 31, 2540855242001514438000⟩, ⟨.privateRow 5 23, 15126352389800652000⟩, ⟨.privateRow 5 24, 43156599246556245450⟩, ⟨.privateRow 5 25, 133809767873522254800⟩, ⟨.privateRow 5 26, 267066910226480364000⟩, ⟨.privateRow 5 27, 414392623043338779840⟩, ⟨.privateRow 5 28, 599952051322843319100⟩, ⟨.privateRow 5 29, 969921553073217544800⟩, ⟨.privateRow 5 30, 970479492300710191800⟩, ⟨.privateRow 6 0, 32723708357340000⟩, ⟨.privateRow 6 20, 1466319622666626000⟩, ⟨.privateRow 6 21, 7445952599629143600⟩, ⟨.privateRow 6 22, 25214344482849522000⟩, ⟨.privateRow 6 23, 58685062382635689000⟩, ⟨.privateRow 6 24, 105573695383998270000⟩, ⟨.privateRow 6 25, 166401147787352478000⟩, ⟨.privateRow 6 26, 239183474651302381200⟩, ⟨.privateRow 6 27, 386017862802980908500⟩, ⟨.privateRow 6 28, 425927424818023128000⟩, ⟨.privateRow 6 29, 167990429223240624000⟩, ⟨.privateRow 7 18, 644166199014237900⟩, ⟨.privateRow 7 19, 4636889976583519200⟩, ⟨.privateRow 7 20, 12921872508729704520⟩, ⟨.privateRow 7 21, 26950155412826646000⟩, ⟨.privateRow 7 22, 46790812487451532500⟩, ⟨.privateRow 7 23, 73239305659801023600⟩, ⟨.privateRow 7 24, 105420080947337956800⟩, ⟨.privateRow 7 25, 170181608734848110400⟩, ⟨.privateRow 7 26, 165631867943385343500⟩, ⟨.privateRow 8 16, 345948332198238000⟩, ⟨.privateRow 8 17, 2820692761212826500⟩, ⟨.privateRow 8 18, 7113955703931039600⟩, ⟨.privateRow 8 19, 13989058085679276600⟩, ⟨.privateRow 8 20, 23806909906292312800⟩, ⟨.privateRow 8 21, 36848504526025742550⟩, ⟨.privateRow 8 22, 52885875866575752000⟩, ⟨.privateRow 8 23, 85764840040233354000⟩, ⟨.privateRow 8 24, 4383711603160409520⟩, ⟨.privateRow 9 14, 216412791269875200⟩, ⟨.privateRow 9 15, 1871762555262045600⟩, ⟨.privateRow 9 16, 4520998467622236600⟩, ⟨.privateRow 9 17, 8598719598580893600⟩, ⟨.privateRow 9 18, 14386716589637672280⟩, ⟨.privateRow 9 19, 22060578910072903200⟩, ⟨.privateRow 9 20, 31457628080994515400⟩, ⟨.privateRow 10 12, 162309593452406400⟩, ⟨.privateRow 10 13, 1412962978715145000⟩, ⟨.privateRow 10 14, 3464685552541752000⟩, ⟨.privateRow 10 15, 6492383738096256000⟩, ⟨.privateRow 10 16, 10734566294238696000⟩, ⟨.privateRow 10 17, 7364797802902940400⟩, ⟨.privateRow 11 10, 152165243861631000⟩, ⟨.privateRow 11 11, 1257899349256149600⟩, ⟨.privateRow 11 12, 3275175725021772000⟩, ⟨.privateRow 11 13, 5509162162374948000⟩, ⟨.privateRow 12 8, 183791745526989600⟩, ⟨.privateRow 12 9, 1380899588044301325⟩, ⟨.privateRow 12 10, 1889554183775097840⟩, ⟨.privateRow 13 6, 260371639496568600⟩, ⟨.privateRow 13 7, 827062854871453200⟩, ⟨.privateRow 14 4, 305398313995975200⟩, ⟨.hall 4 31, 272246446055037103650⟩, ⟨.hall 3 32, 1086662728163860848000⟩, ⟨.assumptionRow 19, 1868085333395424⟩]
  caps := #[0, 0, 0, 0, 364870531213960200, 420172192565950110, 404235780456787500, 72331726763331112, 541711144685550910, 303278160117499200, 44037134140839840, 958755146557978000, 1868085333395424, 3062366834873394048, 1711379847538705344, 25372043407732301280, 7012694890634347200] }

theorem case_52_36_19_checked :
    (Witness.linear .conditional case_52_36_19).check 52 36 19 = true := by
  change case_52_36_19.check 52 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_20 : Certificate := {
  objectiveScale := 82989596289600000
  eta := 69354365530098357153244800
  rows := #[⟨.count 2, 6805042368757273000039680⟩, ⟨.count 3, 622276111235549294203680⟩, ⟨.count 4, 46729499514945552264960⟩, ⟨.count 5, 2465436256876185793200⟩, ⟨.count 6, 45975501293728406400⟩, ⟨.path 5, 1814580227885254830000⟩, ⟨.path 6, 31655606516556422400⟩, ⟨.privateRow 2 33, 145926432670882685781960⟩, ⟨.privateRow 2 34, 641999601290558780549280⟩, ⟨.privateRow 3 30, 64690308006812363896020⟩, ⟨.privateRow 3 31, 132384795748855339369680⟩, ⟨.privateRow 3 32, 204521634375973368133680⟩, ⟨.privateRow 3 33, 342421702343914693500000⟩, ⟨.privateRow 4 26, 2758037482966985865360⟩, ⟨.privateRow 4 27, 9783778239894128750280⟩, ⟨.privateRow 4 28, 29977176231043264182960⟩, ⟨.privateRow 4 29, 47279481449171778326520⟩, ⟨.privateRow 4 30, 71864306072226872043840⟩, ⟨.privateRow 4 31, 116330661535988643503760⟩, ⟨.privateRow 5 23, 718792906800559390800⟩, ⟨.privateRow 5 24, 1722644564099386227300⟩, ⟨.privateRow 5 25, 5336661045409160163840⟩, ⟨.privateRow 5 26, 10952577650561357570760⟩, ⟨.privateRow 5 27, 17531991160008432307200⟩, ⟨.privateRow 5 28, 26372792711909319055380⟩, ⟨.privateRow 5 29, 44598407320255424716080⟩, ⟨.privateRow 5 30, 47616635125325786640120⟩, ⟨.privateRow 6 19, 4150566089017147800⟩, ⟨.privateRow 6 20, 105012224545902382800⟩, ⟨.privateRow 6 21, 327575446717814895600⟩, ⟨.privateRow 6 22, 984216286954630329600⟩, ⟨.privateRow 6 23, 2300211799101849332700⟩, ⟨.privateRow 6 24, 4251912878575346727600⟩, ⟨.privateRow 6 25, 6930168271400477703600⟩, ⟨.privateRow 6 26, 10386248871430694742480⟩, ⟨.privateRow 6 27, 17661776168868853121100⟩, ⟨.privateRow 6 28, 21043370071316939346000⟩, ⟨.privateRow 6 29, 13592465392902079483800⟩, ⟨.privateRow 7 17, 12731677281340174080⟩, ⟨.privateRow 7 18, 51051962894910917940⟩, ⟨.privateRow 7 19, 198321594217037534880⟩, ⟨.privateRow 7 20, 494696393920517652864⟩, ⟨.privateRow 7 21, 1037258393076839213280⟩, ⟨.privateRow 7 22, 1846347397267824220770⟩, ⟨.privateRow 7 23, 2992348341346094565120⟩, ⟨.privateRow 7 24, 4498319672413876829520⟩, ⟨.privateRow 7 25, 7679287981091455720992⟩, ⟨.privateRow 7 26, 9778127084526774633660⟩, ⟨.privateRow 7 27, 2203375899501933876720⟩, ⟨.privateRow 8 14, 1013163824806237104⟩, ⟨.privateRow 8 15, 7024034919875173200⟩, ⟨.privateRow 8 16, 35758723228455427200⟩, ⟨.privateRow 8 17, 118897754734614295440⟩, ⟨.privateRow 8 18, 270222169851396126000⟩, ⟨.privateRow 8 19, 529497294205353738264⟩, ⟨.privateRow 8 20, 920191144412252993280⟩, ⟨.privateRow 8 21, 1472141936911474368540⟩, ⟨.privateRow 8 22, 2204525287034277086880⟩, ⟨.privateRow 8 23, 3779548050567620090760⟩, ⟨.privateRow 8 24, 2808668915979031529424⟩, ⟨.privateRow 9 11, 105172715377810080⟩, ⟨.privateRow 9 12, 670476060533539260⟩, ⟨.privateRow 9 13, 6019385076789996912⟩, ⟨.privateRow 9 14, 27010607010065438760⟩, ⟨.privateRow 9 15, 80800961141221398000⟩, ⟨.privateRow 9 16, 172684834257416000520⟩, ⟨.privateRow 9 17, 321991048707137278560⟩, ⟨.privateRow 9 18, 545946306890443234776⟩, ⟨.privateRow 9 19, 860692602151572990800⟩, ⟨.privateRow 9 20, 1278262609407192599190⟩, ⟨.privateRow 9 21, 1328181148485487296000⟩, ⟨.privateRow 10 9, 63854862907956120⟩, ⟨.privateRow 10 10, 743721344457371280⟩, ⟨.privateRow 10 11, 5962447824030402705⟩, ⟨.privateRow 10 12, 23983886508228318672⟩, ⟨.privateRow 10 13, 65843485781375324880⟩, ⟨.privateRow 10 14, 135450899965369074240⟩, ⟨.privateRow 10 15, 243287027679312817200⟩, ⟨.privateRow 10 16, 402285636320123556000⟩, ⟨.privateRow 10 17, 624117430062363116880⟩, ⟨.privateRow 10 18, 192586266530395657920⟩, ⟨.privateRow 11 7, 100823467749404400⟩, ⟨.privateRow 11 8, 957822943619341800⟩, ⟨.privateRow 11 9, 6986473235811669600⟩, ⟨.privateRow 11 10, 25861219477722228600⟩, ⟨.privateRow 11 11, 66919896327538013760⟩, ⟨.privateRow 11 12, 134642539503061761600⟩, ⟨.privateRow 11 13, 236508588386006706000⟩, ⟨.privateRow 11 14, 136968680937565877400⟩, ⟨.privateRow 12 5, 210721047596255196⟩, ⟨.privateRow 12 6, 1552681403340827760⟩, ⟨.privateRow 12 7, 10301917882483587360⟩, ⟨.privateRow 12 8, 35202810304315573920⟩, ⟨.privateRow 12 9, 87449234752445906340⟩, ⟨.privateRow 12 10, 79512075292986960624⟩, ⟨.privateRow 13 3, 602060135989300560⟩, ⟨.privateRow 13 4, 3160815713943827940⟩, ⟨.privateRow 13 5, 19297611727236002160⟩, ⟨.privateRow 13 6, 49870647931113729720⟩, ⟨.privateRow 14 1, 2490339653410288680⟩, ⟨.privateRow 14 2, 7826781767860907280⟩, ⟨.privateRow 14 3, 13696868093756587740⟩, ⟨.hall 4 31, 15315732541914818283270⟩, ⟨.hall 3 32, 52610915517945758653680⟩, ⟨.assumptionRow 20, 36523299792595616⟩]
  caps := #[0, 309308526037530539520, 222219146773764580440, 0, 9176096684846937560, 24401532804272502450, 14421704230857183000, 1835457527254084272, 1145221494819216696, 6453560183341183024, 30247040324821320, 4600889328618189200, 55488761059863139008, 10474559445979611840, 0, 2289971479940940571776, 749267281119279642720] }

theorem case_52_36_20_checked :
    (Witness.linear .conditional case_52_36_20).check 52 36 20 = true := by
  change case_52_36_20.check 52 36 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_21 : Certificate := {
  objectiveScale := 5917280569200000
  eta := 4306652129653748403328800
  rows := #[⟨.count 2, 501025390700065709718240⟩, ⟨.count 3, 55975054205048719300560⟩, ⟨.count 4, 5568074964156250465920⟩, ⟨.count 5, 450988035673978202400⟩, ⟨.count 6, 24092144361215330400⟩, ⟨.path 6, 23589764400698496000⟩, ⟨.privateRow 2 34, 142666578064568617899840⟩, ⟨.privateRow 3 30, 6619876699933010453940⟩, ⟨.privateRow 3 32, 46957153236046161348240⟩, ⟨.privateRow 4 26, 121348327124647743120⟩, ⟨.privateRow 4 27, 948469683273108796800⟩, ⟨.privateRow 4 29, 10150020419380018697520⟩, ⟨.privateRow 4 30, 4159318522824132988320⟩, ⟨.privateRow 5 23, 36006719457590241360⟩, ⟨.privateRow 5 24, 139132133686018533060⟩, ⟨.privateRow 5 25, 517208222944516680720⟩, ⟨.privateRow 5 26, 602479721196766413000⟩, ⟨.privateRow 5 27, 2034467470620818369136⟩, ⟨.privateRow 5 28, 3832700899049937434520⟩, ⟨.privateRow 5 29, 4499651762116248497760⟩, ⟨.privateRow 6 20, 6858768370776613200⟩, ⟨.privateRow 6 22, 128632326326254951200⟩, ⟨.privateRow 6 23, 198997942404643732350⟩, ⟨.privateRow 6 24, 332399134607745348000⟩, ⟨.privateRow 6 25, 646155538459788357000⟩, ⟨.privateRow 6 26, 1194251822677437123600⟩, ⟨.privateRow 6 27, 2432778243983598911400⟩, ⟨.privateRow 6 28, 2665845084975063591600⟩, ⟨.privateRow 6 29, 1847698404825488014800⟩, ⟨.privateRow 7 15, 8453383986391344⟩, ⟨.privateRow 7 16, 54343182769658640⟩, ⟨.privateRow 7 17, 946128746169185040⟩, ⟨.privateRow 7 18, 3751189143961158900⟩, ⟨.privateRow 7 19, 3262237729293750480⟩, ⟨.privateRow 7 20, 60623443258405523496⟩, ⟨.privateRow 7 21, 95495061099600882720⟩, ⟨.privateRow 7 22, 157882796040832832970⟩, ⟨.privateRow 7 23, 269451614566224090000⟩, ⟨.privateRow 7 24, 451896774452515271880⟩, ⟨.privateRow 7 25, 913624834481203676832⟩, ⟨.privateRow 7 26, 1412687264885789452560⟩, ⟨.privateRow 8 13, 12327851646820710⟩, ⟨.privateRow 8 14, 138071938444391952⟩, ⟨.privateRow 8 15, 577647905736741840⟩, ⟨.privateRow 8 16, 2731093287911049600⟩, ⟨.privateRow 8 17, 2638160252419631940⟩, ⟨.privateRow 8 18, 29810986709584626000⟩, ⟨.privateRow 8 19, 51875599729821547680⟩, ⟨.privateRow 8 20, 82207593826176859040⟩, ⟨.privateRow 8 21, 131969651879215700550⟩, ⟨.privateRow 8 22, 209164897769943155040⟩, ⟨.privateRow 8 23, 399373081950403721160⟩, ⟨.privateRow 8 24, 644342287594707413712⟩, ⟨.privateRow 8 25, 417790892310753861900⟩, ⟨.privateRow 9 10, 5479045176364760⟩, ⟨.privateRow 9 11, 29006709757225200⟩, ⟨.privateRow 9 12, 104786738997976035⟩, ⟨.privateRow 9 13, 512838628507741536⟩, ⟨.privateRow 9 14, 2099257023287183760⟩, ⟨.privateRow 9 15, 2192461000573037040⟩, ⟨.privateRow 9 16, 16239889902745148640⟩, ⟨.privateRow 9 17, 32518631216740883760⟩, ⟨.privateRow 9 19, 179745556055822316560⟩, ⟨.privateRow 9 20, 66286858304954957670⟩, ⟨.privateRow 9 21, 213011187483751216560⟩, ⟨.privateRow 9 22, 339278914456035033480⟩, ⟨.privateRow 10 8, 6673724199782640⟩, ⟨.privateRow 10 9, 28177946621304480⟩, ⟨.privateRow 10 10, 119341891572583680⟩, ⟨.privateRow 10 11, 515128086670722525⟩, ⟨.privateRow 10 12, 1876651244978878368⟩, ⟨.privateRow 10 13, 2209956099299451360⟩, ⟨.privateRow 10 14, 10397662303261353120⟩, ⟨.privateRow 10 15, 23754009001759676640⟩, ⟨.privateRow 10 16, 24610874742198435600⟩, ⟨.privateRow 10 17, 28758412321703352288⟩, ⟨.privateRow 10 18, 185734935154328479920⟩, ⟨.privateRow 10 19, 85907514761702033400⟩, ⟨.privateRow 10 20, 227553020650817278560⟩, ⟨.privateRow 10 22, 120663603021750044256⟩, ⟨.privateRow 11 6, 10566729982989180⟩, ⟨.privateRow 11 7, 44491494665217600⟩, ⟨.privateRow 11 8, 152630544198732600⟩, ⟨.privateRow 11 9, 621572351940540000⟩, ⟨.privateRow 11 10, 2047303934204153625⟩, ⟨.privateRow 11 11, 2789616715509143520⟩, ⟨.privateRow 11 13, 37585045724109206400⟩, ⟨.privateRow 11 14, 23933643411470492700⟩, ⟨.privateRow 11 15, 34485964217210142000⟩, ⟨.privateRow 11 16, 40322641615086710880⟩, ⟨.privateRow 11 17, 281990800812704583600⟩, ⟨.privateRow 11 19, 311537390555615281200⟩, ⟨.privateRow 12 4, 22139815202453520⟩, ⟨.privateRow 12 5, 69740417887728588⟩, ⟨.privateRow 12 6, 269173542724566480⟩, ⟨.privateRow 12 7, 929872238503047840⟩, ⟨.privateRow 12 8, 2844315082479911040⟩, ⟨.privateRow 12 9, 4445951640342697485⟩, ⟨.privateRow 12 10, 2789616715509143520⟩, ⟨.privateRow 12 11, 22582611506502590400⟩, ⟨.privateRow 12 12, 62301439979704205280⟩, ⟨.privateRow 12 13, 45524995010045050500⟩, ⟨.privateRow 12 14, 62766376098955729200⟩, ⟨.privateRow 12 15, 81828756988268209920⟩, ⟨.privateRow 12 17, 685315839776746258080⟩, ⟨.privateRow 13 1, 60643841641503120⟩, ⟨.privateRow 13 2, 63400379897935080⟩, ⟨.privateRow 13 3, 199258336822081680⟩, ⟨.privateRow 13 4, 557923343101828704⟩, ⟨.privateRow 13 5, 1835274154940226000⟩, ⟨.privateRow 13 6, 5191786664975350440⟩, ⟨.privateRow 13 7, 9107278100632792080⟩, ⟨.privateRow 13 9, 40728404046433495392⟩, ⟨.privateRow 13 10, 66950801172219444480⟩, ⟨.privateRow 13 11, 151712232143458805280⟩, ⟨.privateRow 13 12, 114025583246436241380⟩, ⟨.privateRow 13 13, 172956236361566898240⟩, ⟨.privateRow 13 14, 204618386082595677192⟩, ⟨.privateRow 13 16, 1403351558945818512030⟩, ⟨.privateRow 14 2, 3741628769214644880⟩, ⟨.privateRow 14 3, 3626501730161886576⟩, ⟨.privateRow 14 4, 13360795847964845280⟩, ⟨.privateRow 14 5, 25519826990028090720⟩, ⟨.privateRow 14 6, 21332363118599332800⟩, ⟨.privateRow 14 7, 40798144464321223980⟩, ⟨.privateRow 14 8, 55606359862482260832⟩, ⟨.privateRow 14 11, 503680795855817580⟩, ⟨.privateRow 14 12, 49452296320389362400⟩, ⟨.privateRow 14 14, 8504146557229624020720⟩, ⟨.privateRow 15 2, 141735775953827067012⟩, ⟨.privateRow 15 5, 617216372898140695680⟩, ⟨.privateRow 15 7, 307446757790391050832⟩, ⟨.privateRow 15 11, 257701410825140121840⟩, ⟨.privateRow 15 13, 38129979395074339652880⟩, ⟨.privateRow 16 0, 846183737037773534400⟩, ⟨.privateRow 16 3, 5253390700776177359400⟩, ⟨.privateRow 16 6, 11085006955194833300640⟩, ⟨.privateRow 16 12, 341505653206161435591600⟩, ⟨.hall 15 7, 2723462879139892890⟩, ⟨.hall 14 8, 26991506763565344⟩, ⟨.hall 14 10, 224224047378971640⟩, ⟨.hall 15 10, 7105389841038188700⟩, ⟨.hall 12 12, 1952309568716100⟩, ⟨.hall 11 15, 697242029568084⟩, ⟨.hall 8 17, 68627565628468⟩, ⟨.hall 13 18, 313084713546324720⟩, ⟨.hall 2 31, 33961418367631229475⟩]
  caps := #[0, 198666661178826640800, 0, 11956277840579527455, 1914281474447422080, 0, 0, 1118504730768808932, 1013618607012863432, 0, 13347448399565280, 1284846602452228650, 13087415638755254511, 0, 75330119948631102984, 0, 0] }

theorem case_52_36_21_checked :
    (Witness.linear .conditional case_52_36_21).check 52 36 21 = true := by
  change case_52_36_21.check 52 36 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_22 : Certificate := {
  objectiveScale := 3944853712800000
  eta := 1929933558248901988582800
  rows := #[⟨.count 2, 234223658412055714321920⟩, ⟨.count 3, 26419065104229343706160⟩, ⟨.count 4, 2638977412871649769920⟩, ⟨.count 5, 211545934259443383600⟩, ⟨.count 6, 11412068381628314400⟩, ⟨.path 6, 10811782812249619200⟩, ⟨.privateRow 2 34, 116519500590101415686880⟩, ⟨.privateRow 3 30, 3791205350406738924660⟩, ⟨.privateRow 3 33, 104811944171228791857360⟩, ⟨.privateRow 4 26, 4184425073263715280⟩, ⟨.privateRow 4 27, 452382844031732774160⟩, ⟨.privateRow 4 28, 1698597618073517489328⟩, ⟨.privateRow 5 23, 1756425339394645920⟩, ⟨.privateRow 5 24, 47191016104029677880⟩, ⟨.privateRow 5 26, 1078651796663535494400⟩, ⟨.privateRow 5 27, 619480885290730471008⟩, ⟨.privateRow 6 20, 499518144650397600⟩, ⟨.privateRow 6 21, 4290092373093607080⟩, ⟨.privateRow 6 22, 29328546108341079600⟩, ⟨.privateRow 6 23, 34394706094629780900⟩, ⟨.privateRow 6 24, 284033701942749158400⟩, ⟨.privateRow 6 25, 457574630696708124600⟩, ⟨.privateRow 6 26, 608516846260380897840⟩, ⟨.privateRow 6 27, 865890688456048355100⟩, ⟨.privateRow 6 28, 1558592672490904050000⟩, ⟨.privateRow 6 30, 8512135005096763840800⟩, ⟨.privateRow 7 16, 9057197128276440⟩, ⟨.privateRow 7 17, 87785141397140880⟩, ⟨.privateRow 7 18, 412102469336578020⟩, ⟨.privateRow 7 19, 3031690893301259280⟩, ⟨.privateRow 7 20, 14784968592198460656⟩, ⟨.privateRow 7 21, 22429645510558366080⟩, ⟨.privateRow 7 22, 88158228248078728740⟩, ⟨.privateRow 7 23, 189838851808674182400⟩, ⟨.privateRow 7 24, 311972136017772550320⟩, ⟨.privateRow 7 25, 562158488479010767344⟩, ⟨.privateRow 7 26, 815233784917598226180⟩, ⟨.privateRow 8 14, 13149708423275424⟩, ⟨.privateRow 8 15, 56355893242608960⟩, ⟨.privateRow 8 16, 318627550256289120⟩, ⟨.privateRow 8 17, 1882052018081295060⟩, ⟨.privateRow 8 18, 7656716586461735520⟩, ⟨.privateRow 8 19, 13176007840121974848⟩, ⟨.privateRow 8 20, 33860499189934216800⟩, ⟨.privateRow 8 21, 77258646270625389570⟩, ⟨.privateRow 8 22, 143693438795342195760⟩, ⟨.privateRow 8 23, 285825349715420434920⟩, ⟨.privateRow 8 24, 455203456488525352608⟩, ⟨.privateRow 8 25, 656162231753679110460⟩, ⟨.privateRow 8 26, 487525439792936344800⟩, ⟨.privateRow 9 12, 12327851646820710⟩, ⟨.privateRow 9 13, 46023979481463984⟩, ⟨.privateRow 9 14, 239512546281088080⟩, ⟨.privateRow 9 15, 1221405609315774960⟩, ⟨.privateRow 9 16, 4364059482974531340⟩, ⟨.privateRow 9 17, 8078104970025788880⟩, ⟨.privateRow 9 19, 65069140514507889760⟩, ⟨.privateRow 9 20, 47412917433672450660⟩, ⟨.privateRow 9 21, 136127660127521942880⟩, ⟨.privateRow 9 22, 230645885744250936960⟩, ⟨.privateRow 9 23, 337211122806474973056⟩, ⟨.privateRow 9 24, 436455259704040416840⟩, ⟨.privateRow 10 10, 7458868223286480⟩, ⟨.privateRow 10 11, 47550284923451310⟩, ⟨.privateRow 10 12, 211334599659783600⟩, ⟨.privateRow 10 13, 951005698469026200⟩, ⟨.privateRow 10 14, 3062726044300248480⟩, ⟨.privateRow 10 15, 6149836850099702760⟩, ⟨.privateRow 10 16, 6432256724190504480⟩, ⟨.privateRow 10 17, 11183827013995748112⟩, ⟨.privateRow 10 18, 69839040700903153680⟩, ⟨.privateRow 10 19, 64937839110460005690⟩, ⟨.privateRow 10 20, 158138661859706642400⟩, ⟨.privateRow 10 21, 258145213484425667400⟩, ⟨.privateRow 10 22, 376319294922183460848⟩, ⟨.privateRow 10 24, 1163016568847721107520⟩, ⟨.privateRow 11 8, 11740811092210200⟩, ⟨.privateRow 11 9, 62157235194054000⟩, ⟨.privateRow 11 10, 224543012138520075⟩, ⟨.privateRow 11 11, 901694291881743360⟩, ⟨.privateRow 11 12, 2671873152841549800⟩, ⟨.privateRow 11 13, 5657264667815745600⟩, ⟨.privateRow 11 14, 8418161553114713400⟩, ⟨.privateRow 11 15, 6109491153801016800⟩, ⟨.privateRow 11 16, 23331339802440109440⟩, ⟨.privateRow 11 17, 103460027344556282400⟩, ⟨.privateRow 11 18, 91243713403111569300⟩, ⟨.privateRow 11 19, 203152931587240549200⟩, ⟨.privateRow 11 20, 321897817715127053400⟩, ⟨.privateRow 11 21, 453693118549623432480⟩, ⟨.privateRow 11 24, 2166390981112441683600⟩, ⟨.privateRow 12 6, 24470322065869680⟩, ⟨.privateRow 12 7, 77489353208587320⟩, ⟨.privateRow 12 8, 300841018339221360⟩, ⟨.privateRow 12 9, 1075164775769149065⟩, ⟨.privateRow 12 10, 3037582645776622944⟩, ⟨.privateRow 12 11, 6608734837932375720⟩, ⟨.privateRow 12 13, 37466102276351969220⟩, ⟨.privateRow 12 15, 47469977775580592232⟩, ⟨.privateRow 12 16, 187834192177615663680⟩, ⟨.privateRow 12 20, 664021765515026462544⟩, ⟨.privateRow 13 4, 69740417887728588⟩, ⟨.privateRow 13 5, 146821932395218080⟩, ⟨.privateRow 13 6, 542425472460111240⟩, ⟨.privateRow 13 7, 1722998559579176880⟩, ⟨.privateRow 13 8, 4620302685062018955⟩, ⟨.privateRow 13 9, 10321581847383831024⟩, ⟨.privateRow 13 11, 35835845499232843680⟩, ⟨.privateRow 13 12, 80433948630513638160⟩, ⟨.privateRow 13 15, 309957412834349280⟩, ⟨.privateRow 13 16, 573091883992409671890⟩, ⟨.privateRow 13 18, 877566925087251399000⟩, ⟨.privateRow 13 20, 89965139075169878520⟩, ⟨.privateRow 14 2, 287817597631895760⟩, ⟨.privateRow 14 3, 302208477513490548⟩, ⟨.privateRow 14 4, 1272456747425223360⟩, ⟨.privateRow 14 5, 4029446366846540640⟩, ⟨.privateRow 14 6, 10310642173989677520⟩, ⟨.privateRow 14 7, 22665635813511791100⟩, ⟨.privateRow 14 8, 31026737024718362928⟩, ⟨.privateRow 14 9, 12088339100539621920⟩, ⟨.privateRow 14 10, 131576921748181269360⟩, ⟨.privateRow 14 11, 321852028551867433620⟩, ⟨.privateRow 14 15, 1524641769055559814660⟩, ⟨.privateRow 14 16, 752930835405039308160⟩, ⟨.privateRow 14 17, 1729639852968877569720⟩, ⟨.privateRow 14 18, 1700829311445924804144⟩, ⟨.privateRow 15 2, 12692756055566603016⟩, ⟨.privateRow 15 3, 11133996539970704400⟩, ⟨.privateRow 15 4, 37608166090567712640⟩, ⟨.privateRow 15 6, 304097280497949863925⟩, ⟨.privateRow 15 8, 262921375436736776760⟩, ⟨.privateRow 15 9, 758310810499235513520⟩, ⟨.privateRow 15 13, 8236188373834329068160⟩, ⟨.privateRow 15 15, 6515614775190856214880⟩, ⟨.privateRow 15 16, 7587447508772036025120⟩, ⟨.privateRow 15 18, 22582528482195581199300⟩, ⟨.privateRow 16 7, 1359938148810707466000⟩, ⟨.privateRow 16 11, 92212872743691370911240⟩, ⟨.privateRow 16 16, 436757735872046809780560⟩, ⟨.hall 12 9, 342433738511865⟩, ⟨.hall 13 10, 3164553059536440⟩, ⟨.hall 8 13, 80297623310905⟩, ⟨.hall 15 19, 1695389558850681974280⟩, ⟨.hall 12 20, 263052507899507040⟩, ⟨.hall 14 21, 138466429697090214720⟩, ⟨.hall 13 22, 119832231083610165120⟩, ⟨.hall 7 23, 2284631039057136⟩, ⟨.hall 3 32, 28275724096080406545600⟩]
  caps := #[0, 0, 0, 5074483686544752480, 0, 942110958389000400, 0, 1626120005565624840, 0, 1943148024333626180, 126481744802723310, 28425121591666800, 6176154339425359575, 13580841011103355374, 21929185387859256078, 525360370076456808894, 0] }

theorem case_52_36_22_checked :
    (Witness.linear .conditional case_52_36_22).check 52 36 22 = true := by
  change case_52_36_22.check 52 36 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440, 48450] }

theorem case_52_36_23_checked :
    (Witness.linear .negative case_52_36_23).check 52 36 23 = true := by
  change case_52_36_23.check 52 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_37_1_checked :
    (Witness.rising).check 52 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_37_2_checked :
    (Witness.rising).check 52 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_37_3_checked :
    (Witness.rising).check 52 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_37_4_checked :
    (Witness.rising).check 52 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_37_5_checked :
    (Witness.rising).check 52 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_37_6_checked :
    (Witness.rising).check 52 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_37_7_checked :
    (Witness.rising).check 52 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_37_8_checked :
    (Witness.rising).check 52 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_37_9_checked :
    (Witness.rising).check 52 37 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_52_37_10_checked :
    (Witness.linear .positive case_52_37_10).check 52 37 10 = true := by
  change case_52_37_10.check 52 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_52_37_11_checked :
    (Witness.linear .positive case_52_37_11).check 52 37 11 = true := by
  change case_52_37_11.check 52 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_52_37_12_checked :
    (Witness.linear .positive case_52_37_12).check 52 37 12 = true := by
  change case_52_37_12.check 52 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_52_37_13_checked :
    (Witness.linear .positive case_52_37_13).check 52 37 13 = true := by
  change case_52_37_13.check 52 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_52_37_14_checked :
    (Witness.linear .positive case_52_37_14).check 52 37 14 = true := by
  change case_52_37_14.check 52 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_52_37_15_checked :
    (Witness.linear .positive case_52_37_15).check 52 37 15 = true := by
  change case_52_37_15.check 52 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_52_37_16_checked :
    (Witness.linear .positive case_52_37_16).check 52 37 16 = true := by
  change case_52_37_16.check 52 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_52_37_17_checked :
    (Witness.linear .positive case_52_37_17).check 52 37 17 = true := by
  change case_52_37_17.check 52 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_18 : Certificate := {
  objectiveScale := 182
  eta := 2593846275
  rows := #[⟨.assumptionRow 18, 337⟩]
  caps := #[0, 0, 737417835, 211503630, 61274392, 17956862, 5332730, 1608438, 494104, 155155, 50039, 20523360, 13477310, 6017858, 2125200, 609917] }

theorem case_52_37_18_checked :
    (Witness.linear .conditional case_52_37_18).check 52 37 18 = true := by
  change case_52_37_18.check 52 37 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_19 : Certificate := {
  objectiveScale := 65819001179131200000
  eta := 58872494097326012516340127200
  rows := #[⟨.count 2, 5657439058437257742675024000⟩, ⟨.count 3, 492785981334467020572372000⟩, ⟨.count 4, 36550071342845028654285600⟩, ⟨.count 5, 2068628020818961650048000⟩, ⟨.count 6, 116360326171066592815200⟩, ⟨.count 7, 30167491970276524063200⟩, ⟨.path 4, 1305890945155581276492000⟩, ⟨.path 5, 1437699883942958103468000⟩, ⟨.privateRow 2 34, 463595700621941953913647800⟩, ⟨.privateRow 2 35, 727517081534333634556412400⟩, ⟨.privateRow 3 30, 36862951330993896603855360⟩, ⟨.privateRow 3 31, 87606396681683025879532800⟩, ⟨.privateRow 3 32, 185073253595936435624294400⟩, ⟨.privateRow 3 33, 225202482378969271883506800⟩, ⟨.privateRow 3 34, 340328096200109546963834400⟩, ⟨.privateRow 4 26, 968861326938255866565450⟩, ⟨.privateRow 4 27, 10067015203101562922845200⟩, ⟨.privateRow 4 28, 17623202362779039432205800⟩, ⟨.privateRow 4 29, 41684147512015089099498480⟩, ⟨.privateRow 4 30, 60736049972193599415061650⟩, ⟨.privateRow 4 31, 82391730212535226720036800⟩, ⟨.privateRow 4 32, 116743345578046353683216700⟩, ⟨.privateRow 5 23, 329687590818022012976400⟩, ⟨.privateRow 5 24, 1896242352417381512544000⟩, ⟨.privateRow 5 25, 3967563899305117852240500⟩, ⟨.privateRow 5 26, 9251569425251945450973600⟩, ⟨.privateRow 5 27, 15820694717555017119429600⟩, ⟨.privateRow 5 28, 22982457311298663932033280⟩, ⟨.privateRow 5 29, 30929221142526006295795800⟩, ⟨.privateRow 5 30, 46091618088872489265132000⟩, ⟨.privateRow 5 31, 37623172128644865010248000⟩, ⟨.privateRow 6 20, 48483469237944413673000⟩, ⟨.privateRow 6 21, 338502767043102815462400⟩, ⟨.privateRow 6 22, 833269224636137989659960⟩, ⟨.privateRow 6 23, 2238858868365522035833200⟩, ⟨.privateRow 6 24, 4144528562023614962146950⟩, ⟨.privateRow 6 25, 6627921118490039179640400⟩, ⟨.privateRow 6 26, 9640668505358369189911200⟩, ⟨.privateRow 6 27, 12866866289493941463298560⟩, ⟨.privateRow 6 28, 19207534396432311883453500⟩, ⟨.privateRow 6 29, 10276340657589195946957200⟩, ⟨.privateRow 7 18, 55030809528196736203200⟩, ⟨.privateRow 7 19, 172744805210750096123800⟩, ⟨.privateRow 7 20, 542231284244970250694400⟩, ⟨.privateRow 7 21, 1197218467048974054965280⟩, ⟨.privateRow 7 22, 2060008737398882643172800⟩, ⟨.privateRow 7 23, 3191289686284252295542800⟩, ⟨.privateRow 7 24, 4580533474670557939392000⟩, ⟨.privateRow 7 25, 6105325755889296536600000⟩, ⟨.privateRow 7 26, 6771309054814067801157120⟩, ⟨.privateRow 8 15, 2765353430608681372460⟩, ⟨.privateRow 8 16, 33669075859683620606250⟩, ⟨.privateRow 8 17, 135463641828068622476100⟩, ⟨.privateRow 8 18, 362952637767389430135375⟩, ⟨.privateRow 8 19, 730190430644193139257000⟩, ⟨.privateRow 8 20, 1210093521657717071485110⟩, ⟨.privateRow 8 21, 1763541301429081802527900⟩, ⟨.privateRow 8 22, 2707532404332318034672200⟩, ⟨.privateRow 8 23, 1989438354396985774382100⟩, ⟨.privateRow 9 13, 1346763034387344824250⟩, ⟨.privateRow 9 14, 33040586443636193021600⟩, ⟨.privateRow 9 15, 117283820823217914980400⟩, ⟨.privateRow 9 16, 285762396465696304862400⟩, ⟨.privateRow 9 17, 541937445037467557278200⟩, ⟨.privateRow 9 18, 877207980798040745162400⟩, ⟨.privateRow 9 19, 1279963587881732520967200⟩, ⟨.privateRow 10 11, 1140787511481045027600⟩, ⟨.privateRow 10 12, 38382746480039327491125⟩, ⟨.privateRow 10 13, 123255752907129798315360⟩, ⟨.privateRow 10 14, 279818879601850616055600⟩, ⟨.privateRow 10 15, 511189808990839561598400⟩, ⟨.privateRow 10 16, 139524650362528923792300⟩, ⟨.privateRow 11 9, 1436547236679834479200⟩, ⟨.privateRow 11 10, 53997275543436131306400⟩, ⟨.privateRow 11 11, 163227679767746192699100⟩, ⟨.privateRow 11 12, 153423244877406322378560⟩, ⟨.privateRow 12 7, 3742583590297463511600⟩, ⟨.privateRow 12 8, 94812117620869075627200⟩, ⟨.privateRow 12 9, 23005881481534408056600⟩, ⟨.privateRow 13 5, 7110908821565180672040⟩, ⟨.privateRow 13 6, 29940668722379708092800⟩, ⟨.hall 4 32, 1271344304461653514092000⟩, ⟨.hall 3 33, 34671954836443401523846800⟩, ⟨.assumptionRow 19, 56234602774929062484⟩]
  caps := #[0, 7672950707626981450674000, 1247771370633474420033300, 707914558843009870929720, 68670077584033632090384, 18038375258371728099840, 40651255123676192734050, 0, 5191943382285026208842, 66882339715329962632360, 384057821020301299872, 6342142407056105918268, 0, 0, 3035206400151580322371704, 927056752400680956954900] }

theorem case_52_37_19_checked :
    (Witness.linear .conditional case_52_37_19).check 52 37 19 = true := by
  change case_52_37_19.check 52 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_20 : Certificate := {
  objectiveScale := 1316380023582624000000
  eta := 1564359550782233257622582812800
  rows := #[⟨.count 2, 133582119885689132818220860800⟩, ⟨.count 3, 9963236568071405943208684800⟩, ⟨.count 4, 566597214902313595948147200⟩, ⟨.count 5, 20169123202984876087968000⟩, ⟨.count 6, 465441304684266371260800⟩, ⟨.path 4, 190652090892132875045040000⟩, ⟨.path 5, 16797955863930163610688000⟩, ⟨.privateRow 2 34, 11109657288284144371154973600⟩, ⟨.privateRow 2 35, 17848665578481466094047281600⟩, ⟨.privateRow 3 30, 918160547040496128373804800⟩, ⟨.privateRow 3 31, 1998023160683384465229799200⟩, ⟨.privateRow 3 32, 4379750961378426079522876800⟩, ⟨.privateRow 3 33, 5520056300004618452091211200⟩, ⟨.privateRow 3 34, 8632074436674404121402796800⟩, ⟨.privateRow 4 26, 40052193937465880135265300⟩, ⟨.privateRow 4 27, 221860355232833636967648000⟩, ⟨.privateRow 4 28, 388326730745674516500104400⟩, ⟨.privateRow 4 29, 938213309917309937868957600⟩, ⟨.privateRow 4 30, 1427159400488131760878428000⟩, ⟨.privateRow 4 31, 2019782541677373918086241600⟩, ⟨.privateRow 4 32, 2998954686406899296626149600⟩, ⟨.privateRow 5 23, 13280591893657733793308160⟩, ⟨.privateRow 5 24, 41131220480617020808454400⟩, ⟨.privateRow 5 25, 82906732396884947380830000⟩, ⟨.privateRow 5 26, 198610453870271950136572800⟩, ⟨.privateRow 5 27, 352183920544428220920672000⟩, ⟨.privateRow 5 28, 535071323865032620401415680⟩, ⟨.privateRow 5 29, 757893591127547074536336000⟩, ⟨.privateRow 5 30, 1197477045551576425171536000⟩, ⟨.privateRow 5 31, 1086184858031516288398953600⟩, ⟨.privateRow 6 20, 2876685841451368544598000⟩, ⟨.privateRow 6 21, 8314474215496212904795200⟩, ⟨.privateRow 6 22, 17182541497927500205711200⟩, ⟨.privateRow 6 23, 45596009292217946369808000⟩, ⟨.privateRow 6 24, 87347818179080655673276800⟩, ⟨.privateRow 6 25, 145450407713833241019000000⟩, ⟨.privateRow 6 26, 221743994906662570374832800⟩, ⟨.privateRow 6 27, 312823100878295428124383680⟩, ⟨.privateRow 6 28, 499379733150827460831900000⟩, ⟨.privateRow 6 29, 456365199242923177021214400⟩, ⟨.privateRow 7 17, 576260662942425031084800⟩, ⟨.privateRow 7 18, 1933371573303875696006400⟩, ⟨.privateRow 7 19, 4076921057697370251969600⟩, ⟨.privateRow 7 20, 10893207100539850325366400⟩, ⟨.privateRow 7 21, 23928854630823338886930240⟩, ⟨.privateRow 7 22, 42619483417817329328905600⟩, ⟨.privateRow 7 23, 68768952767100356353783200⟩, ⟨.privateRow 7 24, 103542220399206241162224000⟩, ⟨.privateRow 7 25, 145933087585357665404011200⟩, ⟨.privateRow 7 26, 234354868478580165333937920⟩, ⟨.privateRow 7 27, 69428327948736400379736000⟩, ⟨.privateRow 8 14, 132925511494030934153475⟩, ⟨.privateRow 8 15, 515864112691728561480720⟩, ⟨.privateRow 8 16, 1208854499666080714246800⟩, ⟨.privateRow 8 17, 3143220605672273218738800⟩, ⟨.privateRow 8 18, 7179863088925812727041600⟩, ⟨.privateRow 8 19, 14414576163252128225107200⟩, ⟨.privateRow 8 20, 24571422209790228849476400⟩, ⟨.privateRow 8 21, 38543998907356638911415200⟩, ⟨.privateRow 8 22, 56999590609589349934662450⟩, ⟨.privateRow 8 23, 79777932515396267885132400⟩, ⟨.privateRow 8 24, 41827227616788400613626800⟩, ⟨.privateRow 9 11, 37350228153675696459200⟩, ⟨.privateRow 9 12, 164273401653270483974400⟩, ⟨.privateRow 9 13, 436351223141499723057000⟩, ⟨.privateRow 9 14, 1203251965443029359777920⟩, ⟨.privateRow 9 15, 2711380298716281877027200⟩, ⟨.privateRow 9 16, 5672814534015075601862400⟩, ⟨.privateRow 9 17, 10610337890117257463371200⟩, ⟨.privateRow 9 18, 17526921049120656889497600⟩, ⟨.privateRow 9 19, 26788732869605553368121600⟩, ⟨.privateRow 9 20, 32678576539992874732841600⟩, ⟨.privateRow 10 8, 11636032617106659281520⟩, ⟨.privateRow 10 9, 65325095394282999475200⟩, ⟨.privateRow 10 10, 193933876951777654692000⟩, ⟨.privateRow 10 11, 579520055832370874020800⟩, ⟨.privateRow 10 12, 1401172260976593555149700⟩, ⟨.privateRow 10 13, 2911593939302688522442560⟩, ⟨.privateRow 10 14, 5657328239078999584015200⟩, ⟨.privateRow 10 15, 10006988050711726982107200⟩, ⟨.privateRow 10 16, 14254139955955657619862000⟩, ⟨.privateRow 11 5, 7052140980064641988800⟩, ⟨.privateRow 11 6, 29551828868842309286400⟩, ⟨.privateRow 11 7, 100845616014924380439840⟩, ⟨.privateRow 11 8, 342956750819985747244800⟩, ⟨.privateRow 11 9, 930882609368532742521600⟩, ⟨.privateRow 11 10, 2071670120849577770121600⟩, ⟨.privateRow 11 11, 4053218028292152983062800⟩, ⟨.privateRow 11 12, 4788873868195896219861120⟩, ⟨.privateRow 12 3, 18550196925822210448800⟩, ⟨.privateRow 12 4, 58180163085533296407600⟩, ⟨.privateRow 12 5, 264119470515278139247200⟩, ⟨.privateRow 12 6, 767978152729039512580320⟩, ⟨.privateRow 12 7, 1931173132593491171985600⟩, ⟨.privateRow 12 8, 1137745411450428907526400⟩, ⟨.privateRow 13 1, 71109088215651806720400⟩, ⟨.privateRow 13 2, 222602363109866525385600⟩, ⟨.privateRow 13 3, 853309058587821680644800⟩, ⟨.privateRow 13 4, 162535058778632701075200⟩, ⟨.privateRow 14 0, 462209073401736743682600⟩, ⟨.hall 4 32, 115998316267423274526441600⟩, ⟨.hall 3 33, 976536925578004164526152000⟩, ⟨.assumptionRow 20, 733679140623681155904⟩]
  caps := #[0, 129324908781133054304515200, 10602198413271531589723200, 2817179637251917840943040, 573621671456433304968120, 0, 65702501547044137776000, 486313797634707960504960, 2354664610945875622394, 713335272835564165926080, 24959099962401714748080, 0, 298273090797710408643120, 18114031419031858502731968, 0, 49599667583023712191861824] }

theorem case_52_37_20_checked :
    (Witness.linear .conditional case_52_37_20).check 52 37 20 = true := by
  change case_52_37_20.check 52 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_21 : Certificate := {
  objectiveScale := 2301216535249632000000
  eta := 3701224101895155619707722198400
  rows := #[⟨.count 2, 362516809846004124209199100800⟩, ⟨.count 3, 31674835777296094894528617600⟩, ⟨.count 4, 2270372989217512311833500800⟩, ⟨.count 5, 108487539802533141169920000⟩, ⟨.count 6, 813656548518998558774400⟩, ⟨.path 5, 99731214809247878320464000⟩, ⟨.path 6, 516983237670711075264000⟩, ⟨.privateRow 2 34, 31929171253420658527358848800⟩, ⟨.privateRow 2 35, 52979347624868046824624582400⟩, ⟨.privateRow 3 30, 2142086473401016872400070400⟩, ⟨.privateRow 3 31, 5641623288581229673688764800⟩, ⟨.privateRow 3 32, 12630752227793089738325577600⟩, ⟨.privateRow 3 33, 16425149135528270739552350400⟩, ⟨.privateRow 3 34, 26752213658756153613943497600⟩, ⟨.privateRow 4 26, 69550683720280230971903400⟩, ⟨.privateRow 4 27, 588477098716365707633584800⟩, ⟨.privateRow 4 28, 1051526780321448567991654800⟩, ⟨.privateRow 4 29, 2646580655367746612125490880⟩, ⟨.privateRow 4 30, 4105168506127854061869772800⟩, ⟨.privateRow 4 31, 5964328516352181379860456000⟩, ⟨.privateRow 4 32, 9226933064917820239714927200⟩, ⟨.privateRow 5 23, 32654749480562475492145920⟩, ⟨.privateRow 5 24, 111049051158981840336432000⟩, ⟨.privateRow 5 25, 226637251118729390225286000⟩, ⟨.privateRow 5 26, 543173864461325752164681600⟩, ⟨.privateRow 5 27, 986242143088195030852214400⟩, ⟨.privateRow 5 28, 1522839596208157702602167040⟩, ⟨.privateRow 5 29, 2213213616684052663079599200⟩, ⟨.privateRow 5 30, 3628094549846214573575049600⟩, ⟨.privateRow 5 31, 3439190621165053741512926400⟩, ⟨.privateRow 6 18, 96863874823690304616000⟩, ⟨.privateRow 6 19, 521574710589101640240000⟩, ⟨.privateRow 6 20, 8317378051527540823027200⟩, ⟨.privateRow 6 21, 22991961560423216850216000⟩, ⟨.privateRow 6 22, 47585347145886099045656160⟩, ⟨.privateRow 6 23, 124986686480835056389512000⟩, ⟨.privateRow 6 24, 238164052222748536474590000⟩, ⟨.privateRow 6 25, 402004453293279502217323200⟩, ⟨.privateRow 6 26, 623057502028423146381496800⟩, ⟨.privateRow 6 27, 901341602564395970124987840⟩, ⟨.privateRow 6 28, 1500823406099481133265996400⟩, ⟨.privateRow 6 29, 1706418594810677532985200000⟩, ⟨.privateRow 6 31, 997949756758551732336801600⟩, ⟨.privateRow 7 15, 50853534282437409923400⟩, ⟨.privateRow 7 16, 204920908515895933320960⟩, ⟨.privateRow 7 17, 2072886921226972518782400⟩, ⟨.privateRow 7 18, 5758184804903682108249600⟩, ⟨.privateRow 7 19, 11624741244118655335082400⟩, ⟨.privateRow 7 21, 126270455701831698560022720⟩, ⟨.privateRow 7 22, 85172763887562824442569600⟩, ⟨.privateRow 7 23, 187683443858382334223961600⟩, ⟨.privateRow 7 24, 286807475761292079281001600⟩, ⟨.privateRow 7 25, 413684084066464915391688000⟩, ⟨.privateRow 7 26, 690704003409460998781824000⟩, ⟨.privateRow 7 27, 664327970294970128834887200⟩, ⟨.privateRow 8 12, 21973749381300115399000⟩, ⟨.privateRow 8 13, 88412026922407523134800⟩, ⟨.privateRow 8 14, 598235326905895641737775⟩, ⟨.privateRow 8 15, 1782510549811065361166880⟩, ⟨.privateRow 8 16, 3701007217221833722203000⟩, ⟨.privateRow 8 17, 9084962167277835403580400⟩, ⟨.privateRow 8 18, 1094292719188745746870200⟩, ⟨.privateRow 8 19, 66009942186857593935519600⟩, ⟨.privateRow 8 20, 70198218723476600658261360⟩, ⟨.privateRow 8 21, 92799538387106647353056800⟩, ⟨.privateRow 8 22, 155709284178299812734623850⟩, ⟨.privateRow 8 23, 222184741672667092556437200⟩, ⟨.privateRow 8 24, 370095071329485323619197400⟩, ⟨.privateRow 8 25, 86145887074448972410239600⟩, ⟨.privateRow 9 9, 13560942475316642646240⟩, ⟨.privateRow 9 10, 47582254299356640864000⟩, ⟨.privateRow 9 11, 220993136634789732012800⟩, ⟨.privateRow 9 12, 680706132094325591654400⟩, ⟨.privateRow 9 13, 1531256421171170898804600⟩, ⟨.privateRow 9 14, 3724738866553637846833920⟩, ⟨.privateRow 9 16, 18129936940077173014742400⟩, ⟨.privateRow 9 17, 30994287413029259914795200⟩, ⟨.privateRow 9 18, 60407834662774135424160000⟩, ⟨.privateRow 9 19, 70987013544124185372184320⟩, ⟨.privateRow 9 20, 96815084131186519869971200⟩, ⟨.privateRow 9 21, 147271835281938739138166400⟩, ⟨.privateRow 9 22, 96502249691015194145433600⟩, ⟨.privateRow 10 7, 51660733239301495795200⟩, ⟨.privateRow 10 8, 108487539802533141169920⟩, ⟨.privateRow 10 9, 335454892810464318091200⟩, ⟨.privateRow 10 10, 798588834657535622500800⟩, ⟨.privateRow 10 11, 2042118396282976774963200⟩, ⟨.privateRow 10 12, 4347977181148398548450700⟩, ⟨.privateRow 10 13, 641884610498321085255360⟩, ⟨.privateRow 10 14, 15188255572354639763788800⟩, ⟨.privateRow 10 16, 111437044790914510945477200⟩, ⟨.privateRow 10 17, 45429157292310752864904000⟩, ⟨.privateRow 10 18, 89827682956497440888693760⟩, ⟨.privateRow 10 27, 724696765880921383015065600⟩, ⟨.privateRow 11 4, 35376371674739067772800⟩, ⟨.privateRow 11 5, 110953165707136167105600⟩, ⟨.privateRow 11 6, 219558116267031357129600⟩, ⟨.privateRow 11 7, 542437699012665705849600⟩, ⟨.privateRow 11 8, 1427467628980699225920000⟩, ⟨.privateRow 11 9, 3269693907937457171371200⟩, ⟨.privateRow 11 10, 6493298338181027714140800⟩, ⟨.privateRow 11 11, 2508774357933578889554400⟩, ⟨.privateRow 11 12, 15586043218297261281411840⟩, ⟨.privateRow 11 13, 12224221002749716442539200⟩, ⟨.privateRow 11 14, 67053644793334906869254400⟩, ⟨.privateRow 11 15, 152357188710182480130506400⟩, ⟨.privateRow 11 21, 78291841224161416877625600⟩, ⟨.privateRow 12 2, 155385799196336530321500⟩, ⟨.privateRow 12 3, 226998384912909018208800⟩, ⟨.privateRow 12 5, 2308589016631285593348000⟩, ⟨.privateRow 12 6, 2759651793726936778509840⟩, ⟨.privateRow 12 7, 6869687964469615024740000⟩, ⟨.privateRow 12 8, 13010970919373245472253600⟩, ⟨.privateRow 12 9, 8643106571767989592471200⟩, ⟨.privateRow 12 10, 22002629166201252693524400⟩, ⟨.privateRow 12 11, 31723564763924066030437440⟩, ⟨.privateRow 12 12, 68671644056255241457513200⟩, ⟨.privateRow 12 14, 466468169187402264025143000⟩, ⟨.privateRow 12 21, 56237228445138117053957280⟩, ⟨.privateRow 13 0, 716017762696718731721472⟩, ⟨.privateRow 13 2, 1426846990881142400169600⟩, ⟨.privateRow 13 5, 59220635789707778436130080⟩, ⟨.privateRow 13 6, 14131929526908922336608000⟩, ⟨.privateRow 13 7, 34640674167503290493006400⟩, ⟨.privateRow 13 8, 51068913957045380130134400⟩, ⟨.privateRow 13 9, 86332350033484576246625400⟩, ⟨.privateRow 13 10, 142805764893401124826671360⟩, ⟨.privateRow 13 12, 522096285299690741880240000⟩, ⟨.privateRow 13 13, 1369632588436188712865829600⟩, ⟨.privateRow 14 3, 157907488737579934585003200⟩, ⟨.privateRow 14 4, 399478243437877659072937920⟩, ⟨.privateRow 14 6, 231628431335338987865916000⟩, ⟨.privateRow 14 7, 351340088460497769829996800⟩, ⟨.privateRow 14 10, 3224637138430579716788486400⟩, ⟨.privateRow 14 11, 1109827532179914034168281600⟩, ⟨.privateRow 14 13, 8904521657567167060800571200⟩, ⟨.privateRow 15 22, 2305222170409430526438661276800⟩, ⟨.hall 14 19, 1440997539551038027278720⟩, ⟨.hall 4 29, 180575614385701584269220⟩, ⟨.hall 3 33, 3375023432181849580662129600⟩]
  caps := #[0, 48432521344744343579572800, 3269432881937905224141600, 4233698127137824330265280, 0, 403328702157837550094400, 0, 572445203393875152546480, 730110756721668989793455, 546873214207199159586840, 313350013923084539874720, 0, 6845480688339228745069260, 7105848643958734217872896, 0, 31902128650499871382819200] }

theorem case_52_37_21_checked :
    (Witness.linear .conditional case_52_37_21).check 52 37 21 = true := by
  change case_52_37_21.check 52 37 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_22 : Certificate := {
  objectiveScale := 2344801917006549000000
  eta := 3776640082986433868645484844800
  rows := #[⟨.count 2, 352957639139915033051831203200⟩, ⟨.count 3, 28353753398756138804465414400⟩, ⟨.count 4, 1843147566549694830192768000⟩, ⟨.count 5, 74470608749482619401728000⟩, ⟨.path 4, 210380229329651442341280000⟩, ⟨.path 5, 73477368870255148518720000⟩, ⟨.privateRow 3 30, 1489877616294336654405820800⟩, ⟨.privateRow 3 34, 149433188958016508357878665600⟩, ⟨.privateRow 4 27, 423302243706601540862724000⟩, ⟨.privateRow 4 28, 850749131412058215602865600⟩, ⟨.privateRow 4 29, 1625553756609800301628344000⟩, ⟨.privateRow 4 32, 32730588887517723159912754800⟩, ⟨.privateRow 5 23, 7679781527290395125803200⟩, ⟨.privateRow 5 24, 69195607296394267194105600⟩, ⟨.privateRow 5 25, 159937268322131031824492400⟩, ⟨.privateRow 5 26, 436916401868616332222102400⟩, ⟨.privateRow 5 27, 761772268666582627630176000⟩, ⟨.privateRow 5 28, 1128695163859345950307440000⟩, ⟨.privateRow 5 30, 7223649048699814081967616000⟩, ⟨.privateRow 6 18, 33245807477447597947200⟩, ⟨.privateRow 6 19, 161114297775322974667200⟩, ⟨.privateRow 6 20, 2210846197250265263488800⟩, ⟨.privateRow 6 21, 10959027083020453650595200⟩, ⟨.privateRow 6 22, 28717728499019235106791360⟩, ⟨.privateRow 6 23, 86468651270232596972006400⟩, ⟨.privateRow 6 24, 188561908560213413657031600⟩, ⟨.privateRow 6 25, 330197359866009542811590400⟩, ⟨.privateRow 6 26, 552633975761785604810323200⟩, ⟨.privateRow 6 27, 904724808045276972456743040⟩, ⟨.privateRow 6 28, 1019025556443115686579114000⟩, ⟨.privateRow 7 15, 9696693847588882734600⟩, ⟨.privateRow 7 16, 62058840624568849501440⟩, ⟨.privateRow 7 17, 554096791290793299120000⟩, ⟨.privateRow 7 18, 2088518674865297819760000⟩, ⟨.privateRow 7 19, 5404290704389537310750400⟩, ⟨.privateRow 7 20, 17771395269762897811776000⟩, ⟨.privateRow 7 21, 43813541480945607748016640⟩, ⟨.privateRow 7 22, 86589321238113703068259200⟩, ⟨.privateRow 7 23, 148553349745061683494072000⟩, ⟨.privateRow 7 24, 242295444895638093839193600⟩, ⟨.privateRow 7 25, 381532580589797239330728000⟩, ⟨.privateRow 7 26, 734125055168337205177284480⟩, ⟨.privateRow 7 27, 786712165242581234023567200⟩, ⟨.privateRow 8 12, 7541872992569131015800⟩, ⟨.privateRow 8 13, 23956537741101945579600⟩, ⟨.privateRow 8 14, 161207535216165175462725⟩, ⟨.privateRow 8 15, 543014855464977433137600⟩, ⟨.privateRow 8 16, 1328447057119676934640200⟩, ⟨.privateRow 8 17, 4177037349730595639520000⟩, ⟨.privateRow 8 18, 11618255345052746329839900⟩, ⟨.privateRow 8 19, 25793205634586428074036000⟩, ⟨.privateRow 8 20, 48138266936970249447648240⟩, ⟨.privateRow 8 21, 81557814541642582804861200⟩, ⟨.privateRow 8 22, 131901702235289674618080150⟩, ⟨.privateRow 8 23, 208323770621599556670146400⟩, ⟨.privateRow 8 24, 393821523925974883383044400⟩, ⟨.privateRow 8 25, 641626353217417334995388160⟩, ⟨.privateRow 8 26, 750921668251130667850158600⟩, ⟨.privateRow 9 9, 7757355078071106187680⟩, ⟨.privateRow 9 10, 16331273848570749868800⟩, ⟨.privateRow 9 11, 60334983940553048126400⟩, ⟨.privateRow 9 12, 191652301928815564636800⟩, ⟨.privateRow 9 13, 465441304684266371260800⟩, ⟨.privateRow 9 14, 1334265073428230264280960⟩, ⟨.privateRow 9 15, 3612711079215972310262400⟩, ⟨.privateRow 9 16, 9010466282990284879536000⟩, ⟨.privateRow 9 17, 18475434010939351236991200⟩, ⟨.privateRow 9 18, 32961706940822136655651200⟩, ⟨.privateRow 9 19, 54161853155092463402381760⟩, ⟨.privateRow 9 20, 84882703120938059706969600⟩, ⟨.privateRow 9 21, 129276322376054984617687200⟩, ⟨.privateRow 9 22, 238616242201467226333036800⟩, ⟨.privateRow 9 23, 387660891101473413218995200⟩, ⟨.privateRow 9 24, 585028690567810544250074880⟩, ⟨.privateRow 9 26, 993044881394142540105542400⟩, ⟨.privateRow 10 7, 11081935825815865982400⟩, ⟨.privateRow 10 8, 34908097851319977844560⟩, ⟨.privateRow 10 9, 97987643091424499212800⟩, ⟨.privateRow 10 10, 219791727212014675317600⟩, ⟨.privateRow 10 11, 616025256199764314904000⟩, ⟨.privateRow 10 12, 1556319362538015678903300⟩, ⟨.privateRow 10 13, 3832133408567126456713920⟩, ⟨.privateRow 10 14, 8743647366568718260113600⟩, ⟨.privateRow 10 15, 16934902855050614892796800⟩, ⟨.privateRow 10 16, 29148261705852181500207600⟩, ⟨.privateRow 10 17, 46522974045486443200113600⟩, ⟨.privateRow 10 18, 70723806246774275113078560⟩, ⟨.privateRow 10 19, 104207136548755193121168000⟩, ⟨.privateRow 10 20, 182220270783890284348603200⟩, ⟨.privateRow 10 21, 294790574902527850997822400⟩, ⟨.privateRow 10 23, 1457482901488311714966069120⟩, ⟨.privateRow 11 5, 21156422940193925966400⟩, ⟨.privateRow 11 6, 66491614954895195894400⟩, ⟨.privateRow 11 7, 139632391405279911378240⟩, ⟨.privateRow 11 8, 391950572365697996851200⟩, ⟨.privateRow 11 9, 982598309889006783772800⟩, ⟨.privateRow 11 11, 9832447561455127092884400⟩, ⟨.privateRow 11 12, 8750296528064207779703040⟩, ⟨.privateRow 11 13, 20545909021062615531369600⟩, ⟨.privateRow 11 14, 34514262901202521684262400⟩, ⟨.privateRow 11 15, 53874831017203832473437600⟩, ⟨.privateRow 11 16, 80055904405693815856857600⟩, ⟨.privateRow 11 17, 114870913996076940427165440⟩, ⟨.privateRow 11 19, 678962503208173569076692000⟩, ⟨.privateRow 11 21, 658056431272771937900894400⟩, ⟨.privateRow 11 24, 3245522217563389406801558400⟩, ⟨.privateRow 12 3, 55650590777466631346400⟩, ⟨.privateRow 12 4, 116360326171066592815200⟩, ⟨.privateRow 12 5, 365703882251923577419200⟩, ⟨.privateRow 12 6, 895974511517212764677040⟩, ⟨.privateRow 12 7, 2088361643385984639472800⟩, ⟨.privateRow 12 8, 497763617509562647042800⟩, ⟨.privateRow 12 9, 14757227248518798477033600⟩, ⟨.privateRow 12 11, 73043255415117535863194880⟩, ⟨.privateRow 12 13, 159404696060040380880453600⟩, ⟨.privateRow 12 14, 92050714695161263799557800⟩, ⟨.privateRow 12 20, 1358894675801106026426844000⟩, ⟨.privateRow 12 23, 12225785536917015129438372000⟩, ⟨.privateRow 13 1, 639981793940866260483600⟩, ⟨.privateRow 13 2, 222602363109866525385600⟩, ⟨.privateRow 13 3, 1163603261710665928152000⟩, ⟨.privateRow 13 4, 2925631058015388619353600⟩, ⟨.privateRow 13 5, 6143825221832316100642560⟩, ⟨.privateRow 13 6, 3233592222017008474022400⟩, ⟨.privateRow 13 9, 134716167624552347831797800⟩, ⟨.privateRow 13 10, 90109436586873969476090880⟩, ⟨.privateRow 13 12, 187859271206026588461955200⟩, ⟨.privateRow 13 13, 69544688274907466972551200⟩, ⟨.privateRow 13 14, 115429443561698060072678400⟩, ⟨.privateRow 13 15, 180218873173747938952181760⟩, ⟨.privateRow 13 16, 291262825331309800326758400⟩, ⟨.privateRow 13 17, 450547182934369847380454400⟩, ⟨.privateRow 13 18, 2442901933442849497160256000⟩, ⟨.privateRow 13 20, 2235328409876657674617118080⟩, ⟨.privateRow 13 22, 12139174667470351228852924800⟩, ⟨.privateRow 13 24, 64674000168488180819430681600⟩, ⟨.privateRow 14 6, 351278895785319925198776000⟩, ⟨.privateRow 14 8, 659341243207577464863228900⟩, ⟨.privateRow 14 9, 363850982581847164626942720⟩, ⟨.privateRow 14 11, 844775968001943463838352000⟩, ⟨.privateRow 14 12, 74877869891081352476581200⟩, ⟨.privateRow 14 13, 45380527206715971197928000⟩, ⟨.privateRow 14 17, 6185149760526783464890929600⟩, ⟨.privateRow 14 19, 66558106569850091090294400⟩, ⟨.privateRow 15 5, 6160322530298347319801692800⟩, ⟨.privateRow 15 7, 6843005331712712490220893000⟩, ⟨.privateRow 15 9, 5723997165007107833765318400⟩, ⟨.privateRow 15 10, 6701889346148751479784259200⟩, ⟨.privateRow 15 14, 258837081104972576462256000⟩, ⟨.hall 14 5, 25975246083844137900019200⟩, ⟨.hall 13 7, 745380640110310638033600⟩, ⟨.hall 14 9, 3331285400963593014701760⟩, ⟨.hall 6 16, 17541925326023978880⟩, ⟨.hall 13 17, 310671420045976995805800⟩, ⟨.hall 7 22, 383074845178247085248⟩, ⟨.hall 9 22, 3580935450515862603120⟩, ⟨.hall 13 22, 16639526642462522772573600⟩, ⟨.hall 3 31, 14308897756506747781186800⟩, ⟨.hall 1 35, 58341878081060818734592502400⟩]
  caps := #[0, 0, 0, 1347820194851926213017600, 0, 73753070966600946120000, 1984454389377420859130400, 38938547287608380665440, 1098348387868835599616505, 0, 0, 5438665208942951992149600, 33637222211616057669136920, 69085486958531309883975600, 0, 0] }

theorem case_52_37_22_checked :
    (Witness.linear .conditional case_52_37_22).check 52 37 22 = true := by
  change case_52_37_22.check 52 37 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876, 177650] }

theorem case_52_37_23_checked :
    (Witness.linear .negative case_52_37_23).check 52 37 23 = true := by
  change case_52_37_23.check 52 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226] }

theorem case_52_37_24_checked :
    (Witness.linear .negative case_52_37_24).check 52 37 24 = true := by
  change case_52_37_24.check 52 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_38_1_checked :
    (Witness.rising).check 52 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_38_2_checked :
    (Witness.rising).check 52 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_38_3_checked :
    (Witness.rising).check 52 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_38_4_checked :
    (Witness.rising).check 52 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_38_5_checked :
    (Witness.rising).check 52 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_38_6_checked :
    (Witness.rising).check 52 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_38_7_checked :
    (Witness.rising).check 52 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_38_8_checked :
    (Witness.rising).check 52 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_38_9_checked :
    (Witness.rising).check 52 38 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_52_38_10_checked :
    (Witness.linear .positive case_52_38_10).check 52 38 10 = true := by
  change case_52_38_10.check 52 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_52_38_11_checked :
    (Witness.linear .positive case_52_38_11).check 52 38 11 = true := by
  change case_52_38_11.check 52 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_52_38_12_checked :
    (Witness.linear .positive case_52_38_12).check 52 38 12 = true := by
  change case_52_38_12.check 52 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_52_38_13_checked :
    (Witness.linear .positive case_52_38_13).check 52 38 13 = true := by
  change case_52_38_13.check 52 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_52_38_14_checked :
    (Witness.linear .positive case_52_38_14).check 52 38 14 = true := by
  change case_52_38_14.check 52 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_52_38_15_checked :
    (Witness.linear .positive case_52_38_15).check 52 38 15 = true := by
  change case_52_38_15.check 52 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_52_38_16_checked :
    (Witness.linear .positive case_52_38_16).check 52 38 16 = true := by
  change case_52_38_16.check 52 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_52_38_17_checked :
    (Witness.linear .positive case_52_38_17).check 52 38 17 = true := by
  change case_52_38_17.check 52 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_52_38_18_checked :
    (Witness.linear .positive case_52_38_18).check 52 38 18 = true := by
  change case_52_38_18.check 52 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_19 : Certificate := {
  objectiveScale := 11
  eta := 226413150
  rows := #[⟨.assumptionRow 19, 16⟩]
  caps := #[0, 0, 65202585, 18917730, 5534605, 1634380, 487730, 147288, 45084, 14872, 7597590, 5821530, 3108105, 1356080, 502964] }

theorem case_52_38_19_checked :
    (Witness.linear .conditional case_52_38_19).check 52 38 19 = true := by
  change case_52_38_19.check 52 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_20 : Certificate := {
  objectiveScale := 6714534030204000000
  eta := 16229300159534944459066689600
  rows := #[⟨.count 2, 1267523980199899693403932800⟩, ⟨.count 3, 83725108795963375990048800⟩, ⟨.count 4, 3969499855579049641449600⟩, ⟨.count 5, 85467700239740303284800⟩, ⟨.count 6, 6330940758499281724800⟩, ⟨.path 4, 2524975493678678392934400⟩, ⟨.path 5, 58212160289523307267200⟩, ⟨.privateRow 2 35, 101849009452357194747720000⟩, ⟨.privateRow 2 36, 152512362872247696750432000⟩, ⟨.privateRow 3 30, 760240469416455413786400⟩, ⟨.privateRow 3 31, 10439088216689465636022720⟩, ⟨.privateRow 3 32, 19425304666062827357225400⟩, ⟨.privateRow 3 33, 40896294564715735121776800⟩, ⟨.privateRow 3 34, 47268386438145262177788000⟩, ⟨.privateRow 3 35, 67673008502788447176818400⟩, ⟨.privateRow 4 27, 832716551641358649365100⟩, ⟨.privateRow 4 28, 2524688732478677847825600⟩, ⟨.privateRow 4 29, 4157053975549590862546800⟩, ⟨.privateRow 4 30, 9444180876491303512970400⟩, ⟨.privateRow 4 31, 13516954203193372687555800⟩, ⟨.privateRow 4 32, 17888073113139720513422400⟩, ⟨.privateRow 4 33, 24365416876679298128108400⟩, ⟨.privateRow 5 23, 14676271758339243998400⟩, ⟨.privateRow 5 24, 241778627567087569070112⟩, ⟨.privateRow 5 25, 538763058548288874780480⟩, ⟨.privateRow 5 26, 975518834125258072770120⟩, ⟨.privateRow 5 27, 2216462359550598531852480⟩, ⟨.privateRow 5 28, 3684607521446581963833600⟩, ⟨.privateRow 5 29, 5271267894341671949702976⟩, ⟨.privateRow 5 30, 6978912545131683209333280⟩, ⟨.privateRow 5 31, 10173188704832495803581120⟩, ⟨.privateRow 5 32, 5006507951821231987971840⟩, ⟨.privateRow 6 20, 3246636286409888064000⟩, ⟨.privateRow 6 21, 60583585869527848727600⟩, ⟨.privateRow 6 22, 134388606100871116612800⟩, ⟨.privateRow 6 23, 238993013633347885111200⟩, ⟨.privateRow 6 24, 575412171161379161209600⟩, ⟨.privateRow 6 25, 1035900181609444972220400⟩, ⟨.privateRow 6 26, 1619364204013280561179200⟩, ⟨.privateRow 6 27, 2322751820507180917254400⟩, ⟨.privateRow 6 28, 3067551828851518638389760⟩, ⟨.privateRow 6 29, 4496814462922385648444400⟩, ⟨.privateRow 7 17, 527578396541606810400⟩, ⟨.privateRow 7 18, 15714299382703574281200⟩, ⟨.privateRow 7 19, 40603245056913662600400⟩, ⟨.privateRow 7 20, 72805818722741739835200⟩, ⟨.privateRow 7 21, 166906619996799245472000⟩, ⟨.privateRow 7 22, 331266475188474916250160⟩, ⟨.privateRow 7 23, 553253878506631675172800⟩, ⟨.privateRow 7 24, 838355045754397072151250⟩, ⟨.privateRow 7 25, 1186825287191526063338400⟩, ⟨.privateRow 7 26, 1570864675702634277966000⟩, ⟨.privateRow 7 27, 421165833959164716742320⟩, ⟨.privateRow 8 14, 139653104966895920400⟩, ⟨.privateRow 8 15, 4599824144847134378175⟩, ⟨.privateRow 8 16, 14613921584202508648080⟩, ⟨.privateRow 8 17, 29111022237742232931000⟩, ⟨.privateRow 8 18, 63857277458324485858800⟩, ⟨.privateRow 8 19, 124442554284251506403100⟩, ⟨.privateRow 8 20, 226690844659445871759600⟩, ⟨.privateRow 8 21, 361417580550827745464520⟩, ⟨.privateRow 8 22, 533030039972536747440800⟩, ⟨.privateRow 8 23, 552671344027116984319650⟩, ⟨.privateRow 9 11, 55534568057011243200⟩, ⟨.privateRow 9 12, 1582735189624820431200⟩, ⟨.privateRow 9 13, 6206804665195374240000⟩, ⟨.privateRow 9 14, 14574353204461888137300⟩, ⟨.privateRow 9 15, 33976048737279478589760⟩, ⟨.privateRow 9 16, 64213827693349857494400⟩, ⟨.privateRow 9 17, 115904915424833003884800⟩, ⟨.privateRow 9 18, 196962601375533209216000⟩, ⟨.privateRow 9 19, 253429477029622762377600⟩, ⟨.privateRow 10 9, 664748779642424581104⟩, ⟨.privateRow 10 10, 3198791120083847608320⟩, ⟨.privateRow 10 11, 8652285703282351690560⟩, ⟨.privateRow 10 12, 23238276666491481154560⟩, ⟨.privateRow 10 13, 47482055688744612936000⟩, ⟨.privateRow 10 14, 83948274457700475670848⟩, ⟨.privateRow 10 15, 75428637036977156549760⟩, ⟨.privateRow 11 6, 431655051715860117600⟩, ⟨.privateRow 11 7, 2034945243803340554400⟩, ⟨.privateRow 11 8, 5935256961093076617000⟩, ⟨.privateRow 11 9, 10745938919031675559200⟩, ⟨.privateRow 11 10, 64628353576346834274000⟩, ⟨.privateRow 12 4, 1513920616162871716800⟩, ⟨.privateRow 12 5, 6330940758499281724800⟩, ⟨.privateRow 12 6, 19897242383854885420800⟩, ⟨.privateRow 13 1, 4178420900609525938368⟩, ⟨.privateRow 13 2, 4352521771468256185800⟩, ⟨.hall 3 34, 4848460537885839204913440⟩, ⟨.assumptionRow 20, 4409857971088008075⟩]
  caps := #[0, 0, 0, 84070488969269606507340, 7496515668526221048075, 5584995981235953430680, 0, 774419557472231903010, 8393992448758202738900, 0, 1081993692789725157936, 0, 121032064005573922461975, 82160482045250773980816, 1014065023386950792357100] }

theorem case_52_38_20_checked :
    (Witness.linear .conditional case_52_38_20).check 52 38 20 = true := by
  change case_52_38_20.check 52 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_21 : Certificate := {
  objectiveScale := 32805294833282400000
  eta := 110705799314334176402981731200
  rows := #[⟨.count 2, 8987783357211090293429568000⟩, ⟨.count 3, 631463858604614607435864000⟩, ⟨.count 4, 33731252361284173029734400⟩, ⟨.count 5, 940144702637143336132800⟩, ⟨.path 4, 13235465455902732060345600⟩, ⟨.path 5, 946128241467659711260800⟩, ⟨.privateRow 2 35, 741617479596933234986090400⟩, ⟨.privateRow 2 36, 1126293353759297716687094400⟩, ⟨.privateRow 3 30, 2724678628939128372310800⟩, ⟨.privateRow 3 31, 74354999926346514073258560⟩, ⟨.privateRow 3 32, 139480912688471737730146800⟩, ⟨.privateRow 3 33, 297851769865115707306665600⟩, ⟨.privateRow 3 34, 350726204344912083451764000⟩, ⟨.privateRow 3 35, 510759724838256926891258400⟩, ⟨.privateRow 4 27, 5585670326084694404258700⟩, ⟨.privateRow 4 28, 17974671338514907117015200⟩, ⟨.privateRow 4 29, 29443622732590534481613600⟩, ⟨.privateRow 4 30, 67488145032640268150454240⟩, ⟨.privateRow 4 31, 98120481029398524016920600⟩, ⟨.privateRow 4 32, 132436949727046474401091200⟩, ⟨.privateRow 4 33, 185251240269637107369804000⟩, ⟨.privateRow 5 22, 4748205568874461293600⟩, ⟨.privateRow 5 23, 223251992747442852822720⟩, ⟨.privateRow 5 24, 1720749698160104772800640⟩, ⟨.privateRow 5 25, 3831485347043765299848960⟩, ⟨.privateRow 5 26, 6887272177652406106366800⟩, ⟨.privateRow 5 27, 15568959071290597913603520⟩, ⟨.privateRow 5 28, 26114180987695762222541280⟩, ⟨.privateRow 5 29, 37951077614454284270582592⟩, ⟨.privateRow 5 30, 51428764157593065163240320⟩, ⟨.privateRow 5 31, 77483117755121009173482240⟩, ⟨.privateRow 5 32, 46827752961353712169741920⟩, ⟨.privateRow 6 18, 844125434466570896640⟩, ⟨.privateRow 6 19, 6557045785588541786400⟩, ⟨.privateRow 6 20, 92042138719720326614400⟩, ⟨.privateRow 6 21, 465587934947968010178000⟩, ⟨.privateRow 6 22, 974677106774412145540800⟩, ⟨.privateRow 6 23, 1700174140694982107195040⟩, ⟨.privateRow 6 24, 4029643792784792817835200⟩, ⟨.privateRow 6 25, 7208171737348838448792600⟩, ⟨.privateRow 6 26, 11359516560964425494784000⟩, ⟨.privateRow 6 27, 16554354926682538496731200⟩, ⟨.privateRow 6 28, 22398868403570458742342400⟩, ⟨.privateRow 6 29, 34428447212313906429678000⟩, ⟨.privateRow 6 30, 7108591315001610163329600⟩, ⟨.privateRow 7 15, 558612419867583681600⟩, ⟨.privateRow 7 16, 3412772752628519054775⟩, ⟨.privateRow 7 17, 36244635842408387874480⟩, ⟨.privateRow 7 18, 143463639688135509085200⟩, ⟨.privateRow 7 19, 311372711343498327138000⟩, ⟨.privateRow 7 20, 533183917004861382760500⟩, ⟨.privateRow 7 21, 1184245634382462232635600⟩, ⟨.privateRow 7 22, 2303117111182557450460680⟩, ⟨.privateRow 7 23, 3820722747754316520916800⟩, ⟨.privateRow 7 24, 5822783841680362815107850⟩, ⟨.privateRow 7 25, 8362946636950461898399200⟩, ⟨.privateRow 7 26, 11323678914170777775020400⟩, ⟨.privateRow 7 27, 7618021014702185699451840⟩, ⟨.privateRow 8 12, 374858334384825891600⟩, ⟨.privateRow 8 13, 1978418987031025539000⟩, ⟨.privateRow 8 14, 16479066386093718607200⟩, ⟨.privateRow 8 15, 56681703978438881692350⟩, ⟨.privateRow 8 16, 127251909245835562668480⟩, ⟨.privateRow 8 17, 226048500832487746584600⟩, ⟨.privateRow 8 18, 469341858154129443252000⟩, ⟨.privateRow 8 19, 881187816823618775070600⟩, ⟨.privateRow 8 20, 1572087698349162548299200⟩, ⟨.privateRow 8 21, 2485685615305780487199600⟩, ⟨.privateRow 8 22, 3673528375119208220815200⟩, ⟨.privateRow 8 23, 5169905575960124387237850⟩, ⟨.privateRow 8 24, 785828021648723344090800⟩, ⟨.privateRow 9 9, 301473369452346748800⟩, ⟨.privateRow 9 10, 1424461670662338388080⟩, ⟨.privateRow 9 11, 9329807433577888857600⟩, ⟨.privateRow 9 12, 29896109137357719256000⟩, ⟨.privateRow 9 13, 68336919363801070382400⟩, ⟨.privateRow 9 14, 106043257704862968890400⟩, ⟨.privateRow 9 15, 307472689504448449101120⟩, ⟨.privateRow 9 16, 451305634070163082953600⟩, ⟨.privateRow 9 17, 822778800883425882619200⟩, ⟨.privateRow 9 18, 1368538360628928066177600⟩, ⟨.privateRow 9 19, 2089210450304762969184000⟩, ⟨.privateRow 9 20, 441583117905324900304800⟩, ⟨.privateRow 10 6, 247732464463015371840⟩, ⟨.privateRow 10 7, 1294965155147580352800⟩, ⟨.privateRow 10 8, 6783150812677801848000⟩, ⟨.privateRow 10 9, 21082032725802608143584⟩, ⟨.privateRow 10 10, 49481300138797017691200⟩, ⟨.privateRow 10 11, 95913752491264118130720⟩, ⟨.privateRow 10 12, 169594730671798405733760⟩, ⟨.privateRow 10 13, 430899655375357362394200⟩, ⟨.privateRow 10 14, 603971748360831476545920⟩, ⟨.privateRow 10 15, 681299667625358417613120⟩, ⟨.privateRow 11 3, 569784668264935355232⟩, ⟨.privateRow 11 4, 1780577088327922985100⟩, ⟨.privateRow 11 5, 6812642772732922725600⟩, ⟨.privateRow 11 6, 20719442482361285644800⟩, ⟨.privateRow 11 7, 49517000932547953490400⟩, ⟨.privateRow 11 8, 99000086111032517971560⟩, ⟨.privateRow 11 9, 215168683936890061778400⟩, ⟨.privateRow 11 10, 339496698174523982492400⟩, ⟨.privateRow 12 2, 18802894052742866722656⟩, ⟨.privateRow 12 3, 23938869743075409021900⟩, ⟨.privateRow 12 4, 72668189575817842406400⟩, ⟨.privateRow 12 5, 140072064281796608161200⟩, ⟨.privateRow 13 0, 84371960493076966063200⟩, ⟨.hall 3 34, 39544276944732795657433440⟩, ⟨.assumptionRow 21, 6133726836591354000⟩]
  caps := #[0, 0, 0, 85827087912178350127260, 0, 21857756132379444252768, 9045662810454190188360, 0, 16761162378333647608560, 6983608385058760439600, 18275325195845988618192, 0, 0, 348148219037778588646800, 11475966937596904138968000] }

theorem case_52_38_21_checked :
    (Witness.linear .conditional case_52_38_21).check 52 38 21 = true := by
  change case_52_38_21.check 52 38 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_22 : Certificate := {
  objectiveScale := 8
  eta := 11055525
  rows := #[⟨.assumptionRow 22, 5⟩]
  caps := #[0, 0, 4292145, 1677390, 575575, 254771, 93423, 38760, 15504, 5916, 11425365, 11759670, 8379475, 4999280, 2629429] }

theorem case_52_38_22_checked :
    (Witness.linear .conditional case_52_38_22).check 52 38 22 = true := by
  change case_52_38_22.check 52 38 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640, 653752] }

theorem case_52_38_23_checked :
    (Witness.linear .negative case_52_38_23).check 52 38 23 = true := by
  change case_52_38_23.check 52 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888] }

theorem case_52_38_24_checked :
    (Witness.linear .negative case_52_38_24).check 52 38 24 = true := by
  change case_52_38_24.check 52 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_39_1_checked :
    (Witness.rising).check 52 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_39_2_checked :
    (Witness.rising).check 52 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_39_3_checked :
    (Witness.rising).check 52 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_39_4_checked :
    (Witness.rising).check 52 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_39_5_checked :
    (Witness.rising).check 52 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_39_6_checked :
    (Witness.rising).check 52 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_39_7_checked :
    (Witness.rising).check 52 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_39_8_checked :
    (Witness.rising).check 52 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_39_9_checked :
    (Witness.rising).check 52 39 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_52_39_10_checked :
    (Witness.linear .positive case_52_39_10).check 52 39 10 = true := by
  change case_52_39_10.check 52 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_52_39_11_checked :
    (Witness.linear .positive case_52_39_11).check 52 39 11 = true := by
  change case_52_39_11.check 52 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_52_39_12_checked :
    (Witness.linear .positive case_52_39_12).check 52 39 12 = true := by
  change case_52_39_12.check 52 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_52_39_13_checked :
    (Witness.linear .positive case_52_39_13).check 52 39 13 = true := by
  change case_52_39_13.check 52 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_52_39_14_checked :
    (Witness.linear .positive case_52_39_14).check 52 39 14 = true := by
  change case_52_39_14.check 52 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_52_39_15_checked :
    (Witness.linear .positive case_52_39_15).check 52 39 15 = true := by
  change case_52_39_15.check 52 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_52_39_16_checked :
    (Witness.linear .positive case_52_39_16).check 52 39 16 = true := by
  change case_52_39_16.check 52 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_52_39_17_checked :
    (Witness.linear .positive case_52_39_17).check 52 39 17 = true := by
  change case_52_39_17.check 52 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_52_39_18_checked :
    (Witness.linear .positive case_52_39_18).check 52 39 18 = true := by
  change case_52_39_18.check 52 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_19 : Certificate := {
  objectiveScale := 999
  eta := 40875947760
  rows := #[⟨.assumptionRow 19, 1748⟩]
  caps := #[0, 0, 11625259725, 3333040515, 964321345, 281885976, 83374698, 24996970, 7613892, 2362776, 1430715, 431730585, 295861995, 139683830] }

theorem case_52_39_19_checked :
    (Witness.linear .conditional case_52_39_19).check 52 39 19 = true := by
  change case_52_39_19.check 52 39 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_20 : Certificate := {
  objectiveScale := 915
  eta := 35891136600
  rows := #[⟨.assumptionRow 20, 1186⟩]
  caps := #[0, 0, 10296895875, 3109764105, 943841340, 288133765, 88583396, 27464690, 8600844, 2731365, 1451265270, 1182461280, 677270880, 320496605] }

theorem case_52_39_20_checked :
    (Witness.linear .conditional case_52_39_20).check 52 39 20 = true := by
  change case_52_39_20.check 52 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_21 : Certificate := {
  objectiveScale := 10582315380000000
  eta := 110247836732427649246992000
  rows := #[⟨.count 2, 5526155159318686088196000⟩, ⟨.count 3, 193114563683458769352000⟩, ⟨.count 4, 2601202136571737899200⟩, ⟨.path 2, 659499328547344817532000⟩, ⟨.path 3, 129127186231082263224000⟩, ⟨.path 4, 2593537253745566768640⟩, ⟨.privateRow 2 36, 402863924785658214879000⟩, ⟨.privateRow 2 37, 558531330073692097122000⟩, ⟨.privateRow 3 31, 22632470769855012066000⟩, ⟨.privateRow 3 32, 43869219155600153515200⟩, ⟨.privateRow 3 33, 77885150471085211254000⟩, ⟨.privateRow 3 34, 161111728676902823820000⟩, ⟨.privateRow 3 35, 170642152820038375476000⟩, ⟨.privateRow 3 36, 220580843627639250756000⟩, ⟨.privateRow 4 26, 537526897209286344360⟩, ⟨.privateRow 4 27, 1369198171043562459600⟩, ⟨.privateRow 4 28, 7693508059789115614050⟩, ⟨.privateRow 4 29, 11105674944748414430400⟩, ⟨.privateRow 4 30, 17488145377046383439400⟩, ⟨.privateRow 4 31, 38937361855733020920240⟩, ⟨.privateRow 4 32, 53528377194910976658300⟩, ⟨.privateRow 4 33, 67373330444496257781600⟩, ⟨.privateRow 4 34, 84279772390157400256200⟩, ⟨.privateRow 5 21, 2090578369758278400⟩, ⟨.privateRow 5 22, 72607394918912515200⟩, ⟨.privateRow 5 23, 167376930728772164400⟩, ⟨.privateRow 5 24, 602324136214220347200⟩, ⟨.privateRow 5 25, 2097790865133944460480⟩, ⟨.privateRow 5 26, 3012988003792736569600⟩, ⟨.privateRow 5 27, 4466586017562616747800⟩, ⟨.privateRow 5 28, 9775544456989709798400⟩, ⟨.privateRow 5 29, 15743797272921301584000⟩, ⟨.privateRow 5 30, 21673025959284072172800⟩, ⟨.privateRow 5 31, 27512925974055712990800⟩, ⟨.privateRow 5 32, 34865620761643688016000⟩, ⟨.privateRow 6 17, 403512369162903000⟩, ⟨.privateRow 6 18, 9432101629182857625⟩, ⟨.privateRow 6 19, 27438841103077404000⟩, ⟨.privateRow 6 20, 86236357752528984000⟩, ⟨.privateRow 6 21, 237627399552933159000⟩, ⟨.privateRow 6 22, 639096340692511201500⟩, ⟨.privateRow 6 23, 1011495460663444302000⟩, ⟨.privateRow 6 24, 1402124780367255344400⟩, ⟨.privateRow 6 25, 2836109104015306119000⟩, ⟨.privateRow 6 26, 4874395793457104664750⟩, ⟨.privateRow 6 27, 7349362928311172769000⟩, ⟨.privateRow 6 28, 10182858809364281040000⟩, ⟨.privateRow 6 29, 12974456015590150481400⟩, ⟨.privateRow 6 30, 5331709811841728064750⟩, ⟨.privateRow 7 13, 97995861082419300⟩, ⟨.privateRow 7 14, 1547303069722410000⟩, ⟨.privateRow 7 15, 5444214504578850000⟩, ⟨.privateRow 7 16, 19599172216483860000⟩, ⟨.privateRow 7 17, 49242920193915698250⟩, ⟨.privateRow 7 18, 114589826892375634800⟩, ⟨.privateRow 7 19, 253249303854423591000⟩, ⟨.privateRow 7 20, 428769582951385368000⟩, ⟨.privateRow 7 21, 609534255932648046000⟩, ⟨.privateRow 7 22, 1082765177814294702000⟩, ⟨.privateRow 7 23, 1805671736304658021800⟩, ⟨.privateRow 7 24, 2871932035455434952000⟩, ⟨.privateRow 7 25, 4184668257872010158250⟩, ⟨.privateRow 7 26, 5727438098005626288000⟩, ⟨.privateRow 7 27, 297907417690554672000⟩, ⟨.privateRow 8 10, 311805012534970500⟩, ⟨.privateRow 8 11, 1306611481098924000⟩, ⟨.privateRow 8 12, 5373439716019324950⟩, ⟨.privateRow 8 13, 16367028026397048000⟩, ⟨.privateRow 8 14, 36076994783675846000⟩, ⟨.privateRow 8 15, 73708259433756948000⟩, ⟨.privateRow 8 16, 141767345699233254000⟩, ⟨.privateRow 8 17, 240852049682568324000⟩, ⟨.privateRow 8 18, 359971463042753562000⟩, ⟨.privateRow 8 19, 618429264861667644000⟩, ⟨.privateRow 8 20, 927013624767163683750⟩, ⟨.privateRow 8 21, 1442409987986773533000⟩, ⟨.privateRow 8 22, 2158979480793807071400⟩, ⟨.privateRow 8 23, 333839233420775082000⟩, ⟨.privateRow 9 6, 146340485883079488⟩, ⟨.privateRow 9 7, 457314018384623400⟩, ⟨.privateRow 9 8, 1749723200775950400⟩, ⟨.privateRow 9 9, 6485544260727386400⟩, ⟨.privateRow 9 10, 17421486414652320000⟩, ⟨.privateRow 9 11, 35487567826646775840⟩, ⟨.privateRow 9 12, 65853218647385769600⟩, ⟨.privateRow 9 13, 115649633982600317600⟩, ⟨.privateRow 9 14, 189812218454229571200⟩, ⟨.privateRow 9 15, 289022459619081988800⟩, ⟨.privateRow 9 16, 504630775486819101120⟩, ⟨.privateRow 9 17, 744768544226386680000⟩, ⟨.privateRow 9 18, 275514107076028497600⟩, ⟨.privateRow 10 4, 1266408050911264800⟩, ⟨.privateRow 10 5, 2963394839132359632⟩, ⟨.privateRow 10 6, 10289565413654026500⟩, ⟨.privateRow 10 7, 25052854920201108000⟩, ⟨.privateRow 10 8, 48267415940413433400⟩, ⟨.privateRow 10 9, 84668423975210275200⟩, ⟨.privateRow 10 10, 140349672242240921460⟩, ⟨.privateRow 10 11, 220954878356360148000⟩, ⟨.privateRow 10 12, 250150768056388999800⟩, ⟨.privateRow 11 3, 47490301909172430000⟩, ⟨.privateRow 11 4, 37316823900185269440⟩, ⟨.privateRow 11 5, 98322513952694031000⟩, ⟨.privateRow 11 6, 88281488766422952000⟩, ⟨.privateRow 12 0, 97015902471595107000⟩, ⟨.privateRow 13 0, 67072722696411432000⟩, ⟨.hall 3 35, 6219470650030878240000⟩, ⟨.assumptionRow 21, 3916200910949600⟩]
  caps := #[0, 0, 202743575665993362000, 0, 6047172023390788290, 296710862323002400, 10875031225005646125, 19709800484531438400, 6467257237537277580, 16084700996771005984, 392586495782492088, 40017799506164684400, 298474837144573089000, 0] }

theorem case_52_39_21_checked :
    (Witness.linear .conditional case_52_39_21).check 52 39 21 = true := by
  change case_52_39_21.check 52 39 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_22 : Certificate := {
  objectiveScale := 398
  eta := 4032015000
  rows := #[⟨.assumptionRow 22, 307⟩]
  caps := #[0, 0, 1283091225, 486182970, 169317720, 56001550, 20646065, 7631844, 2643432, 969000, 1044572025, 997356360, 680356560, 390881205] }

theorem case_52_39_22_checked :
    (Witness.linear .conditional case_52_39_22).check 52 39 22 = true := by
  change case_52_39_22.check 52 39 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405, 4345965, 2414425] }

theorem case_52_39_23_checked :
    (Witness.linear .negative case_52_39_23).check 52 39 23 = true := by
  change case_52_39_23.check 52 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540] }

theorem case_52_39_24_checked :
    (Witness.linear .negative case_52_39_24).check 52 39 24 = true := by
  change case_52_39_24.check 52 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900] }

theorem case_52_39_25_checked :
    (Witness.linear .negative case_52_39_25).check 52 39 25 = true := by
  change case_52_39_25.check 52 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_40_1_checked :
    (Witness.rising).check 52 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_40_2_checked :
    (Witness.rising).check 52 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_40_3_checked :
    (Witness.rising).check 52 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_40_4_checked :
    (Witness.rising).check 52 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_40_5_checked :
    (Witness.rising).check 52 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_40_6_checked :
    (Witness.rising).check 52 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_40_7_checked :
    (Witness.rising).check 52 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_40_8_checked :
    (Witness.rising).check 52 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_40_9_checked :
    (Witness.rising).check 52 40 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_52_40_10_checked :
    (Witness.linear .positive case_52_40_10).check 52 40 10 = true := by
  change case_52_40_10.check 52 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_52_40_11_checked :
    (Witness.linear .positive case_52_40_11).check 52 40 11 = true := by
  change case_52_40_11.check 52 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_52_40_12_checked :
    (Witness.linear .positive case_52_40_12).check 52 40 12 = true := by
  change case_52_40_12.check 52 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_52_40_13_checked :
    (Witness.linear .positive case_52_40_13).check 52 40 13 = true := by
  change case_52_40_13.check 52 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_52_40_14_checked :
    (Witness.linear .positive case_52_40_14).check 52 40 14 = true := by
  change case_52_40_14.check 52 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_52_40_15_checked :
    (Witness.linear .positive case_52_40_15).check 52 40 15 = true := by
  change case_52_40_15.check 52 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_52_40_16_checked :
    (Witness.linear .positive case_52_40_16).check 52 40 16 = true := by
  change case_52_40_16.check 52 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_52_40_17_checked :
    (Witness.linear .positive case_52_40_17).check 52 40 17 = true := by
  change case_52_40_17.check 52 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_52_40_18_checked :
    (Witness.linear .positive case_52_40_18).check 52 40 18 = true := by
  change case_52_40_18.check 52 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_52_40_19_checked :
    (Witness.linear .positive case_52_40_19).check 52 40 19 = true := by
  change case_52_40_19.check 52 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_20 : Certificate := {
  objectiveScale := 5
  eta := 300230040
  rows := #[⟨.assumptionRow 20, 7⟩]
  caps := #[0, 0, 86843400, 25282635, 7413705, 2191555, 653752, 197030, 60078, 18564, 12746370, 10015005, 5525520] }

theorem case_52_40_20_checked :
    (Witness.linear .conditional case_52_40_20).check 52 40 20 = true := by
  change case_52_40_20.check 52 40 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_21 : Certificate := {
  objectiveScale := 935
  eta := 30186765840
  rows := #[⟨.assumptionRow 21, 954⟩]
  caps := #[0, 0, 9357376350, 2882500530, 884190840, 270489890, 88828553, 29951790, 9980700, 7047341910, 6343139985, 4066092030, 2188105920] }

theorem case_52_40_21_checked :
    (Witness.linear .conditional case_52_40_21).check 52 40 21 = true := by
  change case_52_40_21.check 52 40 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_22 : Certificate := {
  objectiveScale := 804
  eta := 7257627000
  rows := #[⟨.assumptionRow 22, 611⟩]
  caps := #[0, 0, 2366532675, 848544060, 307653060, 104311900, 36461095, 14048562, 4984536, 7583289750, 7276286325, 5007502500, 2916155970] }

theorem case_52_40_22_checked :
    (Witness.linear .conditional case_52_40_22).check 52 40 22 = true := by
  change case_52_40_22.check 52 40 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_23 : Certificate := {
  objectiveScale := 8
  eta := 194220
  rows := #[⟨.assumptionRow 23, 3⟩]
  caps := #[0, 0, 86710, 48070, 21252, 10857, 5852, 2337, 1428, 106073010, 105502725, 75847905, 46527390] }

theorem case_52_40_23_checked :
    (Witness.linear .conditional case_52_40_23).check 52 40 23 = true := by
  change case_52_40_23.check 52 40 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405] }

theorem case_52_40_24_checked :
    (Witness.linear .negative case_52_40_24).check 52 40 24 = true := by
  change case_52_40_24.check 52 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440] }

theorem case_52_40_25_checked :
    (Witness.linear .negative case_52_40_25).check 52 40 25 = true := by
  change case_52_40_25.check 52 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_40_26_checked :
    (Witness.linear .negative case_52_40_26).check 52 40 26 = true := by
  change case_52_40_26.check 52 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_41_1_checked :
    (Witness.rising).check 52 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_41_2_checked :
    (Witness.rising).check 52 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_41_3_checked :
    (Witness.rising).check 52 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_41_4_checked :
    (Witness.rising).check 52 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_41_5_checked :
    (Witness.rising).check 52 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_41_6_checked :
    (Witness.rising).check 52 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_41_7_checked :
    (Witness.rising).check 52 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_41_8_checked :
    (Witness.rising).check 52 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_41_9_checked :
    (Witness.rising).check 52 41 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_52_41_10_checked :
    (Witness.linear .positive case_52_41_10).check 52 41 10 = true := by
  change case_52_41_10.check 52 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_52_41_11_checked :
    (Witness.linear .positive case_52_41_11).check 52 41 11 = true := by
  change case_52_41_11.check 52 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_52_41_12_checked :
    (Witness.linear .positive case_52_41_12).check 52 41 12 = true := by
  change case_52_41_12.check 52 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_52_41_13_checked :
    (Witness.linear .positive case_52_41_13).check 52 41 13 = true := by
  change case_52_41_13.check 52 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_52_41_14_checked :
    (Witness.linear .positive case_52_41_14).check 52 41 14 = true := by
  change case_52_41_14.check 52 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_52_41_15_checked :
    (Witness.linear .positive case_52_41_15).check 52 41 15 = true := by
  change case_52_41_15.check 52 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_52_41_16_checked :
    (Witness.linear .positive case_52_41_16).check 52 41 16 = true := by
  change case_52_41_16.check 52 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_52_41_17_checked :
    (Witness.linear .positive case_52_41_17).check 52 41 17 = true := by
  change case_52_41_17.check 52 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_52_41_18_checked :
    (Witness.linear .positive case_52_41_18).check 52 41 18 = true := by
  change case_52_41_18.check 52 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_52_41_19_checked :
    (Witness.linear .positive case_52_41_19).check 52 41 19 = true := by
  change case_52_41_19.check 52 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_52_41_20_checked :
    (Witness.linear .positive case_52_41_20).check 52 41 20 = true := by
  change case_52_41_20.check 52 41 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_21 : Certificate := {
  objectiveScale := 993
  eta := 57562286760
  rows := #[⟨.assumptionRow 21, 1117⟩]
  caps := #[0, 0, 17847559320, 5515956600, 1701828765, 525038020, 162212215, 50253632, 27293640, 12639436560, 11015464980, 6831013800] }

theorem case_52_41_21_checked :
    (Witness.linear .conditional case_52_41_21).check 52 41 21 = true := by
  change case_52_41_21.check 52 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_22 : Certificate := {
  objectiveScale := 998
  eta := 32717630640
  rows := #[⟨.assumptionRow 22, 887⟩]
  caps := #[0, 0, 11267310840, 3731955045, 1203621510, 380882645, 127794095, 45272326, 27293640, 15971741880, 14932722630, 9997706355] }

theorem case_52_41_22_checked :
    (Witness.linear .conditional case_52_41_22).check 52 41 22 = true := by
  change case_52_41_22.check 52 41 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_23 : Certificate := {
  objectiveScale := 77
  eta := 35796150
  rows := #[⟨.assumptionRow 23, 39⟩]
  caps := #[0, 0, 12876435, 6364215, 2351635, 1157728, 442244, 216657, 1467033150, 2421690240, 1997398200, 1318759050] }

theorem case_52_41_23_checked :
    (Witness.linear .conditional case_52_41_23).check 52 41 23 = true := by
  change case_52_41_23.check 52 41 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825] }

theorem case_52_41_24_checked :
    (Witness.linear .negative case_52_41_24).check 52 41 24 = true := by
  change case_52_41_24.check 52 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845] }

theorem case_52_41_25_checked :
    (Witness.linear .negative case_52_41_25).check 52 41 25 = true := by
  change case_52_41_25.check 52 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_41_26_checked :
    (Witness.linear .negative case_52_41_26).check 52 41 26 = true := by
  change case_52_41_26.check 52 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_42_1_checked :
    (Witness.rising).check 52 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_42_2_checked :
    (Witness.rising).check 52 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_42_3_checked :
    (Witness.rising).check 52 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_42_4_checked :
    (Witness.rising).check 52 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_42_5_checked :
    (Witness.rising).check 52 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_42_6_checked :
    (Witness.rising).check 52 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_42_7_checked :
    (Witness.rising).check 52 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_42_8_checked :
    (Witness.rising).check 52 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_42_9_checked :
    (Witness.rising).check 52 42 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_52_42_10_checked :
    (Witness.linear .positive case_52_42_10).check 52 42 10 = true := by
  change case_52_42_10.check 52 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_52_42_11_checked :
    (Witness.linear .positive case_52_42_11).check 52 42 11 = true := by
  change case_52_42_11.check 52 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_52_42_12_checked :
    (Witness.linear .positive case_52_42_12).check 52 42 12 = true := by
  change case_52_42_12.check 52 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_52_42_13_checked :
    (Witness.linear .positive case_52_42_13).check 52 42 13 = true := by
  change case_52_42_13.check 52 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_52_42_14_checked :
    (Witness.linear .positive case_52_42_14).check 52 42 14 = true := by
  change case_52_42_14.check 52 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_52_42_15_checked :
    (Witness.linear .positive case_52_42_15).check 52 42 15 = true := by
  change case_52_42_15.check 52 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_52_42_16_checked :
    (Witness.linear .positive case_52_42_16).check 52 42 16 = true := by
  change case_52_42_16.check 52 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_52_42_17_checked :
    (Witness.linear .positive case_52_42_17).check 52 42 17 = true := by
  change case_52_42_17.check 52 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_52_42_18_checked :
    (Witness.linear .positive case_52_42_18).check 52 42 18 = true := by
  change case_52_42_18.check 52 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_52_42_19_checked :
    (Witness.linear .positive case_52_42_19).check 52 42 19 = true := by
  change case_52_42_19.check 52 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_52_42_20_checked :
    (Witness.linear .positive case_52_42_20).check 52 42 20 = true := by
  change case_52_42_20.check 52 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_21 : Certificate := {
  objectiveScale := 19
  eta := 2783951280
  rows := #[⟨.assumptionRow 21, 25⟩]
  caps := #[0, 0, 791515560, 235717800, 70525245, 21218535, 6426085, 1961256, 604010, 116618280, 225792840] }

theorem case_52_42_21_checked :
    (Witness.linear .conditional case_52_42_21).check 52 42 21 = true := by
  change case_52_42_21.check 52 42 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_22 : Certificate := {
  objectiveScale := 8
  eta := 238199040
  rows := #[⟨.assumptionRow 22, 7⟩]
  caps := #[0, 0, 76918440, 26403195, 8727810, 2812095, 889295, 326876, 463991880, 436698240, 295267560] }

theorem case_52_42_22_checked :
    (Witness.linear .conditional case_52_42_22).check 52 42 22 = true := by
  change case_52_42_22.check 52 42 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_23 : Certificate := {
  objectiveScale := 17
  eta := 33307950
  rows := #[⟨.assumptionRow 23, 10⟩]
  caps := #[0, 0, 13656825, 5278845, 2022735, 847550, 298034, 138567, 1275977670, 1255507440, 893246400] }

theorem case_52_42_23_checked :
    (Witness.linear .conditional case_52_42_23).check 52 42 23 = true := by
  change case_52_42_23.check 52 42 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 129644790, 129644790, 94287120] }

theorem case_52_42_24_checked :
    (Witness.linear .negative case_52_42_24).check 52 42 24 = true := by
  change case_52_42_24.check 52 42 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670] }

theorem case_52_42_25_checked :
    (Witness.linear .negative case_52_42_25).check 52 42 25 = true := by
  change case_52_42_25.check 52 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_42_26_checked :
    (Witness.linear .negative case_52_42_26).check 52 42 26 = true := by
  change case_52_42_26.check 52 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_42_27_checked :
    (Witness.linear .negative case_52_42_27).check 52 42 27 = true := by
  change case_52_42_27.check 52 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_43_1_checked :
    (Witness.rising).check 52 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_43_2_checked :
    (Witness.rising).check 52 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_43_3_checked :
    (Witness.rising).check 52 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_43_4_checked :
    (Witness.rising).check 52 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_43_5_checked :
    (Witness.rising).check 52 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_43_6_checked :
    (Witness.rising).check 52 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_43_7_checked :
    (Witness.rising).check 52 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_43_8_checked :
    (Witness.rising).check 52 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_43_9_checked :
    (Witness.rising).check 52 43 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_52_43_10_checked :
    (Witness.linear .positive case_52_43_10).check 52 43 10 = true := by
  change case_52_43_10.check 52 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_52_43_11_checked :
    (Witness.linear .positive case_52_43_11).check 52 43 11 = true := by
  change case_52_43_11.check 52 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_52_43_12_checked :
    (Witness.linear .positive case_52_43_12).check 52 43 12 = true := by
  change case_52_43_12.check 52 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_52_43_13_checked :
    (Witness.linear .positive case_52_43_13).check 52 43 13 = true := by
  change case_52_43_13.check 52 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_52_43_14_checked :
    (Witness.linear .positive case_52_43_14).check 52 43 14 = true := by
  change case_52_43_14.check 52 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_52_43_15_checked :
    (Witness.linear .positive case_52_43_15).check 52 43 15 = true := by
  change case_52_43_15.check 52 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_52_43_16_checked :
    (Witness.linear .positive case_52_43_16).check 52 43 16 = true := by
  change case_52_43_16.check 52 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_52_43_17_checked :
    (Witness.linear .positive case_52_43_17).check 52 43 17 = true := by
  change case_52_43_17.check 52 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_52_43_18_checked :
    (Witness.linear .positive case_52_43_18).check 52 43 18 = true := by
  change case_52_43_18.check 52 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_52_43_19_checked :
    (Witness.linear .positive case_52_43_19).check 52 43 19 = true := by
  change case_52_43_19.check 52 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_52_43_20_checked :
    (Witness.linear .positive case_52_43_20).check 52 43 20 = true := by
  change case_52_43_20.check 52 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_52_43_21_checked :
    (Witness.linear .positive case_52_43_21).check 52 43 21 = true := by
  change case_52_43_21.check 52 43 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_22 : Certificate := {
  objectiveScale := 838
  eta := 63735611880
  rows := #[⟨.assumptionRow 22, 823⟩]
  caps := #[0, 0, 19187428920, 6300488670, 2029404195, 645077550, 203167855, 63577382, 83349814080, 76389935880] }

theorem case_52_43_22_checked :
    (Witness.linear .conditional case_52_43_22).check 52 43 22 = true := by
  change case_52_43_22.check 52 43 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_23 : Certificate := {
  objectiveScale := 12
  eta := 22088430
  rows := #[⟨.assumptionRow 23, 7⟩]
  caps := #[0, 0, 8714355, 3502785, 1282710, 562925, 201894, 3295707030, 3247943160, 2319959400] }

theorem case_52_43_23_checked :
    (Witness.linear .conditional case_52_43_23).check 52 43 23 = true := by
  change case_52_43_23.check 52 43 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 477638700, 477638700, 347993910] }

theorem case_52_43_24_checked :
    (Witness.linear .negative case_52_43_24).check 52 43 24 = true := by
  change case_52_43_24.check 52 43 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 129644790] }

theorem case_52_43_25_checked :
    (Witness.linear .negative case_52_43_25).check 52 43 25 = true := by
  change case_52_43_25.check 52 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_43_26_checked :
    (Witness.linear .negative case_52_43_26).check 52 43 26 = true := by
  change case_52_43_26.check 52 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_43_27_checked :
    (Witness.linear .negative case_52_43_27).check 52 43 27 = true := by
  change case_52_43_27.check 52 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_43_28_checked :
    (Witness.linear .negative case_52_43_28).check 52 43 28 = true := by
  change case_52_43_28.check 52 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_44_1_checked :
    (Witness.rising).check 52 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_44_2_checked :
    (Witness.rising).check 52 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_44_3_checked :
    (Witness.rising).check 52 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_44_4_checked :
    (Witness.rising).check 52 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_44_5_checked :
    (Witness.rising).check 52 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_44_6_checked :
    (Witness.rising).check 52 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_44_7_checked :
    (Witness.rising).check 52 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_44_8_checked :
    (Witness.rising).check 52 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_44_9_checked :
    (Witness.rising).check 52 44 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_52_44_10_checked :
    (Witness.linear .positive case_52_44_10).check 52 44 10 = true := by
  change case_52_44_10.check 52 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_52_44_11_checked :
    (Witness.linear .positive case_52_44_11).check 52 44 11 = true := by
  change case_52_44_11.check 52 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_52_44_12_checked :
    (Witness.linear .positive case_52_44_12).check 52 44 12 = true := by
  change case_52_44_12.check 52 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_52_44_13_checked :
    (Witness.linear .positive case_52_44_13).check 52 44 13 = true := by
  change case_52_44_13.check 52 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_52_44_14_checked :
    (Witness.linear .positive case_52_44_14).check 52 44 14 = true := by
  change case_52_44_14.check 52 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_52_44_15_checked :
    (Witness.linear .positive case_52_44_15).check 52 44 15 = true := by
  change case_52_44_15.check 52 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_52_44_16_checked :
    (Witness.linear .positive case_52_44_16).check 52 44 16 = true := by
  change case_52_44_16.check 52 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_52_44_17_checked :
    (Witness.linear .positive case_52_44_17).check 52 44 17 = true := by
  change case_52_44_17.check 52 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_52_44_18_checked :
    (Witness.linear .positive case_52_44_18).check 52 44 18 = true := by
  change case_52_44_18.check 52 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_52_44_19_checked :
    (Witness.linear .positive case_52_44_19).check 52 44 19 = true := by
  change case_52_44_19.check 52 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_52_44_20_checked :
    (Witness.linear .positive case_52_44_20).check 52 44 20 = true := by
  change case_52_44_20.check 52 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_52_44_21_checked :
    (Witness.linear .positive case_52_44_21).check 52 44 21 = true := by
  change case_52_44_21.check 52 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_22 : Certificate := {
  objectiveScale := 7
  eta := 11774104110
  rows := #[⟨.assumptionRow 22, 12⟩]
  caps := #[0, 0, 3295707030, 927983760, 263011440, 75087525, 21611835, 6277505, 1842392] }

theorem case_52_44_22_checked :
    (Witness.linear .conditional case_52_44_22).check 52 44 22 = true := by
  change case_52_44_22.check 52 44 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_23 : Certificate := {
  objectiveScale := 15
  eta := 259451400
  rows := #[⟨.assumptionRow 23, 11⟩]
  caps := #[0, 0, 96768360, 34337160, 11396385, 4242810, 1562275, 6816586590, 6611884290] }

theorem case_52_44_23_checked :
    (Witness.linear .conditional case_52_44_23).check 52 44 23 = true := by
  change case_52_44_23.check 52 44 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 1767263190, 1767263190, 1289624490] }

theorem case_52_44_24_checked :
    (Witness.linear .negative case_52_44_24).check 52 44 24 = true := by
  change case_52_44_24.check 52 44 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 477638700] }

theorem case_52_44_25_checked :
    (Witness.linear .negative case_52_44_25).check 52 44 25 = true := by
  change case_52_44_25.check 52 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_44_26_checked :
    (Witness.linear .negative case_52_44_26).check 52 44 26 = true := by
  change case_52_44_26.check 52 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_44_27_checked :
    (Witness.linear .negative case_52_44_27).check 52 44 27 = true := by
  change case_52_44_27.check 52 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_44_28_checked :
    (Witness.linear .negative case_52_44_28).check 52 44 28 = true := by
  change case_52_44_28.check 52 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_45_1_checked :
    (Witness.rising).check 52 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_45_2_checked :
    (Witness.rising).check 52 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_45_3_checked :
    (Witness.rising).check 52 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_45_4_checked :
    (Witness.rising).check 52 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_45_5_checked :
    (Witness.rising).check 52 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_45_6_checked :
    (Witness.rising).check 52 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_45_7_checked :
    (Witness.rising).check 52 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_45_8_checked :
    (Witness.rising).check 52 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_45_9_checked :
    (Witness.rising).check 52 45 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_52_45_10_checked :
    (Witness.linear .positive case_52_45_10).check 52 45 10 = true := by
  change case_52_45_10.check 52 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_52_45_11_checked :
    (Witness.linear .positive case_52_45_11).check 52 45 11 = true := by
  change case_52_45_11.check 52 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_52_45_12_checked :
    (Witness.linear .positive case_52_45_12).check 52 45 12 = true := by
  change case_52_45_12.check 52 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_52_45_13_checked :
    (Witness.linear .positive case_52_45_13).check 52 45 13 = true := by
  change case_52_45_13.check 52 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_52_45_14_checked :
    (Witness.linear .positive case_52_45_14).check 52 45 14 = true := by
  change case_52_45_14.check 52 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_52_45_15_checked :
    (Witness.linear .positive case_52_45_15).check 52 45 15 = true := by
  change case_52_45_15.check 52 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_52_45_16_checked :
    (Witness.linear .positive case_52_45_16).check 52 45 16 = true := by
  change case_52_45_16.check 52 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_52_45_17_checked :
    (Witness.linear .positive case_52_45_17).check 52 45 17 = true := by
  change case_52_45_17.check 52 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_52_45_18_checked :
    (Witness.linear .positive case_52_45_18).check 52 45 18 = true := by
  change case_52_45_18.check 52 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_52_45_19_checked :
    (Witness.linear .positive case_52_45_19).check 52 45 19 = true := by
  change case_52_45_19.check 52 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_52_45_20_checked :
    (Witness.linear .positive case_52_45_20).check 52 45 20 = true := by
  change case_52_45_20.check 52 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_52_45_21_checked :
    (Witness.linear .positive case_52_45_21).check 52 45 21 = true := by
  change case_52_45_21.check 52 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_52_45_22_checked :
    (Witness.linear .positive case_52_45_22).check 52 45 22 = true := by
  change case_52_45_22.check 52 45 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_23 : Certificate := {
  objectiveScale := 992
  eta := 76109340000
  rows := #[⟨.assumptionRow 23, 845⟩]
  caps := #[0, 0, 24514651200, 7701148650, 2541079905, 890173830, 492957660, 769298348250] }

theorem case_52_45_23_checked :
    (Witness.linear .conditional case_52_45_23).check 52 45 23 = true := by
  change case_52_45_23.check 52 45 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 6564120420, 6564120420, 4796857230] }

theorem case_52_45_24_checked :
    (Witness.linear .negative case_52_45_24).check 52 45 24 = true := by
  change case_52_45_24.check 52 45 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 1767263190] }

theorem case_52_45_25_checked :
    (Witness.linear .negative case_52_45_25).check 52 45 25 = true := by
  change case_52_45_25.check 52 45 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_45_26_checked :
    (Witness.linear .negative case_52_45_26).check 52 45 26 = true := by
  change case_52_45_26.check 52 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_45_27_checked :
    (Witness.linear .negative case_52_45_27).check 52 45 27 = true := by
  change case_52_45_27.check 52 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_45_28_checked :
    (Witness.linear .negative case_52_45_28).check 52 45 28 = true := by
  change case_52_45_28.check 52 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_52_45_29_checked :
    (Witness.linear .negative case_52_45_29).check 52 45 29 = true := by
  change case_52_45_29.check 52 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_46_1_checked :
    (Witness.rising).check 52 46 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_46_2_checked :
    (Witness.rising).check 52 46 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_46_3_checked :
    (Witness.rising).check 52 46 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_46_4_checked :
    (Witness.rising).check 52 46 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_46_5_checked :
    (Witness.rising).check 52 46 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_46_6_checked :
    (Witness.rising).check 52 46 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_46_7_checked :
    (Witness.rising).check 52 46 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_46_8_checked :
    (Witness.rising).check 52 46 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_46_9_checked :
    (Witness.rising).check 52 46 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_52_46_10_checked :
    (Witness.linear .positive case_52_46_10).check 52 46 10 = true := by
  change case_52_46_10.check 52 46 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_52_46_11_checked :
    (Witness.linear .positive case_52_46_11).check 52 46 11 = true := by
  change case_52_46_11.check 52 46 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_52_46_12_checked :
    (Witness.linear .positive case_52_46_12).check 52 46 12 = true := by
  change case_52_46_12.check 52 46 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_52_46_13_checked :
    (Witness.linear .positive case_52_46_13).check 52 46 13 = true := by
  change case_52_46_13.check 52 46 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_52_46_14_checked :
    (Witness.linear .positive case_52_46_14).check 52 46 14 = true := by
  change case_52_46_14.check 52 46 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_52_46_15_checked :
    (Witness.linear .positive case_52_46_15).check 52 46 15 = true := by
  change case_52_46_15.check 52 46 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_52_46_16_checked :
    (Witness.linear .positive case_52_46_16).check 52 46 16 = true := by
  change case_52_46_16.check 52 46 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_52_46_17_checked :
    (Witness.linear .positive case_52_46_17).check 52 46 17 = true := by
  change case_52_46_17.check 52 46 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_52_46_18_checked :
    (Witness.linear .positive case_52_46_18).check 52 46 18 = true := by
  change case_52_46_18.check 52 46 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_52_46_19_checked :
    (Witness.linear .positive case_52_46_19).check 52 46 19 = true := by
  change case_52_46_19.check 52 46 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_52_46_20_checked :
    (Witness.linear .positive case_52_46_20).check 52 46 20 = true := by
  change case_52_46_20.check 52 46 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_52_46_21_checked :
    (Witness.linear .positive case_52_46_21).check 52 46 21 = true := by
  change case_52_46_21.check 52 46 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_52_46_22_checked :
    (Witness.linear .positive case_52_46_22).check 52 46 22 = true := by
  change case_52_46_22.check 52 46 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670] }

theorem case_52_46_23_checked :
    (Witness.linear .positive case_52_46_23).check 52 46 23 = true := by
  change case_52_46_23.check 52 46 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 24466267020, 24466267020, 17902146600] }

theorem case_52_46_24_checked :
    (Witness.linear .negative case_52_46_24).check 52 46 24 = true := by
  change case_52_46_24.check 52 46 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 6564120420] }

theorem case_52_46_25_checked :
    (Witness.linear .negative case_52_46_25).check 52 46 25 = true := by
  change case_52_46_25.check 52 46 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_52_46_26_checked :
    (Witness.linear .negative case_52_46_26).check 52 46 26 = true := by
  change case_52_46_26.check 52 46 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_52_46_27_checked :
    (Witness.linear .negative case_52_46_27).check 52 46 27 = true := by
  change case_52_46_27.check 52 46 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_52_46_28_checked :
    (Witness.linear .negative case_52_46_28).check 52 46 28 = true := by
  change case_52_46_28.check 52 46 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_52_46_29_checked :
    (Witness.linear .negative case_52_46_29).check 52 46 29 = true := by
  change case_52_46_29.check 52 46 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_46_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_52_46_30_checked :
    (Witness.linear .negative case_52_46_30).check 52 46 30 = true := by
  change case_52_46_30.check 52 46 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_47_1_checked :
    (Witness.rising).check 52 47 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_47_2_checked :
    (Witness.rising).check 52 47 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_47_3_checked :
    (Witness.rising).check 52 47 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_47_4_checked :
    (Witness.rising).check 52 47 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_47_5_checked :
    (Witness.rising).check 52 47 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_47_6_checked :
    (Witness.rising).check 52 47 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_47_7_checked :
    (Witness.rising).check 52 47 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_47_8_checked :
    (Witness.rising).check 52 47 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_47_9_checked :
    (Witness.rising).check 52 47 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_52_47_10_checked :
    (Witness.linear .positive case_52_47_10).check 52 47 10 = true := by
  change case_52_47_10.check 52 47 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_52_47_11_checked :
    (Witness.linear .positive case_52_47_11).check 52 47 11 = true := by
  change case_52_47_11.check 52 47 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_52_47_12_checked :
    (Witness.linear .positive case_52_47_12).check 52 47 12 = true := by
  change case_52_47_12.check 52 47 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_52_47_13_checked :
    (Witness.linear .positive case_52_47_13).check 52 47 13 = true := by
  change case_52_47_13.check 52 47 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_52_47_14_checked :
    (Witness.linear .positive case_52_47_14).check 52 47 14 = true := by
  change case_52_47_14.check 52 47 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_52_47_15_checked :
    (Witness.linear .positive case_52_47_15).check 52 47 15 = true := by
  change case_52_47_15.check 52 47 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_52_47_16_checked :
    (Witness.linear .positive case_52_47_16).check 52 47 16 = true := by
  change case_52_47_16.check 52 47 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_52_47_17_checked :
    (Witness.linear .positive case_52_47_17).check 52 47 17 = true := by
  change case_52_47_17.check 52 47 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_52_47_18_checked :
    (Witness.linear .positive case_52_47_18).check 52 47 18 = true := by
  change case_52_47_18.check 52 47 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_52_47_19_checked :
    (Witness.linear .positive case_52_47_19).check 52 47 19 = true := by
  change case_52_47_19.check 52 47 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_52_47_20_checked :
    (Witness.linear .positive case_52_47_20).check 52 47 20 = true := by
  change case_52_47_20.check 52 47 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845] }

theorem case_52_47_21_checked :
    (Witness.linear .positive case_52_47_21).check 52 47 21 = true := by
  change case_52_47_21.check 52 47 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670] }

theorem case_52_47_22_checked :
    (Witness.linear .positive case_52_47_22).check 52 47 22 = true := by
  change case_52_47_22.check 52 47 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790] }

theorem case_52_47_23_checked :
    (Witness.linear .positive case_52_47_23).check 52 47 23 = true := by
  change case_52_47_23.check 52 47 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_24 : Certificate := {
  objectiveScale := 25
  eta := 1123300500
  rows := #[⟨.assumptionRow 24, 18⟩]
  caps := #[0, 0, 378658800, 129024480, 49034505, 16921905] }

theorem case_52_47_24_checked :
    (Witness.linear .conditional case_52_47_24).check 52 47 24 = true := by
  change case_52_47_24.check 52 47 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 24466267020] }

theorem case_52_47_25_checked :
    (Witness.linear .negative case_52_47_25).check 52 47 25 = true := by
  change case_52_47_25.check 52 47 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_52_47_26_checked :
    (Witness.linear .negative case_52_47_26).check 52 47 26 = true := by
  change case_52_47_26.check 52 47 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_52_47_27_checked :
    (Witness.linear .negative case_52_47_27).check 52 47 27 = true := by
  change case_52_47_27.check 52 47 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_52_47_28_checked :
    (Witness.linear .negative case_52_47_28).check 52 47 28 = true := by
  change case_52_47_28.check 52 47 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_52_47_29_checked :
    (Witness.linear .negative case_52_47_29).check 52 47 29 = true := by
  change case_52_47_29.check 52 47 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_47_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_52_47_30_checked :
    (Witness.linear .negative case_52_47_30).check 52 47 30 = true := by
  change case_52_47_30.check 52 47 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_48_1_checked :
    (Witness.rising).check 52 48 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_48_2_checked :
    (Witness.rising).check 52 48 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_48_3_checked :
    (Witness.rising).check 52 48 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_48_4_checked :
    (Witness.rising).check 52 48 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_48_5_checked :
    (Witness.rising).check 52 48 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_48_6_checked :
    (Witness.rising).check 52 48 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_48_7_checked :
    (Witness.rising).check 52 48 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_48_8_checked :
    (Witness.rising).check 52 48 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_48_9_checked :
    (Witness.rising).check 52 48 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_52_48_10_checked :
    (Witness.linear .positive case_52_48_10).check 52 48 10 = true := by
  change case_52_48_10.check 52 48 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_52_48_11_checked :
    (Witness.linear .positive case_52_48_11).check 52 48 11 = true := by
  change case_52_48_11.check 52 48 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_52_48_12_checked :
    (Witness.linear .positive case_52_48_12).check 52 48 12 = true := by
  change case_52_48_12.check 52 48 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_52_48_13_checked :
    (Witness.linear .positive case_52_48_13).check 52 48 13 = true := by
  change case_52_48_13.check 52 48 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_52_48_14_checked :
    (Witness.linear .positive case_52_48_14).check 52 48 14 = true := by
  change case_52_48_14.check 52 48 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_52_48_15_checked :
    (Witness.linear .positive case_52_48_15).check 52 48 15 = true := by
  change case_52_48_15.check 52 48 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_52_48_16_checked :
    (Witness.linear .positive case_52_48_16).check 52 48 16 = true := by
  change case_52_48_16.check 52 48 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_52_48_17_checked :
    (Witness.linear .positive case_52_48_17).check 52 48 17 = true := by
  change case_52_48_17.check 52 48 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_52_48_18_checked :
    (Witness.linear .positive case_52_48_18).check 52 48 18 = true := by
  change case_52_48_18.check 52 48 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_52_48_19_checked :
    (Witness.linear .positive case_52_48_19).check 52 48 19 = true := by
  change case_52_48_19.check 52 48 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_52_48_20_checked :
    (Witness.linear .positive case_52_48_20).check 52 48 20 = true := by
  change case_52_48_20.check 52 48 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_52_48_21_checked :
    (Witness.linear .positive case_52_48_21).check 52 48 21 = true := by
  change case_52_48_21.check 52 48 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790] }

theorem case_52_48_22_checked :
    (Witness.linear .positive case_52_48_22).check 52 48 22 = true := by
  change case_52_48_22.check 52 48 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700] }

theorem case_52_48_23_checked :
    (Witness.linear .positive case_52_48_23).check 52 48 23 = true := by
  change case_52_48_23.check 52 48 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190] }

theorem case_52_48_24_checked :
    (Witness.linear .positive case_52_48_24).check 52 48 24 = true := by
  change case_52_48_24.check 52 48 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 91482563640] }

theorem case_52_48_25_checked :
    (Witness.linear .negative case_52_48_25).check 52 48 25 = true := by
  change case_52_48_25.check 52 48 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_52_48_26_checked :
    (Witness.linear .negative case_52_48_26).check 52 48 26 = true := by
  change case_52_48_26.check 52 48 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_52_48_27_checked :
    (Witness.linear .negative case_52_48_27).check 52 48 27 = true := by
  change case_52_48_27.check 52 48 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_52_48_28_checked :
    (Witness.linear .negative case_52_48_28).check 52 48 28 = true := by
  change case_52_48_28.check 52 48 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_52_48_29_checked :
    (Witness.linear .negative case_52_48_29).check 52 48 29 = true := by
  change case_52_48_29.check 52 48 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_52_48_30_checked :
    (Witness.linear .negative case_52_48_30).check 52 48 30 = true := by
  change case_52_48_30.check 52 48 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_48_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_52_48_31_checked :
    (Witness.linear .negative case_52_48_31).check 52 48 31 = true := by
  change case_52_48_31.check 52 48 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_49_1_checked :
    (Witness.rising).check 52 49 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_49_2_checked :
    (Witness.rising).check 52 49 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_49_3_checked :
    (Witness.rising).check 52 49 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_49_4_checked :
    (Witness.rising).check 52 49 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_49_5_checked :
    (Witness.rising).check 52 49 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_49_6_checked :
    (Witness.rising).check 52 49 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_49_7_checked :
    (Witness.rising).check 52 49 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_49_8_checked :
    (Witness.rising).check 52 49 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_49_9_checked :
    (Witness.rising).check 52 49 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_52_49_10_checked :
    (Witness.linear .positive case_52_49_10).check 52 49 10 = true := by
  change case_52_49_10.check 52 49 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_52_49_11_checked :
    (Witness.linear .positive case_52_49_11).check 52 49 11 = true := by
  change case_52_49_11.check 52 49 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_52_49_12_checked :
    (Witness.linear .positive case_52_49_12).check 52 49 12 = true := by
  change case_52_49_12.check 52 49 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_52_49_13_checked :
    (Witness.linear .positive case_52_49_13).check 52 49 13 = true := by
  change case_52_49_13.check 52 49 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_52_49_14_checked :
    (Witness.linear .positive case_52_49_14).check 52 49 14 = true := by
  change case_52_49_14.check 52 49 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_52_49_15_checked :
    (Witness.linear .positive case_52_49_15).check 52 49 15 = true := by
  change case_52_49_15.check 52 49 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_52_49_16_checked :
    (Witness.linear .positive case_52_49_16).check 52 49 16 = true := by
  change case_52_49_16.check 52 49 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_52_49_17_checked :
    (Witness.linear .positive case_52_49_17).check 52 49 17 = true := by
  change case_52_49_17.check 52 49 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_52_49_18_checked :
    (Witness.linear .positive case_52_49_18).check 52 49 18 = true := by
  change case_52_49_18.check 52 49 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_52_49_19_checked :
    (Witness.linear .positive case_52_49_19).check 52 49 19 = true := by
  change case_52_49_19.check 52 49 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_52_49_20_checked :
    (Witness.linear .positive case_52_49_20).check 52 49 20 = true := by
  change case_52_49_20.check 52 49 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_52_49_21_checked :
    (Witness.linear .positive case_52_49_21).check 52 49 21 = true := by
  change case_52_49_21.check 52 49 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700] }

theorem case_52_49_22_checked :
    (Witness.linear .positive case_52_49_22).check 52 49 22 = true := by
  change case_52_49_22.check 52 49 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190] }

theorem case_52_49_23_checked :
    (Witness.linear .positive case_52_49_23).check 52 49 23 = true := by
  change case_52_49_23.check 52 49 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420] }

theorem case_52_49_24_checked :
    (Witness.linear .positive case_52_49_24).check 52 49 24 = true := by
  change case_52_49_24.check 52 49 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 343059613650] }

theorem case_52_49_25_checked :
    (Witness.linear .negative case_52_49_25).check 52 49 25 = true := by
  change case_52_49_25.check 52 49 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_52_49_26_checked :
    (Witness.linear .negative case_52_49_26).check 52 49 26 = true := by
  change case_52_49_26.check 52 49 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_52_49_27_checked :
    (Witness.linear .negative case_52_49_27).check 52 49 27 = true := by
  change case_52_49_27.check 52 49 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_52_49_28_checked :
    (Witness.linear .negative case_52_49_28).check 52 49 28 = true := by
  change case_52_49_28.check 52 49 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_52_49_29_checked :
    (Witness.linear .negative case_52_49_29).check 52 49 29 = true := by
  change case_52_49_29.check 52 49 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_52_49_30_checked :
    (Witness.linear .negative case_52_49_30).check 52 49 30 = true := by
  change case_52_49_30.check 52 49 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_52_49_31_checked :
    (Witness.linear .negative case_52_49_31).check 52 49 31 = true := by
  change case_52_49_31.check 52 49 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_49_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_52_49_32_checked :
    (Witness.linear .negative case_52_49_32).check 52 49 32 = true := by
  change case_52_49_32.check 52 49 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_50_1_checked :
    (Witness.rising).check 52 50 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_50_2_checked :
    (Witness.rising).check 52 50 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_50_3_checked :
    (Witness.rising).check 52 50 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_50_4_checked :
    (Witness.rising).check 52 50 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_50_5_checked :
    (Witness.rising).check 52 50 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_50_6_checked :
    (Witness.rising).check 52 50 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_50_7_checked :
    (Witness.rising).check 52 50 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_50_8_checked :
    (Witness.rising).check 52 50 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_52_50_9_checked :
    (Witness.linear .positive case_52_50_9).check 52 50 9 = true := by
  change case_52_50_9.check 52 50 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_52_50_10_checked :
    (Witness.linear .positive case_52_50_10).check 52 50 10 = true := by
  change case_52_50_10.check 52 50 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_52_50_11_checked :
    (Witness.linear .positive case_52_50_11).check 52 50 11 = true := by
  change case_52_50_11.check 52 50 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_52_50_12_checked :
    (Witness.linear .positive case_52_50_12).check 52 50 12 = true := by
  change case_52_50_12.check 52 50 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_52_50_13_checked :
    (Witness.linear .positive case_52_50_13).check 52 50 13 = true := by
  change case_52_50_13.check 52 50 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_52_50_14_checked :
    (Witness.linear .positive case_52_50_14).check 52 50 14 = true := by
  change case_52_50_14.check 52 50 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_52_50_15_checked :
    (Witness.linear .positive case_52_50_15).check 52 50 15 = true := by
  change case_52_50_15.check 52 50 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_52_50_16_checked :
    (Witness.linear .positive case_52_50_16).check 52 50 16 = true := by
  change case_52_50_16.check 52 50 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_52_50_17_checked :
    (Witness.linear .positive case_52_50_17).check 52 50 17 = true := by
  change case_52_50_17.check 52 50 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_52_50_18_checked :
    (Witness.linear .positive case_52_50_18).check 52 50 18 = true := by
  change case_52_50_18.check 52 50 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_52_50_19_checked :
    (Witness.linear .positive case_52_50_19).check 52 50 19 = true := by
  change case_52_50_19.check 52 50 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_52_50_20_checked :
    (Witness.linear .positive case_52_50_20).check 52 50 20 = true := by
  change case_52_50_20.check 52 50 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_52_50_21_checked :
    (Witness.linear .positive case_52_50_21).check 52 50 21 = true := by
  change case_52_50_21.check 52 50 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_52_50_22_checked :
    (Witness.linear .positive case_52_50_22).check 52 50 22 = true := by
  change case_52_50_22.check 52 50 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420] }

theorem case_52_50_23_checked :
    (Witness.linear .positive case_52_50_23).check 52 50 23 = true := by
  change case_52_50_23.check 52 50 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020] }

theorem case_52_50_24_checked :
    (Witness.linear .positive case_52_50_24).check 52 50 24 = true := by
  change case_52_50_24.check 52 50 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640] }

theorem case_52_50_25_checked :
    (Witness.linear .positive case_52_50_25).check 52 50 25 = true := by
  change case_52_50_25.check 52 50 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_52_50_26_checked :
    (Witness.linear .negative case_52_50_26).check 52 50 26 = true := by
  change case_52_50_26.check 52 50 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_52_50_27_checked :
    (Witness.linear .negative case_52_50_27).check 52 50 27 = true := by
  change case_52_50_27.check 52 50 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_52_50_28_checked :
    (Witness.linear .negative case_52_50_28).check 52 50 28 = true := by
  change case_52_50_28.check 52 50 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_52_50_29_checked :
    (Witness.linear .negative case_52_50_29).check 52 50 29 = true := by
  change case_52_50_29.check 52 50 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_52_50_30_checked :
    (Witness.linear .negative case_52_50_30).check 52 50 30 = true := by
  change case_52_50_30.check 52 50 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_52_50_31_checked :
    (Witness.linear .negative case_52_50_31).check 52 50 31 = true := by
  change case_52_50_31.check 52 50 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_50_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_52_50_32_checked :
    (Witness.linear .negative case_52_50_32).check 52 50 32 = true := by
  change case_52_50_32.check 52 50 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_51_1_checked :
    (Witness.rising).check 52 51 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_51_2_checked :
    (Witness.rising).check 52 51 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_51_3_checked :
    (Witness.rising).check 52 51 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_51_4_checked :
    (Witness.rising).check 52 51 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_51_5_checked :
    (Witness.rising).check 52 51 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_51_6_checked :
    (Witness.rising).check 52 51 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_51_7_checked :
    (Witness.rising).check 52 51 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_52_51_8_checked :
    (Witness.rising).check 52 51 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_9_checked :
    (Witness.linear .positive case_52_51_9).check 52 51 9 = true := by
  change case_52_51_9.check 52 51 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_10_checked :
    (Witness.linear .positive case_52_51_10).check 52 51 10 = true := by
  change case_52_51_10.check 52 51 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_11_checked :
    (Witness.linear .positive case_52_51_11).check 52 51 11 = true := by
  change case_52_51_11.check 52 51 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_12_checked :
    (Witness.linear .positive case_52_51_12).check 52 51 12 = true := by
  change case_52_51_12.check 52 51 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_13_checked :
    (Witness.linear .positive case_52_51_13).check 52 51 13 = true := by
  change case_52_51_13.check 52 51 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_14_checked :
    (Witness.linear .positive case_52_51_14).check 52 51 14 = true := by
  change case_52_51_14.check 52 51 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_15_checked :
    (Witness.linear .positive case_52_51_15).check 52 51 15 = true := by
  change case_52_51_15.check 52 51 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_16_checked :
    (Witness.linear .positive case_52_51_16).check 52 51 16 = true := by
  change case_52_51_16.check 52 51 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_17_checked :
    (Witness.linear .positive case_52_51_17).check 52 51 17 = true := by
  change case_52_51_17.check 52 51 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_18_checked :
    (Witness.linear .positive case_52_51_18).check 52 51 18 = true := by
  change case_52_51_18.check 52 51 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_19_checked :
    (Witness.linear .positive case_52_51_19).check 52 51 19 = true := by
  change case_52_51_19.check 52 51 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_20_checked :
    (Witness.linear .positive case_52_51_20).check 52 51 20 = true := by
  change case_52_51_20.check 52 51 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_21_checked :
    (Witness.linear .positive case_52_51_21).check 52 51 21 = true := by
  change case_52_51_21.check 52 51 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_22_checked :
    (Witness.linear .positive case_52_51_22).check 52 51 22 = true := by
  change case_52_51_22.check 52 51 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_23_checked :
    (Witness.linear .positive case_52_51_23).check 52 51 23 = true := by
  change case_52_51_23.check 52 51 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_24_checked :
    (Witness.linear .positive case_52_51_24).check 52 51 24 = true := by
  change case_52_51_24.check 52 51 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_25_checked :
    (Witness.linear .positive case_52_51_25).check 52 51 25 = true := by
  change case_52_51_25.check 52 51 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_26_checked :
    (Witness.linear .negative case_52_51_26).check 52 51 26 = true := by
  change case_52_51_26.check 52 51 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_27_checked :
    (Witness.linear .negative case_52_51_27).check 52 51 27 = true := by
  change case_52_51_27.check 52 51 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_28_checked :
    (Witness.linear .negative case_52_51_28).check 52 51 28 = true := by
  change case_52_51_28.check 52 51 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_29_checked :
    (Witness.linear .negative case_52_51_29).check 52 51 29 = true := by
  change case_52_51_29.check 52 51 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_30_checked :
    (Witness.linear .negative case_52_51_30).check 52 51 30 = true := by
  change case_52_51_30.check 52 51 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_31_checked :
    (Witness.linear .negative case_52_51_31).check 52 51 31 = true := by
  change case_52_51_31.check 52 51 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_32_checked :
    (Witness.linear .negative case_52_51_32).check 52 51 32 = true := by
  change case_52_51_32.check 52 51 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_52_51_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_52_51_33_checked :
    (Witness.linear .negative case_52_51_33).check 52 51 33 = true := by
  change case_52_51_33.check 52 51 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_52 (a k : ℕ) (h : Domain 52 a k) :
    ∃ w : Witness, w.check 52 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 26 ≤ a := by omega
  have haHi : a ≤ 51 := by omega
  interval_cases a

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_26_1_checked⟩

    · exact ⟨Witness.rising, case_52_26_2_checked⟩

    · exact ⟨Witness.rising, case_52_26_3_checked⟩

    · exact ⟨Witness.rising, case_52_26_4_checked⟩

    · exact ⟨Witness.rising, case_52_26_5_checked⟩

    · exact ⟨Witness.rising, case_52_26_6_checked⟩

    · exact ⟨Witness.rising, case_52_26_7_checked⟩

    · exact ⟨Witness.rising, case_52_26_8_checked⟩

    · exact ⟨Witness.rising, case_52_26_9_checked⟩

    · exact ⟨Witness.rising, case_52_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_26_11, case_52_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_26_12, case_52_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_26_13, case_52_26_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_26_14, case_52_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_52_26_15, case_52_26_15_checked⟩

    · exact ⟨Witness.linear .conditional case_52_26_16, case_52_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_27_1_checked⟩

    · exact ⟨Witness.rising, case_52_27_2_checked⟩

    · exact ⟨Witness.rising, case_52_27_3_checked⟩

    · exact ⟨Witness.rising, case_52_27_4_checked⟩

    · exact ⟨Witness.rising, case_52_27_5_checked⟩

    · exact ⟨Witness.rising, case_52_27_6_checked⟩

    · exact ⟨Witness.rising, case_52_27_7_checked⟩

    · exact ⟨Witness.rising, case_52_27_8_checked⟩

    · exact ⟨Witness.rising, case_52_27_9_checked⟩

    · exact ⟨Witness.rising, case_52_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_27_11, case_52_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_27_12, case_52_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_27_13, case_52_27_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_27_14, case_52_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_52_27_15, case_52_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_52_27_16, case_52_27_16_checked⟩

    · exact ⟨Witness.linear .conditional case_52_27_17, case_52_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_28_1_checked⟩

    · exact ⟨Witness.rising, case_52_28_2_checked⟩

    · exact ⟨Witness.rising, case_52_28_3_checked⟩

    · exact ⟨Witness.rising, case_52_28_4_checked⟩

    · exact ⟨Witness.rising, case_52_28_5_checked⟩

    · exact ⟨Witness.rising, case_52_28_6_checked⟩

    · exact ⟨Witness.rising, case_52_28_7_checked⟩

    · exact ⟨Witness.rising, case_52_28_8_checked⟩

    · exact ⟨Witness.rising, case_52_28_9_checked⟩

    · exact ⟨Witness.rising, case_52_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_28_11, case_52_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_28_12, case_52_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_28_13, case_52_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_28_14, case_52_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_52_28_15, case_52_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_52_28_16, case_52_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_52_28_17, case_52_28_17_checked⟩

    · exact ⟨Witness.linear .conditional case_52_28_18, case_52_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_29_1_checked⟩

    · exact ⟨Witness.rising, case_52_29_2_checked⟩

    · exact ⟨Witness.rising, case_52_29_3_checked⟩

    · exact ⟨Witness.rising, case_52_29_4_checked⟩

    · exact ⟨Witness.rising, case_52_29_5_checked⟩

    · exact ⟨Witness.rising, case_52_29_6_checked⟩

    · exact ⟨Witness.rising, case_52_29_7_checked⟩

    · exact ⟨Witness.rising, case_52_29_8_checked⟩

    · exact ⟨Witness.rising, case_52_29_9_checked⟩

    · exact ⟨Witness.rising, case_52_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_29_11, case_52_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_29_12, case_52_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_29_13, case_52_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_29_14, case_52_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_52_29_15, case_52_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_52_29_16, case_52_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_52_29_17, case_52_29_17_checked⟩

    · exact ⟨Witness.linear .conditional case_52_29_18, case_52_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_30_1_checked⟩

    · exact ⟨Witness.rising, case_52_30_2_checked⟩

    · exact ⟨Witness.rising, case_52_30_3_checked⟩

    · exact ⟨Witness.rising, case_52_30_4_checked⟩

    · exact ⟨Witness.rising, case_52_30_5_checked⟩

    · exact ⟨Witness.rising, case_52_30_6_checked⟩

    · exact ⟨Witness.rising, case_52_30_7_checked⟩

    · exact ⟨Witness.rising, case_52_30_8_checked⟩

    · exact ⟨Witness.rising, case_52_30_9_checked⟩

    · exact ⟨Witness.rising, case_52_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_30_11, case_52_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_30_12, case_52_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_30_13, case_52_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_30_14, case_52_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_30_15, case_52_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_52_30_16, case_52_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_52_30_17, case_52_30_17_checked⟩

    · exact ⟨Witness.linear .conditional case_52_30_18, case_52_30_18_checked⟩

    · exact ⟨Witness.linear .conditional case_52_30_19, case_52_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_31_1_checked⟩

    · exact ⟨Witness.rising, case_52_31_2_checked⟩

    · exact ⟨Witness.rising, case_52_31_3_checked⟩

    · exact ⟨Witness.rising, case_52_31_4_checked⟩

    · exact ⟨Witness.rising, case_52_31_5_checked⟩

    · exact ⟨Witness.rising, case_52_31_6_checked⟩

    · exact ⟨Witness.rising, case_52_31_7_checked⟩

    · exact ⟨Witness.rising, case_52_31_8_checked⟩

    · exact ⟨Witness.rising, case_52_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_31_10, case_52_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_31_11, case_52_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_31_12, case_52_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_31_13, case_52_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_31_14, case_52_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_31_15, case_52_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_52_31_16, case_52_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_52_31_17, case_52_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_52_31_18, case_52_31_18_checked⟩

    · exact ⟨Witness.linear .conditional case_52_31_19, case_52_31_19_checked⟩

    · exact ⟨Witness.linear .conditional case_52_31_20, case_52_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_32_1_checked⟩

    · exact ⟨Witness.rising, case_52_32_2_checked⟩

    · exact ⟨Witness.rising, case_52_32_3_checked⟩

    · exact ⟨Witness.rising, case_52_32_4_checked⟩

    · exact ⟨Witness.rising, case_52_32_5_checked⟩

    · exact ⟨Witness.rising, case_52_32_6_checked⟩

    · exact ⟨Witness.rising, case_52_32_7_checked⟩

    · exact ⟨Witness.rising, case_52_32_8_checked⟩

    · exact ⟨Witness.rising, case_52_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_32_10, case_52_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_32_11, case_52_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_32_12, case_52_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_32_13, case_52_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_32_14, case_52_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_32_15, case_52_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_52_32_16, case_52_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_52_32_17, case_52_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_52_32_18, case_52_32_18_checked⟩

    · exact ⟨Witness.linear .conditional case_52_32_19, case_52_32_19_checked⟩

    · exact ⟨Witness.linear .conditional case_52_32_20, case_52_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_33_1_checked⟩

    · exact ⟨Witness.rising, case_52_33_2_checked⟩

    · exact ⟨Witness.rising, case_52_33_3_checked⟩

    · exact ⟨Witness.rising, case_52_33_4_checked⟩

    · exact ⟨Witness.rising, case_52_33_5_checked⟩

    · exact ⟨Witness.rising, case_52_33_6_checked⟩

    · exact ⟨Witness.rising, case_52_33_7_checked⟩

    · exact ⟨Witness.rising, case_52_33_8_checked⟩

    · exact ⟨Witness.rising, case_52_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_33_10, case_52_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_33_11, case_52_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_33_12, case_52_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_33_13, case_52_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_33_14, case_52_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_33_15, case_52_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_33_16, case_52_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_52_33_17, case_52_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_52_33_18, case_52_33_18_checked⟩

    · exact ⟨Witness.linear .conditional case_52_33_19, case_52_33_19_checked⟩

    · exact ⟨Witness.linear .conditional case_52_33_20, case_52_33_20_checked⟩

    · exact ⟨Witness.linear .conditional case_52_33_21, case_52_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_34_1_checked⟩

    · exact ⟨Witness.rising, case_52_34_2_checked⟩

    · exact ⟨Witness.rising, case_52_34_3_checked⟩

    · exact ⟨Witness.rising, case_52_34_4_checked⟩

    · exact ⟨Witness.rising, case_52_34_5_checked⟩

    · exact ⟨Witness.rising, case_52_34_6_checked⟩

    · exact ⟨Witness.rising, case_52_34_7_checked⟩

    · exact ⟨Witness.rising, case_52_34_8_checked⟩

    · exact ⟨Witness.rising, case_52_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_34_10, case_52_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_34_11, case_52_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_34_12, case_52_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_34_13, case_52_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_34_14, case_52_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_34_15, case_52_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_34_16, case_52_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_52_34_17, case_52_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_52_34_18, case_52_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_52_34_19, case_52_34_19_checked⟩

    · exact ⟨Witness.linear .conditional case_52_34_20, case_52_34_20_checked⟩

    · exact ⟨Witness.linear .conditional case_52_34_21, case_52_34_21_checked⟩

    · exact ⟨Witness.linear .conditional case_52_34_22, case_52_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_35_1_checked⟩

    · exact ⟨Witness.rising, case_52_35_2_checked⟩

    · exact ⟨Witness.rising, case_52_35_3_checked⟩

    · exact ⟨Witness.rising, case_52_35_4_checked⟩

    · exact ⟨Witness.rising, case_52_35_5_checked⟩

    · exact ⟨Witness.rising, case_52_35_6_checked⟩

    · exact ⟨Witness.rising, case_52_35_7_checked⟩

    · exact ⟨Witness.rising, case_52_35_8_checked⟩

    · exact ⟨Witness.rising, case_52_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_35_10, case_52_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_35_11, case_52_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_35_12, case_52_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_35_13, case_52_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_35_14, case_52_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_35_15, case_52_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_35_16, case_52_35_16_checked⟩

    · exact ⟨Witness.linear .conditional case_52_35_17, case_52_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_52_35_18, case_52_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_52_35_19, case_52_35_19_checked⟩

    · exact ⟨Witness.linear .conditional case_52_35_20, case_52_35_20_checked⟩

    · exact ⟨Witness.linear .conditional case_52_35_21, case_52_35_21_checked⟩

    · exact ⟨Witness.linear .conditional case_52_35_22, case_52_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_36_1_checked⟩

    · exact ⟨Witness.rising, case_52_36_2_checked⟩

    · exact ⟨Witness.rising, case_52_36_3_checked⟩

    · exact ⟨Witness.rising, case_52_36_4_checked⟩

    · exact ⟨Witness.rising, case_52_36_5_checked⟩

    · exact ⟨Witness.rising, case_52_36_6_checked⟩

    · exact ⟨Witness.rising, case_52_36_7_checked⟩

    · exact ⟨Witness.rising, case_52_36_8_checked⟩

    · exact ⟨Witness.rising, case_52_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_36_10, case_52_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_36_11, case_52_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_36_12, case_52_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_36_13, case_52_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_36_14, case_52_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_36_15, case_52_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_36_16, case_52_36_16_checked⟩

    · exact ⟨Witness.linear .conditional case_52_36_17, case_52_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_52_36_18, case_52_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_52_36_19, case_52_36_19_checked⟩

    · exact ⟨Witness.linear .conditional case_52_36_20, case_52_36_20_checked⟩

    · exact ⟨Witness.linear .conditional case_52_36_21, case_52_36_21_checked⟩

    · exact ⟨Witness.linear .conditional case_52_36_22, case_52_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_52_36_23, case_52_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_37_1_checked⟩

    · exact ⟨Witness.rising, case_52_37_2_checked⟩

    · exact ⟨Witness.rising, case_52_37_3_checked⟩

    · exact ⟨Witness.rising, case_52_37_4_checked⟩

    · exact ⟨Witness.rising, case_52_37_5_checked⟩

    · exact ⟨Witness.rising, case_52_37_6_checked⟩

    · exact ⟨Witness.rising, case_52_37_7_checked⟩

    · exact ⟨Witness.rising, case_52_37_8_checked⟩

    · exact ⟨Witness.rising, case_52_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_37_10, case_52_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_37_11, case_52_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_37_12, case_52_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_37_13, case_52_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_37_14, case_52_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_37_15, case_52_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_37_16, case_52_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_37_17, case_52_37_17_checked⟩

    · exact ⟨Witness.linear .conditional case_52_37_18, case_52_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_52_37_19, case_52_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_52_37_20, case_52_37_20_checked⟩

    · exact ⟨Witness.linear .conditional case_52_37_21, case_52_37_21_checked⟩

    · exact ⟨Witness.linear .conditional case_52_37_22, case_52_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_52_37_23, case_52_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_52_37_24, case_52_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_38_1_checked⟩

    · exact ⟨Witness.rising, case_52_38_2_checked⟩

    · exact ⟨Witness.rising, case_52_38_3_checked⟩

    · exact ⟨Witness.rising, case_52_38_4_checked⟩

    · exact ⟨Witness.rising, case_52_38_5_checked⟩

    · exact ⟨Witness.rising, case_52_38_6_checked⟩

    · exact ⟨Witness.rising, case_52_38_7_checked⟩

    · exact ⟨Witness.rising, case_52_38_8_checked⟩

    · exact ⟨Witness.rising, case_52_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_38_10, case_52_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_38_11, case_52_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_38_12, case_52_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_38_13, case_52_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_38_14, case_52_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_38_15, case_52_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_38_16, case_52_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_38_17, case_52_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_38_18, case_52_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_52_38_19, case_52_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_52_38_20, case_52_38_20_checked⟩

    · exact ⟨Witness.linear .conditional case_52_38_21, case_52_38_21_checked⟩

    · exact ⟨Witness.linear .conditional case_52_38_22, case_52_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_52_38_23, case_52_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_52_38_24, case_52_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_39_1_checked⟩

    · exact ⟨Witness.rising, case_52_39_2_checked⟩

    · exact ⟨Witness.rising, case_52_39_3_checked⟩

    · exact ⟨Witness.rising, case_52_39_4_checked⟩

    · exact ⟨Witness.rising, case_52_39_5_checked⟩

    · exact ⟨Witness.rising, case_52_39_6_checked⟩

    · exact ⟨Witness.rising, case_52_39_7_checked⟩

    · exact ⟨Witness.rising, case_52_39_8_checked⟩

    · exact ⟨Witness.rising, case_52_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_39_10, case_52_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_39_11, case_52_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_39_12, case_52_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_39_13, case_52_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_39_14, case_52_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_39_15, case_52_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_39_16, case_52_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_39_17, case_52_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_39_18, case_52_39_18_checked⟩

    · exact ⟨Witness.linear .conditional case_52_39_19, case_52_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_52_39_20, case_52_39_20_checked⟩

    · exact ⟨Witness.linear .conditional case_52_39_21, case_52_39_21_checked⟩

    · exact ⟨Witness.linear .conditional case_52_39_22, case_52_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_52_39_23, case_52_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_52_39_24, case_52_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_52_39_25, case_52_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_40_1_checked⟩

    · exact ⟨Witness.rising, case_52_40_2_checked⟩

    · exact ⟨Witness.rising, case_52_40_3_checked⟩

    · exact ⟨Witness.rising, case_52_40_4_checked⟩

    · exact ⟨Witness.rising, case_52_40_5_checked⟩

    · exact ⟨Witness.rising, case_52_40_6_checked⟩

    · exact ⟨Witness.rising, case_52_40_7_checked⟩

    · exact ⟨Witness.rising, case_52_40_8_checked⟩

    · exact ⟨Witness.rising, case_52_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_40_10, case_52_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_40_11, case_52_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_40_12, case_52_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_40_13, case_52_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_40_14, case_52_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_40_15, case_52_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_40_16, case_52_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_40_17, case_52_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_40_18, case_52_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_40_19, case_52_40_19_checked⟩

    · exact ⟨Witness.linear .conditional case_52_40_20, case_52_40_20_checked⟩

    · exact ⟨Witness.linear .conditional case_52_40_21, case_52_40_21_checked⟩

    · exact ⟨Witness.linear .conditional case_52_40_22, case_52_40_22_checked⟩

    · exact ⟨Witness.linear .conditional case_52_40_23, case_52_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_52_40_24, case_52_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_52_40_25, case_52_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_40_26, case_52_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_41_1_checked⟩

    · exact ⟨Witness.rising, case_52_41_2_checked⟩

    · exact ⟨Witness.rising, case_52_41_3_checked⟩

    · exact ⟨Witness.rising, case_52_41_4_checked⟩

    · exact ⟨Witness.rising, case_52_41_5_checked⟩

    · exact ⟨Witness.rising, case_52_41_6_checked⟩

    · exact ⟨Witness.rising, case_52_41_7_checked⟩

    · exact ⟨Witness.rising, case_52_41_8_checked⟩

    · exact ⟨Witness.rising, case_52_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_41_10, case_52_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_41_11, case_52_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_41_12, case_52_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_41_13, case_52_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_41_14, case_52_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_41_15, case_52_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_41_16, case_52_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_41_17, case_52_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_41_18, case_52_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_41_19, case_52_41_19_checked⟩

    · exact ⟨Witness.linear .positive case_52_41_20, case_52_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_52_41_21, case_52_41_21_checked⟩

    · exact ⟨Witness.linear .conditional case_52_41_22, case_52_41_22_checked⟩

    · exact ⟨Witness.linear .conditional case_52_41_23, case_52_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_52_41_24, case_52_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_52_41_25, case_52_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_41_26, case_52_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_42_1_checked⟩

    · exact ⟨Witness.rising, case_52_42_2_checked⟩

    · exact ⟨Witness.rising, case_52_42_3_checked⟩

    · exact ⟨Witness.rising, case_52_42_4_checked⟩

    · exact ⟨Witness.rising, case_52_42_5_checked⟩

    · exact ⟨Witness.rising, case_52_42_6_checked⟩

    · exact ⟨Witness.rising, case_52_42_7_checked⟩

    · exact ⟨Witness.rising, case_52_42_8_checked⟩

    · exact ⟨Witness.rising, case_52_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_42_10, case_52_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_42_11, case_52_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_42_12, case_52_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_42_13, case_52_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_42_14, case_52_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_42_15, case_52_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_42_16, case_52_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_42_17, case_52_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_42_18, case_52_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_42_19, case_52_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_52_42_20, case_52_42_20_checked⟩

    · exact ⟨Witness.linear .conditional case_52_42_21, case_52_42_21_checked⟩

    · exact ⟨Witness.linear .conditional case_52_42_22, case_52_42_22_checked⟩

    · exact ⟨Witness.linear .conditional case_52_42_23, case_52_42_23_checked⟩

    · exact ⟨Witness.linear .negative case_52_42_24, case_52_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_52_42_25, case_52_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_42_26, case_52_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_52_42_27, case_52_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_43_1_checked⟩

    · exact ⟨Witness.rising, case_52_43_2_checked⟩

    · exact ⟨Witness.rising, case_52_43_3_checked⟩

    · exact ⟨Witness.rising, case_52_43_4_checked⟩

    · exact ⟨Witness.rising, case_52_43_5_checked⟩

    · exact ⟨Witness.rising, case_52_43_6_checked⟩

    · exact ⟨Witness.rising, case_52_43_7_checked⟩

    · exact ⟨Witness.rising, case_52_43_8_checked⟩

    · exact ⟨Witness.rising, case_52_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_10, case_52_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_11, case_52_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_12, case_52_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_13, case_52_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_14, case_52_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_15, case_52_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_16, case_52_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_17, case_52_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_18, case_52_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_19, case_52_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_20, case_52_43_20_checked⟩

    · exact ⟨Witness.linear .positive case_52_43_21, case_52_43_21_checked⟩

    · exact ⟨Witness.linear .conditional case_52_43_22, case_52_43_22_checked⟩

    · exact ⟨Witness.linear .conditional case_52_43_23, case_52_43_23_checked⟩

    · exact ⟨Witness.linear .negative case_52_43_24, case_52_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_52_43_25, case_52_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_43_26, case_52_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_52_43_27, case_52_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_52_43_28, case_52_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_44_1_checked⟩

    · exact ⟨Witness.rising, case_52_44_2_checked⟩

    · exact ⟨Witness.rising, case_52_44_3_checked⟩

    · exact ⟨Witness.rising, case_52_44_4_checked⟩

    · exact ⟨Witness.rising, case_52_44_5_checked⟩

    · exact ⟨Witness.rising, case_52_44_6_checked⟩

    · exact ⟨Witness.rising, case_52_44_7_checked⟩

    · exact ⟨Witness.rising, case_52_44_8_checked⟩

    · exact ⟨Witness.rising, case_52_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_10, case_52_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_11, case_52_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_12, case_52_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_13, case_52_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_14, case_52_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_15, case_52_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_16, case_52_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_17, case_52_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_18, case_52_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_19, case_52_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_20, case_52_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_52_44_21, case_52_44_21_checked⟩

    · exact ⟨Witness.linear .conditional case_52_44_22, case_52_44_22_checked⟩

    · exact ⟨Witness.linear .conditional case_52_44_23, case_52_44_23_checked⟩

    · exact ⟨Witness.linear .negative case_52_44_24, case_52_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_52_44_25, case_52_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_44_26, case_52_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_52_44_27, case_52_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_52_44_28, case_52_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_45_1_checked⟩

    · exact ⟨Witness.rising, case_52_45_2_checked⟩

    · exact ⟨Witness.rising, case_52_45_3_checked⟩

    · exact ⟨Witness.rising, case_52_45_4_checked⟩

    · exact ⟨Witness.rising, case_52_45_5_checked⟩

    · exact ⟨Witness.rising, case_52_45_6_checked⟩

    · exact ⟨Witness.rising, case_52_45_7_checked⟩

    · exact ⟨Witness.rising, case_52_45_8_checked⟩

    · exact ⟨Witness.rising, case_52_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_10, case_52_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_11, case_52_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_12, case_52_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_13, case_52_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_14, case_52_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_15, case_52_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_16, case_52_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_17, case_52_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_18, case_52_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_19, case_52_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_20, case_52_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_21, case_52_45_21_checked⟩

    · exact ⟨Witness.linear .positive case_52_45_22, case_52_45_22_checked⟩

    · exact ⟨Witness.linear .conditional case_52_45_23, case_52_45_23_checked⟩

    · exact ⟨Witness.linear .negative case_52_45_24, case_52_45_24_checked⟩

    · exact ⟨Witness.linear .negative case_52_45_25, case_52_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_45_26, case_52_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_52_45_27, case_52_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_52_45_28, case_52_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_52_45_29, case_52_45_29_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_46_1_checked⟩

    · exact ⟨Witness.rising, case_52_46_2_checked⟩

    · exact ⟨Witness.rising, case_52_46_3_checked⟩

    · exact ⟨Witness.rising, case_52_46_4_checked⟩

    · exact ⟨Witness.rising, case_52_46_5_checked⟩

    · exact ⟨Witness.rising, case_52_46_6_checked⟩

    · exact ⟨Witness.rising, case_52_46_7_checked⟩

    · exact ⟨Witness.rising, case_52_46_8_checked⟩

    · exact ⟨Witness.rising, case_52_46_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_10, case_52_46_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_11, case_52_46_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_12, case_52_46_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_13, case_52_46_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_14, case_52_46_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_15, case_52_46_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_16, case_52_46_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_17, case_52_46_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_18, case_52_46_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_19, case_52_46_19_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_20, case_52_46_20_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_21, case_52_46_21_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_22, case_52_46_22_checked⟩

    · exact ⟨Witness.linear .positive case_52_46_23, case_52_46_23_checked⟩

    · exact ⟨Witness.linear .negative case_52_46_24, case_52_46_24_checked⟩

    · exact ⟨Witness.linear .negative case_52_46_25, case_52_46_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_46_26, case_52_46_26_checked⟩

    · exact ⟨Witness.linear .negative case_52_46_27, case_52_46_27_checked⟩

    · exact ⟨Witness.linear .negative case_52_46_28, case_52_46_28_checked⟩

    · exact ⟨Witness.linear .negative case_52_46_29, case_52_46_29_checked⟩

    · exact ⟨Witness.linear .negative case_52_46_30, case_52_46_30_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_47_1_checked⟩

    · exact ⟨Witness.rising, case_52_47_2_checked⟩

    · exact ⟨Witness.rising, case_52_47_3_checked⟩

    · exact ⟨Witness.rising, case_52_47_4_checked⟩

    · exact ⟨Witness.rising, case_52_47_5_checked⟩

    · exact ⟨Witness.rising, case_52_47_6_checked⟩

    · exact ⟨Witness.rising, case_52_47_7_checked⟩

    · exact ⟨Witness.rising, case_52_47_8_checked⟩

    · exact ⟨Witness.rising, case_52_47_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_10, case_52_47_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_11, case_52_47_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_12, case_52_47_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_13, case_52_47_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_14, case_52_47_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_15, case_52_47_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_16, case_52_47_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_17, case_52_47_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_18, case_52_47_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_19, case_52_47_19_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_20, case_52_47_20_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_21, case_52_47_21_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_22, case_52_47_22_checked⟩

    · exact ⟨Witness.linear .positive case_52_47_23, case_52_47_23_checked⟩

    · exact ⟨Witness.linear .conditional case_52_47_24, case_52_47_24_checked⟩

    · exact ⟨Witness.linear .negative case_52_47_25, case_52_47_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_47_26, case_52_47_26_checked⟩

    · exact ⟨Witness.linear .negative case_52_47_27, case_52_47_27_checked⟩

    · exact ⟨Witness.linear .negative case_52_47_28, case_52_47_28_checked⟩

    · exact ⟨Witness.linear .negative case_52_47_29, case_52_47_29_checked⟩

    · exact ⟨Witness.linear .negative case_52_47_30, case_52_47_30_checked⟩

  · have hkHi : k ≤ 31 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_48_1_checked⟩

    · exact ⟨Witness.rising, case_52_48_2_checked⟩

    · exact ⟨Witness.rising, case_52_48_3_checked⟩

    · exact ⟨Witness.rising, case_52_48_4_checked⟩

    · exact ⟨Witness.rising, case_52_48_5_checked⟩

    · exact ⟨Witness.rising, case_52_48_6_checked⟩

    · exact ⟨Witness.rising, case_52_48_7_checked⟩

    · exact ⟨Witness.rising, case_52_48_8_checked⟩

    · exact ⟨Witness.rising, case_52_48_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_10, case_52_48_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_11, case_52_48_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_12, case_52_48_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_13, case_52_48_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_14, case_52_48_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_15, case_52_48_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_16, case_52_48_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_17, case_52_48_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_18, case_52_48_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_19, case_52_48_19_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_20, case_52_48_20_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_21, case_52_48_21_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_22, case_52_48_22_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_23, case_52_48_23_checked⟩

    · exact ⟨Witness.linear .positive case_52_48_24, case_52_48_24_checked⟩

    · exact ⟨Witness.linear .negative case_52_48_25, case_52_48_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_48_26, case_52_48_26_checked⟩

    · exact ⟨Witness.linear .negative case_52_48_27, case_52_48_27_checked⟩

    · exact ⟨Witness.linear .negative case_52_48_28, case_52_48_28_checked⟩

    · exact ⟨Witness.linear .negative case_52_48_29, case_52_48_29_checked⟩

    · exact ⟨Witness.linear .negative case_52_48_30, case_52_48_30_checked⟩

    · exact ⟨Witness.linear .negative case_52_48_31, case_52_48_31_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_49_1_checked⟩

    · exact ⟨Witness.rising, case_52_49_2_checked⟩

    · exact ⟨Witness.rising, case_52_49_3_checked⟩

    · exact ⟨Witness.rising, case_52_49_4_checked⟩

    · exact ⟨Witness.rising, case_52_49_5_checked⟩

    · exact ⟨Witness.rising, case_52_49_6_checked⟩

    · exact ⟨Witness.rising, case_52_49_7_checked⟩

    · exact ⟨Witness.rising, case_52_49_8_checked⟩

    · exact ⟨Witness.rising, case_52_49_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_10, case_52_49_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_11, case_52_49_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_12, case_52_49_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_13, case_52_49_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_14, case_52_49_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_15, case_52_49_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_16, case_52_49_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_17, case_52_49_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_18, case_52_49_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_19, case_52_49_19_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_20, case_52_49_20_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_21, case_52_49_21_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_22, case_52_49_22_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_23, case_52_49_23_checked⟩

    · exact ⟨Witness.linear .positive case_52_49_24, case_52_49_24_checked⟩

    · exact ⟨Witness.linear .negative case_52_49_25, case_52_49_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_49_26, case_52_49_26_checked⟩

    · exact ⟨Witness.linear .negative case_52_49_27, case_52_49_27_checked⟩

    · exact ⟨Witness.linear .negative case_52_49_28, case_52_49_28_checked⟩

    · exact ⟨Witness.linear .negative case_52_49_29, case_52_49_29_checked⟩

    · exact ⟨Witness.linear .negative case_52_49_30, case_52_49_30_checked⟩

    · exact ⟨Witness.linear .negative case_52_49_31, case_52_49_31_checked⟩

    · exact ⟨Witness.linear .negative case_52_49_32, case_52_49_32_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_50_1_checked⟩

    · exact ⟨Witness.rising, case_52_50_2_checked⟩

    · exact ⟨Witness.rising, case_52_50_3_checked⟩

    · exact ⟨Witness.rising, case_52_50_4_checked⟩

    · exact ⟨Witness.rising, case_52_50_5_checked⟩

    · exact ⟨Witness.rising, case_52_50_6_checked⟩

    · exact ⟨Witness.rising, case_52_50_7_checked⟩

    · exact ⟨Witness.rising, case_52_50_8_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_9, case_52_50_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_10, case_52_50_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_11, case_52_50_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_12, case_52_50_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_13, case_52_50_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_14, case_52_50_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_15, case_52_50_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_16, case_52_50_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_17, case_52_50_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_18, case_52_50_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_19, case_52_50_19_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_20, case_52_50_20_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_21, case_52_50_21_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_22, case_52_50_22_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_23, case_52_50_23_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_24, case_52_50_24_checked⟩

    · exact ⟨Witness.linear .positive case_52_50_25, case_52_50_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_50_26, case_52_50_26_checked⟩

    · exact ⟨Witness.linear .negative case_52_50_27, case_52_50_27_checked⟩

    · exact ⟨Witness.linear .negative case_52_50_28, case_52_50_28_checked⟩

    · exact ⟨Witness.linear .negative case_52_50_29, case_52_50_29_checked⟩

    · exact ⟨Witness.linear .negative case_52_50_30, case_52_50_30_checked⟩

    · exact ⟨Witness.linear .negative case_52_50_31, case_52_50_31_checked⟩

    · exact ⟨Witness.linear .negative case_52_50_32, case_52_50_32_checked⟩

  · have hkHi : k ≤ 33 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_52_51_1_checked⟩

    · exact ⟨Witness.rising, case_52_51_2_checked⟩

    · exact ⟨Witness.rising, case_52_51_3_checked⟩

    · exact ⟨Witness.rising, case_52_51_4_checked⟩

    · exact ⟨Witness.rising, case_52_51_5_checked⟩

    · exact ⟨Witness.rising, case_52_51_6_checked⟩

    · exact ⟨Witness.rising, case_52_51_7_checked⟩

    · exact ⟨Witness.rising, case_52_51_8_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_9, case_52_51_9_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_10, case_52_51_10_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_11, case_52_51_11_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_12, case_52_51_12_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_13, case_52_51_13_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_14, case_52_51_14_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_15, case_52_51_15_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_16, case_52_51_16_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_17, case_52_51_17_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_18, case_52_51_18_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_19, case_52_51_19_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_20, case_52_51_20_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_21, case_52_51_21_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_22, case_52_51_22_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_23, case_52_51_23_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_24, case_52_51_24_checked⟩

    · exact ⟨Witness.linear .positive case_52_51_25, case_52_51_25_checked⟩

    · exact ⟨Witness.linear .negative case_52_51_26, case_52_51_26_checked⟩

    · exact ⟨Witness.linear .negative case_52_51_27, case_52_51_27_checked⟩

    · exact ⟨Witness.linear .negative case_52_51_28, case_52_51_28_checked⟩

    · exact ⟨Witness.linear .negative case_52_51_29, case_52_51_29_checked⟩

    · exact ⟨Witness.linear .negative case_52_51_30, case_52_51_30_checked⟩

    · exact ⟨Witness.linear .negative case_52_51_31, case_52_51_31_checked⟩

    · exact ⟨Witness.linear .negative case_52_51_32, case_52_51_32_checked⟩

    · exact ⟨Witness.linear .negative case_52_51_33, case_52_51_33_checked⟩


#print axioms coverage_52
end ForestUnimodality.FiniteRows.FiniteData
