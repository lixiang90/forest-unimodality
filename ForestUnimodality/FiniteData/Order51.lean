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

theorem case_51_26_1_checked :
    (Witness.rising).check 51 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_26_2_checked :
    (Witness.rising).check 51 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_26_3_checked :
    (Witness.rising).check 51 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_26_4_checked :
    (Witness.rising).check 51 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_26_5_checked :
    (Witness.rising).check 51 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_26_6_checked :
    (Witness.rising).check 51 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_26_7_checked :
    (Witness.rising).check 51 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_26_8_checked :
    (Witness.rising).check 51 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_26_9_checked :
    (Witness.rising).check 51 26 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_26_10_checked :
    (Witness.rising).check 51 26 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_26_11 : Certificate := {
  objectiveScale := 74459758464000000
  eta := 25806512829461398594560
  rows := #[⟨.count 2, 6414145981033524814080⟩, ⟨.count 3, 1119577803911463536640⟩, ⟨.count 4, 157114233300000936960⟩, ⟨.count 5, 25476696751515609600⟩, ⟨.count 6, 4674696070605200640⟩, ⟨.count 7, 988323733629872640⟩, ⟨.count 8, 253416341956377600⟩, ⟨.count 9, 93569110876200960⟩, ⟨.count 10, 74390883187420800⟩, ⟨.count 12, 12163001545094400⟩, ⟨.path 11, 19209318687491625⟩, ⟨.path 12, 12182658921328896⟩, ⟨.privateRow 8 8, 4326980663940480⟩, ⟨.privateRow 9 5, 2822597613158400⟩, ⟨.privateRow 11 0, 739967118410520⟩, ⟨.hall 9 3, 135650349971136⟩, ⟨.hall 8 5, 52620350675200⟩, ⟨.hall 7 7, 37187800927200⟩, ⟨.hall 6 10, 23386091831424⟩, ⟨.hall 6 11, 13020911608320⟩, ⟨.hall 10 15, 430005105129600⟩, ⟨.hall 5 16, 1189063247623680⟩, ⟨.hall 9 16, 283297481026560⟩, ⟨.hall 4 21, 5838499861604766720⟩]
  caps := #[0, 15468570600906570840, 1988932109038093296, 236117189217605850, 16563958232698800, 0, 3945222443154960, 3456183666027204, 318008095721960, 406719175471560, 204979747315455, 0, 19657376234496, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_26_11_checked :
    (Witness.linear .positive case_51_26_11).check 51 26 11 = true := by
  change case_51_26_11.check 51 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_26_12 : Certificate := {
  objectiveScale := 171171000000
  eta := 82906978835640960
  rows := #[⟨.count 2, 22442223579375600⟩, ⟨.count 3, 4211556821952480⟩, ⟨.count 4, 711678981293280⟩, ⟨.count 5, 128180239387200⟩, ⟨.count 6, 25317587655360⟩, ⟨.count 7, 5631717611520⟩, ⟨.count 8, 1460074936320⟩, ⟨.count 9, 452055764160⟩, ⟨.count 10, 187637650200⟩, ⟨.count 11, 170814964320⟩, ⟨.path 12, 17310523230⟩, ⟨.path 13, 40222959777⟩, ⟨.privateRow 8 10, 86275509320⟩, ⟨.privateRow 8 11, 47460583170⟩, ⟨.privateRow 9 7, 20913984000⟩, ⟨.privateRow 9 8, 43671884256⟩, ⟨.privateRow 10 4, 4711679280⟩, ⟨.privateRow 10 5, 16085794725⟩, ⟨.privateRow 10 6, 5803630560⟩, ⟨.privateRow 11 2, 5782156380⟩, ⟨.privateRow 12 0, 5407634232⟩, ⟨.privateRow 13 0, 2875221360⟩, ⟨.privateRow 14 0, 2876462820⟩, ⟨.privateRow 15 0, 3426843420⟩, ⟨.privateRow 16 0, 5254638480⟩, ⟨.privateRow 17 0, 9432206784⟩, ⟨.privateRow 18 0, 20188288120⟩, ⟨.privateRow 19 0, 52378326000⟩, ⟨.privateRow 20 0, 165864699000⟩, ⟨.privateRow 21 0, 667881854640⟩, ⟨.privateRow 22 0, 2953718559792⟩, ⟨.privateRow 22 1, 870789669750⟩, ⟨.privateRow 23 0, 26564890191840⟩, ⟨.privateRow 24 0, 321162710909040⟩, ⟨.privateRow 25 0, 7895902746251520⟩, ⟨.hall 10 3, 447941340⟩, ⟨.hall 21 3, 111461077728⟩, ⟨.hall 22 3, 2298884728140⟩, ⟨.hall 20 4, 35384469120⟩, ⟨.hall 9 5, 186444720⟩, ⟨.hall 19 5, 9477982800⟩, ⟨.hall 8 6, 75490800⟩, ⟨.hall 8 7, 108424260⟩, ⟨.hall 18 7, 18332414100⟩, ⟨.hall 17 8, 7966678720⟩, ⟨.hall 7 9, 179509932⟩, ⟨.hall 14 9, 50324274⟩, ⟨.hall 16 9, 4486049568⟩, ⟨.hall 15 10, 2941029000⟩, ⟨.hall 6 12, 319286583⟩, ⟨.hall 6 13, 179509473⟩, ⟨.hall 11 14, 1476178704⟩, ⟨.hall 5 20, 33691069526400⟩, ⟨.hall 4 21, 32349044604240⟩]
  caps := #[0, 0, 7060086201168, 531541072062, 0, 83987852130, 11972555595, 6124788810, 4877038166, 0, 2255944005, 356035680, 946917972, 163528497, 0, 0, 1317580992, 0, 9143574440, 8979141600, 0, 725381616960, 0, 14559603278220, 54832657960080, 0] }

theorem case_51_26_12_checked :
    (Witness.linear .positive case_51_26_12).check 51 26 12 = true := by
  change case_51_26_12.check 51 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_26_13 : Certificate := {
  objectiveScale := 189189000000
  eta := 140998263325920000
  rows := #[⟨.count 2, 45542439054272160⟩, ⟨.count 3, 11715116574601440⟩, ⟨.count 4, 2077634488849920⟩, ⟨.count 5, 394094524824000⟩, ⟨.count 6, 80490821130720⟩, ⟨.count 7, 17657781261120⟩, ⟨.count 8, 4484515875840⟩, ⟨.count 9, 1262995493760⟩, ⟨.count 10, 431350920000⟩, ⟨.count 11, 189794404800⟩, ⟨.count 12, 189794404800⟩, ⟨.path 14, 52669053360⟩, ⟨.path 15, 1731612960⟩, ⟨.privateRow 5 21, 19426073546880⟩, ⟨.privateRow 9 9, 66800814080⟩, ⟨.privateRow 9 10, 124420776480⟩, ⟨.privateRow 9 11, 40204644480⟩, ⟨.privateRow 10 6, 8940728160⟩, ⟨.privateRow 10 7, 42099849792⟩, ⟨.privateRow 10 8, 58663725120⟩, ⟨.privateRow 11 4, 12029897880⟩, ⟨.privateRow 11 5, 19711429920⟩, ⟨.privateRow 12 2, 6204817080⟩, ⟨.privateRow 13 0, 7225297200⟩, ⟨.privateRow 14 0, 4049642520⟩, ⟨.privateRow 15 0, 4625040420⟩, ⟨.privateRow 16 0, 1529335080⟩, ⟨.privateRow 17 0, 1533692160⟩, ⟨.hall 11 3, 739248048⟩, ⟨.hall 10 5, 321484275⟩, ⟨.hall 9 7, 272082888⟩, ⟨.hall 17 8, 211479107840⟩, ⟨.hall 8 9, 361496128⟩, ⟨.hall 16 9, 98002929024⟩, ⟨.hall 15 10, 54507070800⟩, ⟨.hall 7 11, 625924530⟩, ⟨.hall 7 12, 114760800⟩, ⟨.hall 12 13, 2711348640⟩, ⟨.hall 6 15, 9319233924⟩, ⟨.hall 5 20, 39099838377600⟩]
  caps := #[0, 66598369992000, 10327071918240, 0, 655078263840, 185768462880, 0, 20532303792, 28474205760, 977372032, 0, 1631296485, 0, 0, 23700600, 1779540840, 0, 1073584512, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_26_13_checked :
    (Witness.linear .positive case_51_26_13).check 51 26 13 = true := by
  change case_51_26_13.check 51 26 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_26_14 : Certificate := {
  objectiveScale := 2144142000000
  eta := 1764170270733911040
  rows := #[⟨.count 2, 590453727387844320⟩, ⟨.count 3, 144860389669195200⟩, ⟨.count 4, 31530109667696640⟩, ⟨.count 5, 7019924828716800⟩, ⟨.count 6, 1741897799722080⟩, ⟨.count 7, 427335905636640⟩, ⟨.count 8, 122111802933120⟩, ⟨.count 9, 36723491925120⟩, ⟨.count 10, 11879404336800⟩, ⟨.count 11, 4409556671520⟩, ⟨.count 12, 2166367563360⟩, ⟨.count 13, 2166367563360⟩, ⟨.path 15, 130772869920⟩, ⟨.path 16, 361878657280⟩, ⟨.privateRow 9 10, 1018467450000⟩, ⟨.privateRow 10 8, 731667016080⟩, ⟨.privateRow 10 9, 2239304382315⟩, ⟨.privateRow 11 6, 432644972760⟩, ⟨.privateRow 11 7, 1158065388480⟩, ⟨.privateRow 11 8, 723519276480⟩, ⟨.privateRow 12 4, 233956522800⟩, ⟨.privateRow 12 5, 256968067356⟩, ⟨.privateRow 13 2, 4727479680⟩, ⟨.privateRow 14 0, 158370569280⟩, ⟨.privateRow 15 0, 46442115720⟩, ⟨.privateRow 16 0, 32665028760⟩, ⟨.privateRow 17 0, 54752810112⟩, ⟨.privateRow 18 0, 27702314640⟩, ⟨.privateRow 19 0, 89043154200⟩, ⟨.privateRow 19 4, 17808630840⟩, ⟨.privateRow 19 5, 47489682240⟩, ⟨.privateRow 20 0, 322251415200⟩, ⟨.privateRow 21 0, 1353455943840⟩, ⟨.privateRow 22 0, 2842257482064⟩, ⟨.privateRow 23 0, 17369351279280⟩, ⟨.hall 17 2, 6156069920⟩, ⟨.hall 12 3, 29700237600⟩, ⟨.hall 18 3, 17808630840⟩, ⟨.hall 17 4, 5628406784⟩, ⟨.hall 21 4, 68214179569536⟩, ⟨.hall 11 5, 12821497920⟩, ⟨.hall 19 5, 612277688880⟩, ⟨.hall 20 5, 12030719500800⟩, ⟨.hall 10 7, 10801452690⟩, ⟨.hall 18 7, 685632287340⟩, ⟨.hall 9 8, 11420644032⟩, ⟨.hall 17 8, 147745678080⟩, ⟨.hall 9 9, 4264642872⟩, ⟨.hall 8 10, 23043478920⟩, ⟨.hall 8 11, 683455080⟩, ⟨.hall 13 11, 7977621960⟩, ⟨.hall 14 11, 4481256780⟩, ⟨.hall 13 12, 99277073280⟩, ⟨.hall 7 13, 53863910100⟩, ⟨.hall 12 13, 144863484480⟩, ⟨.hall 7 14, 126933206400⟩, ⟨.hall 6 19, 1310145353637120⟩, ⟨.hall 5 20, 1567001214979200⟩, ⟨.hall 4 21, 1147238474578560⟩]
  caps := #[0, 1631199418069760, 0, 0, 7346989628160, 1956207984640, 0, 36713575360, 103792866240, 92321989760, 0, 54085981950, 0, 52962289600, 4167463300, 0, 30561937000, 0, 83106943920, 142469046720, 751919968800, 1804607925120, 0, 0, 0, 0] }

theorem case_51_26_14_checked :
    (Witness.linear .positive case_51_26_14).check 51 26 14 = true := by
  change case_51_26_14.check 51 26 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_26_15 : Certificate := {
  objectiveScale := 1659042000000
  eta := 1025903363959393920
  rows := #[⟨.count 2, 298023329249886240⟩, ⟨.count 3, 71179601542489440⟩, ⟨.count 4, 19081021896256320⟩, ⟨.count 5, 5215316903596800⟩, ⟨.count 6, 1465792787178720⟩, ⟨.count 7, 427834547300160⟩, ⟨.count 8, 132306254720640⟩, ⟨.count 9, 43763138939520⟩, ⟨.count 10, 16132524408000⟩, ⟨.count 11, 6721885170000⟩, ⟨.count 12, 3364783662240⟩, ⟨.count 13, 2396832197760⟩, ⟨.count 14, 2366103579840⟩, ⟨.path 14, 276505253640⟩, ⟨.privateRow 4 22, 1927997992000080⟩, ⟨.privateRow 9 11, 5041355679360⟩, ⟨.privateRow 10 9, 2035814585805⟩, ⟨.privateRow 10 10, 4161981783960⟩, ⟨.privateRow 11 7, 797392115520⟩, ⟨.privateRow 11 8, 1315656251910⟩, ⟨.privateRow 12 5, 361829476008⟩, ⟨.privateRow 12 6, 1091292722520⟩, ⟨.privateRow 13 3, 170511596640⟩, ⟨.privateRow 13 4, 156006829440⟩, ⟨.privateRow 14 1, 74901006180⟩, ⟨.privateRow 15 0, 183731527980⟩, ⟨.privateRow 16 0, 150659112240⟩, ⟨.privateRow 17 0, 251602198848⟩, ⟨.privateRow 18 0, 507875768400⟩, ⟨.privateRow 19 0, 1317838682160⟩, ⟨.privateRow 20 0, 4221493539120⟩, ⟨.privateRow 21 0, 14888015382240⟩, ⟨.privateRow 22 0, 87162562783296⟩, ⟨.privateRow 23 0, 668720024252280⟩, ⟨.privateRow 24 0, 7457241482570880⟩, ⟨.privateRow 24 1, 998737698558600⟩, ⟨.privateRow 25 0, 196551579076332480⟩, ⟨.hall 13 2, 44105236560⟩, ⟨.hall 20 2, 1278263946960⟩, ⟨.hall 13 3, 11926141920⟩, ⟨.hall 20 3, 300767987520⟩, ⟨.hall 21 3, 7579353285504⟩, ⟨.hall 22 3, 104216107675680⟩, ⟨.hall 12 4, 27061751376⟩, ⟨.hall 11 5, 6708007152⟩, ⟨.hall 11 6, 14248098480⟩, ⟨.hall 19 6, 1353455943840⟩, ⟨.hall 10 7, 25151872725⟩, ⟨.hall 18 7, 498641663520⟩, ⟨.hall 17 8, 221618517120⟩, ⟨.hall 9 9, 31672620000⟩, ⟨.hall 8 10, 2194255280⟩, ⟨.hall 8 11, 59339221480⟩, ⟨.hall 14 11, 40331311020⟩, ⟨.hall 7 14, 469609980840⟩, ⟨.hall 6 19, 2240104932649584⟩, ⟨.hall 5 20, 2952037797508800⟩, ⟨.hall 4 21, 2881015538637600⟩, ⟨.assumptionRow 15, 2103370315200⟩]
  caps := #[0, 2597030826778080, 0, 0, 0, 367260894000, 195778542960, 59641453872, 0, 37441217520, 24403263885, 0, 46582175640, 11401287480, 13771989000, 0, 47122825680, 0, 156979782960, 712345233600, 3512540425680, 0, 28896284400984, 0, 2729883042726840, 0] }

theorem case_51_26_15_checked :
    (Witness.linear .conditional case_51_26_15).check 51 26 15 = true := by
  change case_51_26_15.check 51 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_26_16 : Certificate := {
  objectiveScale := 24571417500000
  eta := 3859122467230430400
  rows := #[⟨.count 2, 1139359966515650880⟩, ⟨.count 3, 341568292907041200⟩, ⟨.count 4, 107863671444328800⟩, ⟨.count 5, 35072555024707200⟩, ⟨.count 6, 11751381232390800⟩, ⟨.count 7, 4048471666118880⟩, ⟨.count 8, 1434869089093440⟩, ⟨.count 9, 524864348648640⟩, ⟨.count 10, 194800232226600⟩, ⟨.count 11, 93380428781640⟩, ⟨.count 12, 44525767366080⟩, ⟨.count 13, 22792952342160⟩, ⟨.count 14, 20407643376120⟩, ⟨.count 15, 18552403069200⟩, ⟨.count 17, 25486129468800⟩, ⟨.path 13, 516816942642⟩, ⟨.path 14, 1664048814120⟩, ⟨.privateRow 2 24, 4594193413369560⟩, ⟨.privateRow 3 23, 27165665400793920⟩, ⟨.privateRow 11 8, 17477206982235⟩, ⟨.privateRow 13 4, 1814465794680⟩, ⟨.privateRow 13 5, 2813441344560⟩, ⟨.privateRow 14 3, 985044258198⟩, ⟨.privateRow 15 1, 2233443565080⟩, ⟨.privateRow 16 0, 1218938879340⟩, ⟨.hall 13 3, 394400736576⟩, ⟨.hall 14 3, 270165465570⟩, ⟨.hall 13 4, 318947295744⟩, ⟨.hall 12 5, 560958441120⟩, ⟨.hall 11 6, 529382219520⟩, ⟨.hall 10 7, 75598061175⟩, ⟨.hall 11 7, 102612423606⟩, ⟨.hall 10 8, 582932308770⟩, ⟨.hall 9 9, 361557134568⟩, ⟨.hall 9 10, 586473070680⟩, ⟨.hall 15 10, 383314113000⟩, ⟨.hall 8 11, 93470192200⟩, ⟨.hall 14 11, 309206717820⟩, ⟨.hall 8 12, 2443953789200⟩, ⟨.hall 7 14, 8990468883396⟩, ⟨.hall 6 19, 42575798970969264⟩, ⟨.hall 5 20, 59706849625394400⟩, ⟨.hall 4 21, 73711794571964640⟩, ⟨.hall 3 22, 73785004234381440⟩, ⟨.hall 2 23, 27182311029103230⟩, ⟨.assumptionRow 16, 18962791993530⟩]
  caps := #[0, 33438156766067592, 3315402217226484, 652312222194402, 0, 37912686264180, 6796289602440, 0, 1731261728196, 0, 398365817850, 225282057840, 423195847074, 14754222252, 219197431530, 779677094070, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_26_16_checked :
    (Witness.linear .conditional case_51_26_16).check 51 26 16 = true := by
  change case_51_26_16.check 51 26 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_27_1_checked :
    (Witness.rising).check 51 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_27_2_checked :
    (Witness.rising).check 51 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_27_3_checked :
    (Witness.rising).check 51 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_27_4_checked :
    (Witness.rising).check 51 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_27_5_checked :
    (Witness.rising).check 51 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_27_6_checked :
    (Witness.rising).check 51 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_27_7_checked :
    (Witness.rising).check 51 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_27_8_checked :
    (Witness.rising).check 51 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_27_9_checked :
    (Witness.rising).check 51 27 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_27_10_checked :
    (Witness.rising).check 51 27 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_27_11 : Certificate := {
  objectiveScale := 1182102480000000
  eta := 599358472708192797600
  rows := #[⟨.count 2, 140622267957050880000⟩, ⟨.count 3, 22447628512803093600⟩, ⟨.count 4, 3122910106578662400⟩, ⟨.count 5, 486242582383958400⟩, ⟨.count 6, 84164301695073600⟩, ⟨.count 7, 17381540297721600⟩, ⟨.count 8, 4320648537004800⟩, ⟨.count 9, 1521297051674400⟩, ⟨.count 10, 1187353796428800⟩, ⟨.path 11, 344208076898400⟩, ⟨.path 12, 175573619020800⟩, ⟨.privateRow 6 15, 1257272376703200⟩, ⟨.privateRow 6 16, 4115099690301600⟩, ⟨.privateRow 7 11, 19023575210640⟩, ⟨.privateRow 7 12, 849942190697600⟩, ⟨.privateRow 7 13, 1216507572680400⟩, ⟨.privateRow 7 14, 1649186632922400⟩, ⟨.privateRow 7 15, 2089255803835200⟩, ⟨.privateRow 8 9, 430265832796800⟩, ⟨.privateRow 8 10, 343013318968320⟩, ⟨.privateRow 8 11, 576269705211200⟩, ⟨.privateRow 8 12, 538019689006800⟩, ⟨.privateRow 8 13, 806293327039200⟩, ⟨.privateRow 9 5, 44614112142600⟩, ⟨.privateRow 9 6, 35836265757600⟩, ⟨.privateRow 9 7, 267979155444000⟩, ⟨.privateRow 9 8, 164910249504000⟩, ⟨.privateRow 9 9, 102038216880600⟩, ⟨.privateRow 10 3, 92679560221248⟩, ⟨.privateRow 10 4, 17403920974440⟩, ⟨.privateRow 11 0, 24008992207200⟩, ⟨.privateRow 12 0, 10979386889625⟩, ⟨.privateRow 13 0, 8970392692800⟩, ⟨.privateRow 13 12, 5481906645600⟩, ⟨.privateRow 14 0, 10475166358800⟩, ⟨.privateRow 14 11, 5300686591200⟩, ⟨.privateRow 15 0, 15127344041040⟩, ⟨.privateRow 16 0, 25423663465200⟩, ⟨.privateRow 17 0, 43851134527200⟩, ⟨.privateRow 17 6, 18964678692960⟩, ⟨.privateRow 18 0, 114141451263840⟩, ⟨.privateRow 18 6, 30037224016800⟩, ⟨.privateRow 19 0, 347096810860800⟩, ⟨.privateRow 19 5, 60074448033600⟩, ⟨.privateRow 20 4, 114141451263840⟩, ⟨.privateRow 21 0, 6848487075830400⟩, ⟨.privateRow 22 0, 48605234663185200⟩, ⟨.privateRow 22 5, 3994950794234400⟩, ⟨.privateRow 23 0, 17577783494631360⟩, ⟨.privateRow 23 4, 2636667524194704000⟩, ⟨.hall 19 1, 1369697415166080⟩, ⟨.hall 23 3, 1010722550941303200⟩, ⟨.hall 20 6, 978355296547200⟩, ⟨.hall 14 11, 634270190400⟩, ⟨.hall 15 11, 7730167945500⟩, ⟨.hall 6 13, 100301212440⟩, ⟨.hall 6 14, 407404483200⟩, ⟨.hall 5 16, 4409589927600⟩, ⟨.hall 7 19, 1640032431317280⟩, ⟨.hall 4 21, 6171759103910400⟩]
  caps := #[0, 16676250674054400, 20926582888068000, 0, 276470128022400, 0, 0, 0, 27576789734000, 5013505224000, 0, 5404353598800, 323915944275, 0, 4773206790000, 0, 0, 23837026973760, 0, 480595584268800, 0, 0, 49936884927930000, 0, 0] }

theorem case_51_27_11_checked :
    (Witness.linear .positive case_51_27_11).check 51 27 11 = true := by
  change case_51_27_11.check 51 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_27_12 : Certificate := {
  objectiveScale := 710424000000
  eta := 525629775823752600
  rows := #[⟨.count 2, 133360857395766000⟩, ⟨.count 3, 23328803568470400⟩, ⟨.count 4, 3698915479459200⟩, ⟨.count 5, 662264570167200⟩, ⟨.count 6, 127698358788000⟩, ⟨.count 7, 27266410571400⟩, ⟨.count 8, 6702234739200⟩, ⟨.count 9, 1984214232000⟩, ⟨.count 10, 810220811400⟩, ⟨.count 11, 714553339500⟩, ⟨.path 12, 100374030900⟩, ⟨.path 13, 151675524000⟩, ⟨.privateRow 4 23, 48067589770200⟩, ⟨.privateRow 6 16, 2462945284800⟩, ⟨.privateRow 7 13, 923604481800⟩, ⟨.privateRow 7 14, 2174199370200⟩, ⟨.privateRow 7 15, 2998368172800⟩, ⟨.privateRow 8 10, 272829456900⟩, ⟨.privateRow 8 11, 660792332200⟩, ⟨.privateRow 8 12, 1023799426650⟩, ⟨.privateRow 8 13, 1361391431400⟩, ⟨.privateRow 8 14, 1694849656500⟩, ⟨.privateRow 9 7, 70274254050⟩, ⟨.privateRow 9 8, 209194303500⟩, ⟨.privateRow 9 9, 332355883860⟩, ⟨.privateRow 9 10, 447060614000⟩, ⟨.privateRow 9 11, 518100382800⟩, ⟨.privateRow 9 12, 552745393200⟩, ⟨.privateRow 10 4, 14172958800⟩, ⟨.privateRow 10 5, 73390487940⟩, ⟨.privateRow 10 6, 115470244890⟩, ⟨.privateRow 10 7, 159037777080⟩, ⟨.privateRow 10 8, 96069039066⟩, ⟨.privateRow 11 2, 23542859340⟩, ⟨.privateRow 11 3, 61078703400⟩, ⟨.privateRow 12 0, 19237974525⟩, ⟨.privateRow 13 0, 10127003040⟩, ⟨.privateRow 14 0, 9954816300⟩, ⟨.privateRow 15 0, 15008799960⟩, ⟨.privateRow 15 10, 551170620⟩, ⟨.privateRow 15 11, 826755930⟩, ⟨.privateRow 16 0, 25491641175⟩, ⟨.privateRow 17 0, 50607484200⟩, ⟨.privateRow 18 0, 124485821460⟩, ⟨.privateRow 19 0, 370334164200⟩, ⟨.privateRow 19 7, 20078358300⟩, ⟨.privateRow 20 0, 1430583028875⟩, ⟨.privateRow 21 0, 7084792143000⟩, ⟨.privateRow 22 0, 50738011424100⟩, ⟨.privateRow 23 0, 563993053303680⟩, ⟨.privateRow 24 0, 13174525229515650⟩, ⟨.hall 13 3, 42181425⟩, ⟨.hall 20 6, 435987208800⟩, ⟨.hall 16 10, 4008513600⟩, ⟨.hall 6 12, 350566920⟩, ⟨.hall 7 12, 308313390⟩, ⟨.hall 6 13, 388661130⟩, ⟨.hall 5 17, 23752147380⟩, ⟨.hall 5 18, 27979322670⟩, ⟨.hall 8 18, 248316868800⟩, ⟨.hall 4 21, 9384926241600⟩]
  caps := #[0, 0, 0, 8622220721400, 613824096600, 75823862400, 188614881000, 130031272800, 0, 13698810580, 577219500, 0, 5870049075, 370103580, 0, 6190070040, 0, 0, 0, 160626866400, 0, 4359872088000, 8011264961700, 246746960820360, 0] }

theorem case_51_27_12_checked :
    (Witness.linear .positive case_51_27_12).check 51 27 12 = true := by
  change case_51_27_12.check 51 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_27_13 : Certificate := {
  objectiveScale := 17172280125000
  eta := 17738180769019871160
  rows := #[⟨.count 2, 5048019823594587840⟩, ⟨.count 3, 1006346263934891880⟩, ⟨.count 4, 182512180570880160⟩, ⟨.count 5, 35241173077710600⟩, ⟨.count 6, 7273650328504560⟩, ⟨.count 7, 1606900463007840⟩, ⟨.count 8, 409277255587200⟩, ⟨.count 9, 115109228133900⟩, ⟨.count 10, 39466021074480⟩, ⟨.count 11, 17227231421400⟩, ⟨.count 12, 16962197091840⟩, ⟨.path 14, 4838383146168⟩, ⟨.path 15, 57501600156⟩, ⟨.privateRow 7 14, 22735968049080⟩, ⟨.privateRow 7 15, 135288870596880⟩, ⟨.privateRow 8 11, 703783640560⟩, ⟨.privateRow 8 12, 34806838030965⟩, ⟨.privateRow 8 13, 54953128109880⟩, ⟨.privateRow 8 14, 104714885134860⟩, ⟨.privateRow 9 9, 6760383239610⟩, ⟨.privateRow 9 10, 15361431385300⟩, ⟨.privateRow 9 11, 29142733154535⟩, ⟨.privateRow 9 12, 40805916851700⟩, ⟨.privateRow 9 13, 52925883200190⟩, ⟨.privateRow 10 6, 864841819842⟩, ⟨.privateRow 10 7, 4697386683444⟩, ⟨.privateRow 10 8, 8331715560168⟩, ⟨.privateRow 10 9, 11734238776260⟩, ⟨.privateRow 10 10, 18874259152749⟩, ⟨.privateRow 10 11, 13113577372896⟩, ⟨.privateRow 11 4, 1252889557920⟩, ⟨.privateRow 11 5, 2631938133825⟩, ⟨.privateRow 11 6, 4351892896260⟩, ⟨.privateRow 11 7, 4865387783256⟩, ⟨.privateRow 12 2, 1236826871280⟩, ⟨.privateRow 12 3, 1308182267700⟩, ⟨.privateRow 13 0, 594854828568⟩, ⟨.privateRow 14 0, 346781931210⟩, ⟨.privateRow 15 0, 438511345272⟩, ⟨.privateRow 16 0, 741002967705⟩, ⟨.privateRow 17 0, 1350969296040⟩, ⟨.privateRow 18 0, 3372361060068⟩, ⟨.privateRow 19 0, 10057918951080⟩, ⟨.privateRow 20 0, 38782152190782⟩, ⟨.privateRow 21 0, 197524004946840⟩, ⟨.privateRow 22 0, 1416391645228560⟩, ⟨.privateRow 23 0, 15580308097514160⟩, ⟨.privateRow 24 3, 1433388344971302720⟩, ⟨.hall 20 6, 19270634628960⟩, ⟨.hall 19 7, 8430902650170⟩, ⟨.hall 16 8, 27560757952⟩, ⟨.hall 18 8, 3549853747440⟩, ⟨.hall 17 9, 1656598415472⟩, ⟨.hall 14 11, 4684950270⟩, ⟨.hall 7 12, 29161760628⟩, ⟨.hall 7 13, 15493212735⟩, ⟨.hall 8 13, 27571423880⟩, ⟨.hall 8 14, 39957613696⟩, ⟨.hall 6 15, 325815394905⟩, ⟨.hall 9 17, 9257461733520⟩, ⟨.hall 5 21, 8798796583995600⟩, ⟨.hall 4 22, 7935312198733920⟩]
  caps := #[0, 0, 390574934109360, 65553965869392, 2062295986608, 6586357717368, 4224289325256, 0, 0, 106458885715, 0, 0, 210083033160, 343713313944, 0, 115126488477, 1370347953975, 598954329064, 0, 12424488116040, 28665069010578, 110806149116520, 0, 0, 0] }

theorem case_51_27_13_checked :
    (Witness.linear .positive case_51_27_13).check 51 27 13 = true := by
  change case_51_27_13.check 51 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_27_14 : Certificate := {
  objectiveScale := 106849743000000
  eta := 127213215616203116400
  rows := #[⟨.count 2, 35990511705257709600⟩, ⟨.count 3, 7563531385520510400⟩, ⟨.count 4, 1674040030217755200⟩, ⟨.count 5, 369948008289459600⟩, ⟨.count 6, 92651182808184000⟩, ⟨.count 7, 22985303014674000⟩, ⟨.count 8, 6314563371916800⟩, ⟨.count 9, 1885598784669600⟩, ⟨.count 10, 606607360959600⟩, ⟨.count 11, 223954008478200⟩, ⟨.count 12, 106013731824000⟩, ⟨.count 13, 109105799002200⟩, ⟨.path 15, 9904806791880⟩, ⟨.path 16, 14331262875930⟩, ⟨.privateRow 4 23, 102857012332074000⟩, ⟨.privateRow 7 15, 962404793750400⟩, ⟨.privateRow 8 13, 610087609731600⟩, ⟨.privateRow 8 14, 1467388890567600⟩, ⟨.privateRow 8 15, 492107176360800⟩, ⟨.privateRow 9 10, 42903733472600⟩, ⟨.privateRow 9 11, 255798284742000⟩, ⟨.privateRow 9 12, 660551216925600⟩, ⟨.privateRow 9 13, 1029080559807300⟩, ⟨.privateRow 10 8, 38881339280784⟩, ⟨.privateRow 10 9, 119778561903000⟩, ⟨.privateRow 10 10, 274800443037120⟩, ⟨.privateRow 10 11, 464404396135680⟩, ⟨.privateRow 10 12, 588945098441700⟩, ⟨.privateRow 11 6, 24203548278000⟩, ⟨.privateRow 11 7, 61391588338080⟩, ⟨.privateRow 11 8, 102377318043000⟩, ⟨.privateRow 11 9, 240071910603525⟩, ⟨.privateRow 11 10, 248638915839600⟩, ⟨.privateRow 12 4, 14135164243200⟩, ⟨.privateRow 12 5, 32406470296200⟩, ⟨.privateRow 12 6, 61443792069660⟩, ⟨.privateRow 12 7, 78528690240000⟩, ⟨.privateRow 13 2, 9242222774400⟩, ⟨.privateRow 13 3, 17853006921750⟩, ⟨.privateRow 13 4, 13332029911200⟩, ⟨.privateRow 14 0, 7457675940000⟩, ⟨.privateRow 15 0, 1742801500440⟩, ⟨.privateRow 16 0, 1218087070200⟩, ⟨.privateRow 17 0, 2214703764000⟩, ⟨.privateRow 18 0, 5324780621160⟩, ⟨.privateRow 19 0, 15777127766400⟩, ⟨.privateRow 20 0, 59016318551190⟩, ⟨.privateRow 21 0, 289059519434400⟩, ⟨.privateRow 22 0, 2360652742047600⟩, ⟨.privateRow 23 0, 25967180162523600⟩, ⟨.privateRow 24 0, 597245143738042800⟩, ⟨.hall 8 11, 152812860200⟩, ⟨.hall 8 12, 873142670400⟩, ⟨.hall 9 12, 307868160600⟩, ⟨.hall 9 13, 1219622474070⟩, ⟨.hall 7 14, 4570141591015⟩, ⟨.hall 10 16, 371014991146800⟩, ⟨.hall 6 17, 98070270320880⟩, ⟨.hall 5 21, 167836278394020600⟩, ⟨.hall 4 22, 171081342821188800⟩]
  caps := #[0, 0, 18952123026236400, 859094947510800, 413853782722380, 44383551532320, 0, 10440746316000, 6609478525650, 3684818257120, 1808973621000, 0, 3001972883910, 0, 1560747654180, 0, 0, 0, 0, 0, 0, 5781190388688000, 0, 0, 0] }

theorem case_51_27_14_checked :
    (Witness.linear .positive case_51_27_14).check 51 27 14 = true := by
  change case_51_27_14.check 51 27 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_27_15 : Certificate := {
  objectiveScale := 1190112000000
  eta := 1442576731798041840
  rows := #[⟨.count 2, 361143551798789760⟩, ⟨.count 3, 90431158887669600⟩, ⟨.count 4, 22600007350240320⟩, ⟨.count 5, 5644813589775360⟩, ⟨.count 6, 1582688640012480⟩, ⟨.count 7, 458113177201680⟩, ⟨.count 8, 138224772766080⟩, ⟨.count 9, 44357109156360⟩, ⟨.count 10, 15516555294240⟩, ⟨.count 11, 6095789579880⟩, ⟨.count 12, 2935764881280⟩, ⟨.count 13, 2208619413000⟩, ⟨.count 14, 1574143290720⟩, ⟨.path 14, 238025666736⟩, ⟨.privateRow 3 24, 326859610437360⟩, ⟨.privateRow 7 15, 9451106344680⟩, ⟨.privateRow 8 13, 5980673658960⟩, ⟨.privateRow 8 14, 27872330806320⟩, ⟨.privateRow 9 11, 2928093918750⟩, ⟨.privateRow 9 12, 11565134380800⟩, ⟨.privateRow 9 13, 23790177471060⟩, ⟨.privateRow 10 9, 1333024516824⟩, ⟨.privateRow 10 10, 4986661067388⟩, ⟨.privateRow 10 11, 10310638554216⟩, ⟨.privateRow 10 12, 15692709424392⟩, ⟨.privateRow 11 7, 595122540012⟩, ⟨.privateRow 11 8, 2202372812640⟩, ⟨.privateRow 11 9, 4587904871550⟩, ⟨.privateRow 11 10, 7178873593320⟩, ⟨.privateRow 11 11, 8867941582500⟩, ⟨.privateRow 12 5, 274919059800⟩, ⟨.privateRow 12 6, 1020721956408⟩, ⟨.privateRow 12 7, 2135376307680⟩, ⟨.privateRow 12 8, 3416564338110⟩, ⟨.privateRow 12 9, 1736800057080⟩, ⟨.privateRow 13 3, 138746604150⟩, ⟨.privateRow 13 4, 515859359400⟩, ⟨.privateRow 13 5, 1058098592628⟩, ⟨.privateRow 13 6, 412275623760⟩, ⟨.privateRow 14 0, 22946695200⟩, ⟨.privateRow 14 2, 433692539280⟩, ⟨.privateRow 15 0, 121952859336⟩, ⟨.privateRow 16 0, 99945605760⟩, ⟨.privateRow 17 0, 54515784960⟩, ⟨.privateRow 17 7, 37479602160⟩, ⟨.privateRow 18 0, 427802887512⟩, ⟨.privateRow 19 0, 1304647103760⟩, ⟨.privateRow 19 8, 273065672880⟩, ⟨.privateRow 22 5, 508448282902560⟩, ⟨.hall 16 1, 119253279600⟩, ⟨.hall 19 4, 722648798586⟩, ⟨.hall 17 6, 1517031516⟩, ⟨.hall 20 6, 71153112476160⟩, ⟨.hall 9 11, 18754943130⟩, ⟨.hall 8 12, 38714343360⟩, ⟨.hall 9 12, 1103855445⟩, ⟨.hall 7 14, 75592083567⟩, ⟨.hall 7 15, 188795276670⟩, ⟨.hall 10 16, 32613867926640⟩, ⟨.hall 6 17, 219615976008⟩, ⟨.hall 9 17, 2951518670100⟩, ⟨.hall 6 20, 2737444361240160⟩, ⟨.hall 5 21, 4435716026490840⟩, ⟨.hall 4 22, 5251409062099200⟩, ⟨.hall 3 23, 4094824564090260⟩, ⟨.assumptionRow 15, 1702388768080⟩]
  caps := #[0, 0, 55648029222016, 0, 2882835811856, 3878556842160, 1399508896240, 600438524400, 89922652512, 186477459168, 0, 90095379660, 0, 19925521000, 45017411296, 109501114184, 0, 0, 63715323672, 2457591055920, 0, 31129486708320, 0, 0, 0] }

theorem case_51_27_15_checked :
    (Witness.linear .conditional case_51_27_15).check 51 27 15 = true := by
  change case_51_27_15.check 51 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_27_16 : Certificate := {
  objectiveScale := 2826516000000
  eta := 1709039949773476320
  rows := #[⟨.count 2, 452228429907334080⟩, ⟨.count 3, 121591775082697920⟩, ⟨.count 4, 33619845644985600⟩, ⟨.count 5, 9816164808690240⟩, ⟨.count 6, 2942555690954880⟩, ⟨.count 7, 907306209089280⟩, ⟨.count 8, 288443018223360⟩, ⟨.count 9, 100182976573680⟩, ⟨.count 10, 37329683751360⟩, ⟨.count 11, 15018612008400⟩, ⟨.count 12, 6523921958400⟩, ⟨.count 13, 3003722401680⟩, ⟨.count 14, 2698531355520⟩, ⟨.count 15, 2698531355520⟩, ⟨.count 17, 2548612946880⟩, ⟨.path 13, 356338022040⟩, ⟨.privateRow 3 24, 12057487851689280⟩, ⟨.privateRow 7 15, 5855741651760⟩, ⟨.privateRow 8 13, 1595560206240⟩, ⟨.privateRow 8 14, 58230808555920⟩, ⟨.privateRow 9 11, 18739801080⟩, ⟨.privateRow 9 12, 19933794120240⟩, ⟨.privateRow 9 13, 59155305409200⟩, ⟨.privateRow 10 10, 6690108985560⟩, ⟨.privateRow 10 11, 23117418612288⟩, ⟨.privateRow 10 12, 44964278711352⟩, ⟨.privateRow 10 13, 8477886008592⟩, ⟨.privateRow 11 8, 2304103161360⟩, ⟨.privateRow 11 9, 9057347429130⟩, ⟨.privateRow 11 10, 19557468318960⟩, ⟨.privateRow 11 11, 30339737948520⟩, ⟨.privateRow 12 6, 778793183784⟩, ⟨.privateRow 12 7, 3668195934480⟩, ⟨.privateRow 12 8, 8562647570400⟩, ⟨.privateRow 12 9, 14573975660640⟩, ⟨.privateRow 12 10, 18382509268200⟩, ⟨.privateRow 13 4, 237233525760⟩, ⟨.privateRow 13 5, 1558945517976⟩, ⟨.privateRow 13 6, 3914353175040⟩, ⟨.privateRow 13 7, 7120249199910⟩, ⟨.privateRow 13 8, 3065854991760⟩, ⟨.privateRow 14 2, 17401243860⟩, ⟨.privateRow 14 3, 734502852720⟩, ⟨.privateRow 14 4, 1917884784816⟩, ⟨.privateRow 14 5, 1445641797600⟩, ⟨.privateRow 15 1, 303584777496⟩, ⟨.privateRow 15 2, 570371400144⟩, ⟨.privateRow 16 0, 143671808280⟩, ⟨.hall 10 10, 50746791060⟩, ⟨.hall 9 11, 97230131460⟩, ⟨.hall 8 12, 71088790080⟩, ⟨.hall 8 13, 176912415680⟩, ⟨.hall 7 15, 609996963576⟩, ⟨.hall 11 15, 38175986553705⟩, ⟨.hall 7 16, 3266117190336⟩, ⟨.hall 5 19, 65639195458200⟩, ⟨.hall 6 20, 9454937932851840⟩, ⟨.hall 4 22, 17250247156222080⟩, ⟨.hall 3 23, 16597204663319280⟩, ⟨.assumptionRow 16, 2636264695680⟩]
  caps := #[0, 5582675978880, 148466451598080, 101449594923600, 0, 0, 0, 121362521280, 256431094920, 0, 137443994688, 0, 0, 95002244832, 0, 0, 198985238760, 277903053120, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_27_16_checked :
    (Witness.linear .conditional case_51_27_16).check 51 27 16 = true := by
  change case_51_27_16.check 51 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_27_17 : Certificate := {
  objectiveScale := 23126040000000
  eta := 12128670611295638400
  rows := #[⟨.count 2, 3195960635387520000⟩, ⟨.count 3, 885789544285245600⟩, ⟨.count 4, 249035893666560000⟩, ⟨.count 5, 71027112172816800⟩, ⟨.count 6, 20545461227491200⟩, ⟨.count 7, 6314188575895200⟩, ⟨.count 8, 1999911571257600⟩, ⟨.count 9, 649334107422000⟩, ⟨.count 10, 212509344247200⟩, ⟨.count 11, 67142030155200⟩, ⟨.count 12, 31804119547200⟩, ⟨.count 13, 13251716478000⟩, ⟨.count 14, 12368268712800⟩, ⟨.count 15, 11806074680400⟩, ⟨.count 16, 11993472691200⟩, ⟨.count 18, 16383940372800⟩, ⟨.path 12, 3646411025400⟩, ⟨.path 13, 558248811120⟩, ⟨.privateRow 3 24, 127475248070570400⟩, ⟨.privateRow 8 14, 371360391402000⟩, ⟨.privateRow 9 12, 105451537791600⟩, ⟨.privateRow 9 13, 435075715074000⟩, ⟨.privateRow 10 10, 27435068781120⟩, ⟨.privateRow 10 11, 145303063345440⟩, ⟨.privateRow 10 12, 353563826976360⟩, ⟨.privateRow 11 8, 5729024901600⟩, ⟨.privateRow 11 9, 49161860297550⟩, ⟨.privateRow 11 10, 142510450539600⟩, ⟨.privateRow 11 11, 274872725127000⟩, ⟨.privateRow 11 12, 189234511305840⟩, ⟨.privateRow 12 6, 6795752040⟩, ⟨.privateRow 12 7, 15290442090000⟩, ⟨.privateRow 12 8, 55555272927000⟩, ⟨.privateRow 12 9, 122362369588800⟩, ⟨.privateRow 12 10, 201403437958800⟩, ⟨.privateRow 12 11, 182642631827040⟩, ⟨.privateRow 13 5, 2650343295600⟩, ⟨.privateRow 13 6, 21104585502000⟩, ⟨.privateRow 13 7, 54247090659300⟩, ⟨.privateRow 13 8, 99334478390400⟩, ⟨.privateRow 13 9, 135529948184400⟩, ⟨.privateRow 14 4, 6521450775840⟩, ⟨.privateRow 14 5, 24147572248800⟩, ⟨.privateRow 14 6, 50687815528350⟩, ⟨.privateRow 14 7, 16705194105600⟩, ⟨.privateRow 15 2, 1103944645440⟩, ⟨.privateRow 15 3, 10040785418664⟩, ⟨.privateRow 15 4, 16316120140320⟩, ⟨.privateRow 16 1, 3918322044000⟩, ⟨.privateRow 16 2, 2436174140400⟩, ⟨.privateRow 17 0, 1158460430400⟩, ⟨.hall 10 10, 263100001500⟩, ⟨.hall 9 11, 977797878750⟩, ⟨.hall 10 11, 879737962950⟩, ⟨.hall 9 12, 576276138900⟩, ⟨.hall 11 12, 2877151519935⟩, ⟨.hall 8 13, 2240211573600⟩, ⟨.hall 11 13, 281336044275⟩, ⟨.hall 8 14, 3864047707520⟩, ⟨.hall 7 16, 57253379983800⟩, ⟨.hall 6 20, 89770730053118400⟩, ⟨.hall 5 21, 127991714554594800⟩, ⟨.hall 4 22, 160574013177177600⟩, ⟨.hall 3 23, 159207868583864100⟩, ⟨.assumptionRow 17, 12055938694800⟩]
  caps := #[0, 0, 1856605360708560, 171919817673120, 0, 19253462553600, 88236275400, 0, 1584891348040, 1020188598000, 336950551080, 263821638000, 835920490680, 348308417520, 95759333670, 249864014400, 2842318794000, 0, 6742099627200, 0, 0, 0, 0, 0, 0] }

theorem case_51_27_17_checked :
    (Witness.linear .conditional case_51_27_17).check 51 27 17 = true := by
  change case_51_27_17.check 51 27 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_28_1_checked :
    (Witness.rising).check 51 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_28_2_checked :
    (Witness.rising).check 51 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_28_3_checked :
    (Witness.rising).check 51 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_28_4_checked :
    (Witness.rising).check 51 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_28_5_checked :
    (Witness.rising).check 51 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_28_6_checked :
    (Witness.rising).check 51 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_28_7_checked :
    (Witness.rising).check 51 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_28_8_checked :
    (Witness.rising).check 51 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_28_9_checked :
    (Witness.rising).check 51 28 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_28_10_checked :
    (Witness.rising).check 51 28 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_28_11 : Certificate := {
  objectiveScale := 16230240000000
  eta := 10754407538079004800
  rows := #[⟨.count 2, 2290922691820963200⟩, ⟨.count 3, 321463832741251200⟩, ⟨.count 4, 44909472824536320⟩, ⟨.count 5, 6957713344982400⟩, ⟨.count 6, 1205129836310400⟩, ⟨.count 7, 245866190169600⟩, ⟨.count 8, 60716955499200⟩, ⟨.count 9, 21138495618240⟩, ⟨.count 10, 16383940372800⟩, ⟨.path 11, 4888331884800⟩, ⟨.path 12, 2329440422400⟩, ⟨.privateRow 4 24, 1390450406304960⟩, ⟨.privateRow 5 19, 85633395015168⟩, ⟨.privateRow 5 20, 303649028242560⟩, ⟨.privateRow 6 15, 13729135219800⟩, ⟨.privateRow 6 16, 61201385731200⟩, ⟨.privateRow 6 17, 81211753823200⟩, ⟨.privateRow 6 18, 99031817364480⟩, ⟨.privateRow 6 19, 145483322384400⟩, ⟨.privateRow 7 12, 11693635873920⟩, ⟨.privateRow 7 13, 18347157628800⟩, ⟨.privateRow 7 14, 27172711566000⟩, ⟨.privateRow 7 15, 34389447206400⟩, ⟨.privateRow 7 16, 35409300326400⟩, ⟨.privateRow 7 17, 38893118584320⟩, ⟨.privateRow 7 18, 21791711541600⟩, ⟨.privateRow 8 9, 5785913583450⟩, ⟨.privateRow 8 10, 5979700162800⟩, ⟨.privateRow 8 11, 9191872429740⟩, ⟨.privateRow 8 12, 9921683571800⟩, ⟨.privateRow 8 13, 12965599872225⟩, ⟨.privateRow 9 5, 599673634560⟩, ⟨.privateRow 9 6, 128501493120⟩, ⟨.privateRow 9 7, 5089537770240⟩, ⟨.privateRow 9 8, 2298748932480⟩, ⟨.privateRow 9 9, 649646437440⟩, ⟨.privateRow 10 3, 1365328364400⟩, ⟨.privateRow 10 4, 113509652256⟩, ⟨.privateRow 11 0, 299287665600⟩, ⟨.privateRow 12 0, 137247541200⟩, ⟨.privateRow 13 0, 134370551700⟩, ⟨.privateRow 14 0, 175618707264⟩, ⟨.privateRow 14 12, 21416915520⟩, ⟨.privateRow 15 0, 278419901760⟩, ⟨.privateRow 16 0, 526155953400⟩, ⟨.privateRow 17 0, 1177930353600⟩, ⟨.privateRow 18 0, 3420216508800⟩, ⟨.privateRow 19 0, 12233342145024⟩, ⟨.privateRow 20 0, 58800141560160⟩, ⟨.privateRow 21 0, 397765663495200⟩, ⟨.privateRow 22 0, 4046833272081600⟩, ⟨.privateRow 23 0, 90552218002646400⟩, ⟨.hall 21 6, 207529911388800⟩, ⟨.hall 16 9, 2271491040⟩, ⟨.hall 12 15, 16989380100⟩, ⟨.hall 5 17, 20504203200⟩, ⟨.hall 6 21, 9929660832000⟩, ⟨.hall 4 22, 77522948783280⟩]
  caps := #[0, 1317382287811200, 186724907740800, 85820640048000, 17098752602880, 14763750713712, 0, 34519811040, 473121884105, 0, 0, 0, 0, 427823480700, 0, 149918408640, 0, 2222816232000, 0, 12670247221632, 79553132699040, 0, 518824778472000, 0] }

theorem case_51_28_11_checked :
    (Witness.linear .positive case_51_28_11).check 51 28 11 = true := by
  change case_51_28_11.check 51 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_28_12 : Certificate := {
  objectiveScale := 82954560000000
  eta := 86306916958639977600
  rows := #[⟨.count 2, 20006713577525875200⟩, ⟨.count 3, 3127475764629216000⟩, ⟨.count 4, 502222385560896000⟩, ⟨.count 5, 86026609584115200⟩, ⟨.count 6, 16420349129184000⟩, ⟨.count 7, 3446624214633600⟩, ⟨.count 8, 824551247520000⟩, ⟨.count 9, 237470759285760⟩, ⟨.count 10, 95412358641600⟩, ⟨.count 11, 83723665132800⟩, ⟨.path 12, 13552937798400⟩, ⟨.path 13, 16754509371600⟩, ⟨.privateRow 4 24, 21230309935074240⟩, ⟨.privateRow 5 20, 2847528836792640⟩, ⟨.privateRow 6 16, 97263392054400⟩, ⟨.privateRow 6 17, 1000128310781600⟩, ⟨.privateRow 6 18, 1371032402900160⟩, ⟨.privateRow 6 19, 2286166494612000⟩, ⟨.privateRow 7 13, 73816968825600⟩, ⟨.privateRow 7 14, 266506742502000⟩, ⟨.privateRow 7 15, 413285278348800⟩, ⟨.privateRow 7 16, 627836878468800⟩, ⟨.privateRow 7 17, 795809746892160⟩, ⟨.privateRow 7 18, 837508481409600⟩, ⟨.privateRow 8 10, 24830236431000⟩, ⟨.privateRow 8 11, 81115228974780⟩, ⟨.privateRow 8 12, 132157241616400⟩, ⟨.privateRow 8 13, 186168211354125⟩, ⟨.privateRow 8 14, 216591943768200⟩, ⟨.privateRow 8 15, 294261726458700⟩, ⟨.privateRow 8 16, 190883613800880⟩, ⟨.privateRow 9 7, 6723264018240⟩, ⟨.privateRow 9 8, 25973364296880⟩, ⟨.privateRow 9 9, 43976066534400⟩, ⟨.privateRow 9 10, 62226134146176⟩, ⟨.privateRow 9 11, 75309013940160⟩, ⟨.privateRow 9 12, 50984752138320⟩, ⟨.privateRow 10 4, 1248606174816⟩, ⟨.privateRow 10 5, 7294754404080⟩, ⟨.privateRow 10 6, 19381484818080⟩, ⟨.privateRow 10 7, 20908263776400⟩, ⟨.privateRow 10 8, 5332811964480⟩, ⟨.privateRow 11 2, 3584759201100⟩, ⟨.privateRow 11 3, 5853407757120⟩, ⟨.privateRow 12 0, 1978763094000⟩, ⟨.privateRow 13 0, 1053341566200⟩, ⟨.privateRow 14 0, 1154371746528⟩, ⟨.privateRow 15 0, 1884688565760⟩, ⟨.privateRow 16 0, 3567769821000⟩, ⟨.privateRow 17 0, 8245512475200⟩, ⟨.privateRow 18 0, 23665691649600⟩, ⟨.privateRow 19 0, 84104227247040⟩, ⟨.privateRow 20 0, 405836271160320⟩, ⟨.privateRow 21 0, 2758418405542800⟩, ⟨.privateRow 22 0, 28535362815960000⟩, ⟨.privateRow 23 5, 3867112368818899200⟩, ⟨.hall 13 6, 313800960⟩, ⟨.hall 14 10, 1235591280⟩, ⟨.hall 5 20, 1356848064000⟩, ⟨.hall 6 20, 77325263558400⟩, ⟨.hall 5 21, 580798813795200⟩, ⟨.hall 6 21, 1026726930028800⟩, ⟨.hall 4 23, 30513814637866560⟩]
  caps := #[0, 0, 0, 259239014205600, 0, 0, 27003789155200, 3071558599200, 4436275433395, 0, 1788350042304, 0, 2157366253200, 0, 2415663325152, 0, 4043472463800, 11779303536000, 0, 144178675280640, 862402076215680, 0, 71909114296219200, 0] }

theorem case_51_28_12_checked :
    (Witness.linear .positive case_51_28_12).check 51 28 12 = true := by
  change case_51_28_12.check 51 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_28_13 : Certificate := {
  objectiveScale := 8706880000000
  eta := 12280948735687632000
  rows := #[⟨.count 2, 3062738639917756800⟩, ⟨.count 3, 530373207658694400⟩, ⟨.count 4, 96647900497948800⟩, ⟨.count 5, 18642996621849600⟩, ⟨.count 6, 3825489450182400⟩, ⟨.count 7, 846068948524800⟩, ⟨.count 8, 213236889465600⟩, ⟨.count 9, 58812109836480⟩, ⟨.count 10, 19898834155200⟩, ⟨.count 11, 8730542620800⟩, ⟨.count 12, 8730542620800⟩, ⟨.path 13, 72925561800⟩, ⟨.path 14, 2435592956160⟩, ⟨.privateRow 4 24, 5427517564909440⟩, ⟨.privateRow 5 20, 187933433688000⟩, ⟨.privateRow 6 17, 52667764749600⟩, ⟨.privateRow 6 18, 311551870069440⟩, ⟨.privateRow 6 19, 495935450010000⟩, ⟨.privateRow 7 14, 8106932433600⟩, ⟨.privateRow 7 15, 76928120755200⟩, ⟨.privateRow 7 16, 121358321884800⟩, ⟨.privateRow 7 17, 230138615266560⟩, ⟨.privateRow 7 18, 261264322519200⟩, ⟨.privateRow 8 12, 18366842293800⟩, ⟨.privateRow 8 13, 33667568359425⟩, ⟨.privateRow 8 14, 58314638982600⟩, ⟨.privateRow 8 15, 82829920773600⟩, ⟨.privateRow 8 16, 103781018381040⟩, ⟨.privateRow 8 17, 93022443463950⟩, ⟨.privateRow 9 9, 3303816909120⟩, ⟨.privateRow 9 10, 9446623490304⟩, ⟨.privateRow 9 11, 17221999674880⟩, ⟨.privateRow 9 12, 22928697792000⟩, ⟨.privateRow 9 13, 35162795828160⟩, ⟨.privateRow 9 14, 36380200496640⟩, ⟨.privateRow 9 15, 3393447273216⟩, ⟨.privateRow 10 6, 396842846400⟩, ⟨.privateRow 10 7, 2751443735040⟩, ⟨.privateRow 10 8, 5038358008320⟩, ⟨.privateRow 10 9, 7826874767712⟩, ⟨.privateRow 10 10, 10604522728800⟩, ⟨.privateRow 10 11, 4983920962020⟩, ⟨.privateRow 11 4, 676252605600⟩, ⟨.privateRow 11 5, 1648424131200⟩, ⟨.privateRow 11 6, 2820418801200⟩, ⟨.privateRow 11 7, 1571909976000⟩, ⟨.privateRow 12 2, 737938721520⟩, ⟨.privateRow 12 3, 486267467400⟩, ⟨.privateRow 13 0, 265742977500⟩, ⟨.privateRow 14 0, 162138648672⟩, ⟨.privateRow 15 0, 212909336640⟩, ⟨.privateRow 16 0, 413377965000⟩, ⟨.privateRow 16 9, 53739135450⟩, ⟨.privateRow 17 0, 982658476800⟩, ⟨.privateRow 18 0, 2784199017600⟩, ⟨.privateRow 19 0, 10023116463360⟩, ⟨.privateRow 20 0, 47609803200960⟩, ⟨.privateRow 21 0, 297561270006000⟩, ⟨.privateRow 21 5, 52899781334400⟩, ⟨.privateRow 22 0, 3094637208062400⟩, ⟨.privateRow 23 0, 73319096929478400⟩, ⟨.hall 14 5, 114528960⟩, ⟨.hall 20 7, 59512254001200⟩, ⟨.hall 6 17, 67241990400⟩, ⟨.hall 6 18, 831834169920⟩, ⟨.hall 7 20, 207013385779200⟩, ⟨.hall 5 21, 200759457225600⟩, ⟨.hall 4 23, 8173016216164800⟩]
  caps := #[0, 837474409044000, 813267345363200, 202445016446400, 0, 50463607194000, 4160725027680, 2992783522560, 925251432105, 1615017404000, 242221048160, 599842631200, 0, 135113615000, 3513226080, 863920577520, 512588676600, 0, 0, 0, 428488228808640, 0, 28327832904571200, 0] }

theorem case_51_28_13_checked :
    (Witness.linear .positive case_51_28_13).check 51 28 13 = true := by
  change case_51_28_13.check 51 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_28_14 : Certificate := {
  objectiveScale := 47139592500000
  eta := 88807756155830712000
  rows := #[⟨.count 2, 20707645853241547200⟩, ⟨.count 3, 4678139262526329600⟩, ⟨.count 4, 1007661484748318400⟩, ⟨.count 5, 239615127952200000⟩, ⟨.count 6, 55164727235217600⟩, ⟨.count 7, 13798490331225600⟩, ⟨.count 8, 3537324851860800⟩, ⟨.count 9, 955954732692960⟩, ⟨.count 10, 300693493900800⟩, ⟨.count 11, 106013731824000⟩, ⟨.count 12, 47706179320800⟩, ⟨.count 13, 50115582316800⟩, ⟨.path 15, 10713504569040⟩, ⟨.privateRow 3 25, 14838388664299200⟩, ⟨.privateRow 7 16, 1406020503888000⟩, ⟨.privateRow 7 17, 2884151762331840⟩, ⟨.privateRow 8 14, 765045686304900⟩, ⟨.privateRow 8 15, 1338373168382250⟩, ⟨.privateRow 8 16, 2282816978261820⟩, ⟨.privateRow 9 11, 84887134492160⟩, ⟨.privateRow 9 12, 188194452345900⟩, ⟨.privateRow 9 13, 651641780069280⟩, ⟨.privateRow 9 14, 939388748538240⟩, ⟨.privateRow 9 17, 3348277738565760⟩, ⟨.privateRow 10 8, 4271214402000⟩, ⟨.privateRow 10 9, 46795424988312⟩, ⟨.privateRow 10 10, 107609292030240⟩, ⟨.privateRow 10 11, 199366050904020⟩, ⟨.privateRow 10 12, 443254427169840⟩, ⟨.privateRow 10 13, 583742126527560⟩, ⟨.privateRow 10 14, 254587158169344⟩, ⟨.privateRow 11 6, 6425074656000⟩, ⟨.privateRow 11 7, 21947470927200⟩, ⟨.privateRow 11 8, 49778265897360⟩, ⟨.privateRow 11 9, 97232796460800⟩, ⟨.privateRow 11 10, 140347724517000⟩, ⟨.privateRow 11 11, 254432956377600⟩, ⟨.privateRow 11 13, 586545065346240⟩, ⟨.privateRow 11 16, 1097964945277200⟩, ⟨.privateRow 12 4, 5368644111600⟩, ⟨.privateRow 12 5, 12552320330550⟩, ⟨.privateRow 12 6, 23210582194800⟩, ⟨.privateRow 12 7, 47882868873840⟩, ⟨.privateRow 12 9, 266028208295850⟩, ⟨.privateRow 12 10, 104120629470000⟩, ⟨.privateRow 12 11, 85252709341800⟩, ⟨.privateRow 12 12, 283321698299640⟩, ⟨.privateRow 12 13, 302801721522300⟩, ⟨.privateRow 13 3, 10712576397600⟩, ⟨.privateRow 13 5, 57738057249600⟩, ⟨.privateRow 13 7, 48884109674400⟩, ⟨.privateRow 13 9, 68702405428800⟩, ⟨.privateRow 13 12, 15661119474000⟩, ⟨.privateRow 14 0, 4719217334832⟩, ⟨.privateRow 14 2, 10167680643120⟩, ⟨.privateRow 14 4, 61904134066320⟩, ⟨.privateRow 14 5, 4698335842200⟩, ⟨.privateRow 14 7, 99448108659900⟩, ⟨.privateRow 14 8, 4116637118880⟩, ⟨.privateRow 14 10, 51744338742096⟩, ⟨.privateRow 15 0, 18723738393360⟩, ⟨.privateRow 15 1, 1424224882080⟩, ⟨.privateRow 15 3, 74679810922080⟩, ⟨.privateRow 15 4, 17832794707728⟩, ⟨.privateRow 15 6, 86484181984200⟩, ⟨.privateRow 15 7, 56101610204640⟩, ⟨.privateRow 15 9, 25141317128928⟩, ⟨.privateRow 16 0, 50878559932200⟩, ⟨.privateRow 16 3, 33071063955930⟩, ⟨.privateRow 16 4, 194284887696900⟩, ⟨.privateRow 16 5, 130183055627625⟩, ⟨.privateRow 16 10, 164441754477000⟩, ⟨.privateRow 17 0, 156263169862800⟩, ⟨.privateRow 17 3, 273315536894400⟩, ⟨.privateRow 17 4, 315310538743200⟩, ⟨.privateRow 17 5, 29830703760000⟩, ⟨.privateRow 17 8, 244313463794400⟩, ⟨.privateRow 18 0, 508812370466400⟩, ⟨.privateRow 18 3, 1498334102565300⟩, ⟨.privateRow 19 0, 2287525754850336⟩, ⟨.privateRow 19 3, 1131896223469440⟩, ⟨.privateRow 19 5, 4745444489577792⟩, ⟨.privateRow 19 8, 7646384971985760⟩, ⟨.privateRow 20 0, 11735816489036640⟩, ⟨.privateRow 20 2, 3410902329325920⟩, ⟨.privateRow 20 4, 5179946588264448⟩, ⟨.privateRow 20 7, 36421499448734400⟩, ⟨.privateRow 21 0, 95943672158934600⟩, ⟨.privateRow 21 4, 49910943689006400⟩, ⟨.privateRow 21 7, 315652995222364800⟩, ⟨.privateRow 23 3, 5608910915105097600⟩, ⟨.privateRow 23 4, 16670929664340151200⟩, ⟨.hall 14 3, 390858708240⟩, ⟨.hall 17 4, 3406425313200⟩, ⟨.hall 19 4, 258547681271880⟩, ⟨.hall 21 4, 252927079505100000⟩, ⟨.hall 17 7, 21890764775880⟩, ⟨.hall 10 8, 170619518160⟩, ⟨.hall 16 9, 26532151092720⟩, ⟨.hall 11 10, 243860552100⟩, ⟨.hall 14 10, 1003187792880⟩, ⟨.hall 15 10, 13271186401200⟩, ⟨.hall 17 10, 374348213366400⟩, ⟨.hall 12 12, 1251631902510⟩, ⟨.hall 13 12, 3460361636160⟩, ⟨.hall 14 12, 31804119547200⟩, ⟨.hall 8 13, 720373784130⟩, ⟨.hall 9 13, 2062666946340⟩, ⟨.hall 13 13, 20762169816960⟩, ⟨.hall 12 14, 9276201534600⟩, ⟨.hall 7 15, 2363264904000⟩, ⟨.hall 11 16, 3851104711053600⟩, ⟨.hall 10 17, 4708428563638800⟩, ⟨.hall 8 19, 8517352029666480⟩, ⟨.hall 5 20, 638332255454400⟩, ⟨.hall 7 20, 21101444354390400⟩, ⟨.hall 6 21, 102574637602164000⟩, ⟨.hall 3 24, 200561056964364096⟩]
  caps := #[0, 14920775644320000, 0, 2481354097185600, 22147037640000, 0, 0, 0, 3300699573990, 3977690240160, 1368958674096, 0, 0, 0, 9330621961284, 0, 0, 16622331039600, 0, 1324196872187904, 245700591519240, 0, 66772748989346400, 0] }

theorem case_51_28_14_checked :
    (Witness.linear .positive case_51_28_14).check 51 28 14 = true := by
  change case_51_28_14.check 51 28 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_28_15 : Certificate := {
  objectiveScale := 2320718400000
  eta := 4554243905427216000
  rows := #[⟨.count 2, 1065562330025793600⟩, ⟨.count 3, 242498701457812800⟩, ⟨.count 4, 61760901629306880⟩, ⟨.count 5, 15777734579006400⟩, ⟨.count 6, 4057755898996800⟩, ⟨.count 7, 1128885617059200⟩, ⟨.count 8, 337316419440000⟩, ⟨.count 9, 106591988543040⟩, ⟨.count 10, 36622925539200⟩, ⟨.count 11, 13863334161600⟩, ⟨.count 12, 6523921958400⟩, ⟨.count 13, 6264447789600⟩, ⟨.count 14, 674632838880⟩, ⟨.path 14, 536362226400⟩, ⟨.privateRow 3 25, 12763089550411200⟩, ⟨.privateRow 5 20, 474315073792560⟩, ⟨.privateRow 6 18, 289813700816640⟩, ⟨.privateRow 6 19, 903164713050600⟩, ⟨.privateRow 7 16, 135354906086400⟩, ⟨.privateRow 7 17, 359932682229120⟩, ⟨.privateRow 7 18, 647326271592000⟩, ⟨.privateRow 8 13, 4708375021350⟩, ⟨.privateRow 8 14, 52826160687300⟩, ⟨.privateRow 8 15, 145327157375400⟩, ⟨.privateRow 8 16, 251609939200620⟩, ⟨.privateRow 8 17, 345397958655750⟩, ⟨.privateRow 9 11, 4214373042880⟩, ⟨.privateRow 9 12, 21578880943620⟩, ⟨.privateRow 9 13, 57397333593600⟩, ⟨.privateRow 9 14, 102681616717680⟩, ⟨.privateRow 9 15, 141597936960480⟩, ⟨.privateRow 9 16, 156720956432040⟩, ⟨.privateRow 10 9, 2438315831952⟩, ⟨.privateRow 10 10, 9626903526240⟩, ⟨.privateRow 10 11, 23780807570520⟩, ⟨.privateRow 10 12, 42680853072000⟩, ⟨.privateRow 10 13, 60749080872480⟩, ⟨.privateRow 10 14, 69140228373216⟩, ⟨.privateRow 10 15, 30430759839480⟩, ⟨.privateRow 11 7, 1243454133600⟩, ⟨.privateRow 11 8, 4488903120240⟩, ⟨.privateRow 11 9, 10720813672800⟩, ⟨.privateRow 11 10, 18867478845600⟩, ⟨.privateRow 11 11, 27536034240000⟩, ⟨.privateRow 11 12, 7673021848800⟩, ⟨.privateRow 12 5, 622943937000⟩, ⟨.privateRow 12 6, 2199352478400⟩, ⟨.privateRow 12 7, 5188556682540⟩, ⟨.privateRow 12 8, 9196917760800⟩, ⟨.privateRow 12 9, 1958026056525⟩, ⟨.privateRow 13 3, 333609645600⟩, ⟨.privateRow 13 4, 1167633759600⟩, ⟨.privateRow 13 5, 2705944903200⟩, ⟨.privateRow 13 6, 333609645600⟩, ⟨.privateRow 14 0, 212027463648⟩, ⟨.privateRow 14 2, 696873481920⟩, ⟨.privateRow 15 0, 219523384080⟩, ⟨.privateRow 16 0, 183794202900⟩, ⟨.privateRow 17 0, 374796021600⟩, ⟨.privateRow 18 0, 1075713256800⟩, ⟨.privateRow 19 0, 3604466882016⟩, ⟨.privateRow 20 0, 17294159282400⟩, ⟨.privateRow 21 0, 116735575156200⟩, ⟨.privateRow 22 0, 1245179468332800⟩, ⟨.privateRow 23 0, 27964655559640800⟩, ⟨.hall 18 6, 19504690920⟩, ⟨.hall 8 15, 1363422060⟩, ⟨.hall 7 16, 31318647360⟩, ⟨.hall 8 16, 620560100160⟩, ⟨.hall 7 17, 1948939312320⟩, ⟨.hall 6 20, 285560496093600⟩, ⟨.hall 5 22, 12309325636608000⟩, ⟨.hall 4 23, 20387219670057240⟩, ⟨.hall 3 24, 20943918657357696⟩, ⟨.assumptionRow 15, 3579243988320⟩]
  caps := #[0, 0, 0, 96804458150400, 8871957254160, 8195539672320, 0, 0, 24599615040, 86634628080, 328548366432, 113634444000, 0, 0, 260561421120, 357390633600, 0, 535422888000, 1903184992800, 0, 17294159282400, 155647433541600, 2179064069582400, 0] }

theorem case_51_28_15_checked :
    (Witness.linear .conditional case_51_28_15).check 51 28 15 = true := by
  change case_51_28_15.check 51 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_28_16 : Certificate := {
  objectiveScale := 446292000000
  eta := 267661703213704800
  rows := #[⟨.count 2, 72272291641149600⟩, ⟨.count 3, 19922871493324800⟩, ⟨.count 4, 5634437094205920⟩, ⟨.count 5, 1641124694008800⟩, ⟨.count 6, 495159086822400⟩, ⟨.count 7, 155915144985600⟩, ⟨.count 8, 51347054959200⟩, ⟨.count 9, 17877770230320⟩, ⟨.count 10, 6585701522400⟩, ⟨.count 11, 2650343295600⟩, ⟨.count 12, 1155277846800⟩, ⟨.count 13, 481880599200⟩, ⟨.count 14, 449755225920⟩, ⟨.count 15, 374796021600⟩, ⟨.path 13, 47244451800⟩, ⟨.privateRow 2 26, 7081958226142800⟩, ⟨.privateRow 5 20, 266239031058000⟩, ⟨.privateRow 6 18, 88078849818960⟩, ⟨.privateRow 6 19, 255316404142800⟩, ⟨.privateRow 7 16, 29135928822000⟩, ⟨.privateRow 7 17, 90015295930560⟩, ⟨.privateRow 7 18, 174480933627000⟩, ⟨.privateRow 8 14, 9671075914500⟩, ⟨.privateRow 8 15, 32275403235075⟩, ⟨.privateRow 8 16, 65228562609210⟩, ⟨.privateRow 8 17, 102143628261675⟩, ⟨.privateRow 9 12, 3227930736030⟩, ⟨.privateRow 9 13, 11797150965600⟩, ⟨.privateRow 9 14, 25169635050560⟩, ⟨.privateRow 9 15, 40635384661872⟩, ⟨.privateRow 9 16, 52402730420040⟩, ⟨.privateRow 10 10, 1083338976720⟩, ⟨.privateRow 10 11, 4412219236425⟩, ⟨.privateRow 10 12, 10051799832360⟩, ⟨.privateRow 10 13, 16962197091840⟩, ⟨.privateRow 10 14, 22971248163864⟩, ⟨.privateRow 10 15, 24505636305150⟩, ⟨.privateRow 11 8, 363881631960⟩, ⟨.privateRow 11 9, 1697565130800⟩, ⟨.privateRow 11 10, 4169348325450⟩, ⟨.privateRow 11 11, 7459441070400⟩, ⟨.privateRow 11 12, 10643589217800⟩, ⟨.privateRow 11 13, 8404491886560⟩, ⟨.privateRow 12 6, 119440490400⟩, ⟨.privateRow 12 7, 676743640650⟩, ⟨.privateRow 12 8, 1805908181000⟩, ⟨.privateRow 12 9, 3470080885425⟩, ⟨.privateRow 12 10, 4147835798700⟩, ⟨.privateRow 13 4, 33978760200⟩, ⟨.privateRow 13 5, 284185994400⟩, ⟨.privateRow 13 6, 824757179400⟩, ⟨.privateRow 13 7, 1712666802000⟩, ⟨.privateRow 13 8, 57918341250⟩, ⟨.privateRow 14 3, 129840050340⟩, ⟨.privateRow 14 4, 404487654480⟩, ⟨.privateRow 14 5, 199177314336⟩, ⟨.privateRow 15 1, 49972802880⟩, ⟨.privateRow 15 2, 98904505700⟩, ⟨.privateRow 16 0, 23424751350⟩, ⟨.hall 8 16, 217074197340⟩, ⟨.hall 8 17, 525262377640⟩, ⟨.hall 7 18, 2923033233120⟩, ⟨.hall 9 18, 50396256630720⟩, ⟨.hall 7 19, 14158365901680⟩, ⟨.hall 6 21, 1867645081738800⟩, ⟨.hall 5 22, 3608503505006400⟩, ⟨.hall 4 23, 6168394262050020⟩, ⟨.hall 3 24, 8965292171996160⟩, ⟨.hall 2 25, 9023560185578400⟩, ⟨.assumptionRow 16, 460179119400⟩]
  caps := #[0, 584345937520800, 112726799094000, 19199715612000, 814853728080, 4374851180700, 177859456320, 0, 29732195220, 96216574636, 36087235635, 0, 33439476325, 39430091400, 29187127788, 85383097800, 0, 446292000000, 0, 0, 0, 0, 0, 0] }

theorem case_51_28_16_checked :
    (Witness.linear .conditional case_51_28_16).check 51 28 16 = true := by
  change case_51_28_16.check 51 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_28_17 : Certificate := {
  objectiveScale := 3560071284000000
  eta := 1848327904165252910400
  rows := #[⟨.count 2, 473187394483267464000⟩, ⟨.count 3, 127746800959622644800⟩, ⟨.count 4, 36254707658951221440⟩, ⟨.count 5, 10746008037981216000⟩, ⟨.count 6, 3306091662135662400⟩, ⟨.count 7, 1046411752506120000⟩, ⟨.count 8, 337841508666261600⟩, ⟨.count 9, 110620670979218400⟩, ⟨.count 10, 36304081209396000⟩, ⟨.count 11, 15540118019949600⟩, ⟨.count 12, 6505165682769600⟩, ⟨.count 13, 3843961539818400⟩, ⟨.count 14, 2391798291442560⟩, ⟨.count 15, 1993165242868800⟩, ⟨.count 16, 1993165242868800⟩, ⟨.path 6, 5435307203040000⟩, ⟨.path 12, 441174915417600⟩, ⟨.privateRow 2 26, 67598199211895352000⟩, ⟨.privateRow 5 20, 1907416426741665840⟩, ⟨.privateRow 6 18, 557792038848364320⟩, ⟨.privateRow 6 19, 1918469002576526400⟩, ⟨.privateRow 7 16, 158836287330520800⟩, ⟨.privateRow 7 17, 631320853784100480⟩, ⟨.privateRow 7 18, 1407815321722009200⟩, ⟨.privateRow 8 14, 43244567322957000⟩, ⟨.privateRow 8 15, 207164612430675900⟩, ⟨.privateRow 8 16, 502925419906869960⟩, ⟨.privateRow 8 17, 911063375232560550⟩, ⟨.privateRow 9 12, 10729872890777040⟩, ⟨.privateRow 9 13, 67368985208965440⟩, ⟨.privateRow 9 14, 182385692862733360⟩, ⟨.privateRow 9 15, 348963370721469504⟩, ⟨.privateRow 9 16, 522209293631625600⟩, ⟨.privateRow 10 10, 2045367189705840⟩, ⟨.privateRow 10 11, 21419407913543640⟩, ⟨.privateRow 10 12, 66903235371601200⟩, ⟨.privateRow 10 13, 138937854322547280⟩, ⟨.privateRow 10 14, 223001022129998112⟩, ⟨.privateRow 10 15, 277993163025477900⟩, ⟨.privateRow 11 9, 6413903537949600⟩, ⟨.privateRow 11 10, 24648992694433800⟩, ⟨.privateRow 11 11, 56983561727637600⟩, ⟨.privateRow 11 12, 99034029072871200⟩, ⟨.privateRow 11 13, 137370700771698240⟩, ⟨.privateRow 11 14, 147113664828391800⟩, ⟨.privateRow 12 7, 1282963231879560⟩, ⟨.privateRow 12 8, 8964680485668600⟩, ⟨.privateRow 12 9, 23953917383948475⟩, ⟨.privateRow 12 10, 45845929573804800⟩, ⟨.privateRow 12 11, 69508899980704800⟩, ⟨.privateRow 12 12, 23707714932760320⟩, ⟨.privateRow 13 5, 191152710604800⟩, ⟨.privateRow 13 6, 2786050757064960⟩, ⟨.privateRow 13 7, 10173903904533600⟩, ⟨.privateRow 13 8, 22139740022607900⟩, ⟨.privateRow 13 9, 22627275437685600⟩, ⟨.privateRow 14 4, 792089044568640⟩, ⟨.privateRow 14 5, 4001991069788712⟩, ⟨.privateRow 14 6, 10924443783533280⟩, ⟨.privateRow 14 7, 1959352618212990⟩, ⟨.privateRow 15 2, 127341112738840⟩, ⟨.privateRow 15 3, 1636811457022560⟩, ⟨.privateRow 15 4, 3009679516731888⟩, ⟨.privateRow 16 1, 633245207369775⟩, ⟨.privateRow 16 2, 407692890586800⟩, ⟨.privateRow 17 0, 166097103572400⟩, ⟨.hall 9 14, 331145172806448⟩, ⟨.hall 9 15, 453321676948140⟩, ⟨.hall 8 16, 3956967808914120⟩, ⟨.hall 8 17, 1603565545541960⟩, ⟨.hall 10 17, 73201366360122000⟩, ⟨.hall 7 18, 287735132805120⟩, ⟨.hall 7 19, 460530320627897520⟩, ⟨.hall 5 21, 1479570677273052000⟩, ⟨.hall 6 21, 18294616632720355200⟩, ⟨.hall 4 23, 52694405766606043440⟩, ⟨.hall 3 24, 75025723794688098432⟩, ⟨.hall 2 25, 77775070961378498400⟩, ⟨.assumptionRow 17, 2427683809985280⟩]
  caps := #[0, 0, 450648882964082880, 264781840012192800, 0, 1697560443398160, 0, 653321526530400, 0, 0, 352353240608148, 175252023767520, 292247214248265, 0, 908782527782766, 434518567116480, 434518567116480, 1946773558403520, 3560071284000000, 0, 0, 0, 0, 0] }

theorem case_51_28_17_checked :
    (Witness.linear .conditional case_51_28_17).check 51 28 17 = true := by
  change case_51_28_17.check 51 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_28_18 : Certificate := {
  objectiveScale := 369635760000000
  eta := 237252137767992547200
  rows := #[⟨.count 2, 63164530184985028800⟩, ⟨.count 3, 17260989084896356800⟩, ⟨.count 4, 4747558017885883200⟩, ⟨.count 5, 1342024939876420800⟩, ⟨.count 6, 385011676133884800⟩, ⟨.count 7, 111746183432083200⟩, ⟨.count 8, 32365510445268000⟩, ⟨.count 9, 9266756674855680⟩, ⟨.count 10, 2482166966479200⟩, ⟨.count 11, 576551603073600⟩, ⟨.count 12, 123546772087200⟩, ⟨.count 13, 48669940519200⟩, ⟨.count 14, 68137916726880⟩, ⟨.path 7, 40316519738880⟩, ⟨.path 12, 89415533188800⟩, ⟨.privateRow 2 26, 9243589783168540800⟩, ⟨.privateRow 4 21, 4323107466617940⟩, ⟨.privateRow 5 20, 255414980850709680⟩, ⟨.privateRow 6 18, 74281144774636800⟩, ⟨.privateRow 6 19, 251641167740562600⟩, ⟨.privateRow 7 16, 21166016354683200⟩, ⟨.privateRow 7 17, 80805079912677120⟩, ⟨.privateRow 7 18, 185424361721398800⟩, ⟨.privateRow 8 14, 5832281205550800⟩, ⟨.privateRow 8 15, 25738624863601650⟩, ⟨.privateRow 8 16, 64259733633175080⟩, ⟨.privateRow 8 17, 122864729947985025⟩, ⟨.privateRow 9 12, 1519854086991240⟩, ⟨.privateRow 9 13, 8064068366914560⟩, ⟨.privateRow 9 14, 22422421856234400⟩, ⟨.privateRow 9 15, 45756882345990816⟩, ⟨.privateRow 9 16, 75945386351835000⟩, ⟨.privateRow 10 10, 354749788673280⟩, ⟨.privateRow 10 11, 2446881259602780⟩, ⟨.privateRow 10 12, 7822650011164560⟩, ⟨.privateRow 10 13, 17454663001535760⟩, ⟨.privateRow 10 14, 30788604372445920⟩, ⟨.privateRow 10 15, 44082798625265400⟩, ⟨.privateRow 11 8, 63270922674960⟩, ⟨.privateRow 11 9, 694274621594400⟩, ⟨.privateRow 11 10, 2693694015658800⟩, ⟨.privateRow 11 11, 6782771271038400⟩, ⟨.privateRow 11 12, 13006105643361600⟩, ⟨.privateRow 11 13, 20150104143264480⟩, ⟨.privateRow 11 14, 24765512041116000⟩, ⟨.privateRow 12 6, 1559933991000⟩, ⟨.privateRow 12 7, 167131327795740⟩, ⟨.privateRow 12 8, 890756974060800⟩, ⟨.privateRow 12 9, 2654968654332225⟩, ⟨.privateRow 12 10, 5699330259975000⟩, ⟨.privateRow 12 11, 9676114552773900⟩, ⟨.privateRow 12 12, 13309419208571640⟩, ⟨.privateRow 12 13, 2185233531292350⟩, ⟨.privateRow 13 5, 15996414016800⟩, ⟨.privateRow 13 6, 262443294645840⟩, ⟨.privateRow 13 7, 1022484733300800⟩, ⟨.privateRow 13 8, 2563127540612100⟩, ⟨.privateRow 13 9, 4888387432368000⟩, ⟨.privateRow 13 10, 3918554185392000⟩, ⟨.privateRow 14 4, 38493498410640⟩, ⟨.privateRow 14 5, 364537854488808⟩, ⟨.privateRow 14 6, 1157263030123200⟩, ⟨.privateRow 14 7, 2568556110900780⟩, ⟨.privateRow 14 8, 240568563137760⟩, ⟨.privateRow 15 3, 76397058148320⟩, ⟨.privateRow 15 4, 495892616178960⟩, ⟨.privateRow 15 5, 847097310419360⟩, ⟨.privateRow 16 2, 144534974875200⟩, ⟨.privateRow 16 3, 264034427316660⟩, ⟨.privateRow 17 1, 97339881038400⟩, ⟨.privateRow 18 0, 16714929067200⟩, ⟨.hall 9 16, 1256672262605760⟩, ⟨.hall 9 17, 4162389930578880⟩, ⟨.hall 10 17, 60610299259910400⟩, ⟨.hall 8 18, 35408107507532760⟩, ⟨.hall 7 20, 1408324214405908800⟩, ⟨.hall 6 21, 2642454778769114400⟩, ⟨.hall 5 22, 4558481647221902400⟩, ⟨.hall 4 23, 7252602289906133160⟩, ⟨.hall 3 24, 10248437162318427072⟩, ⟨.hall 2 25, 10631821215805574400⟩, ⟨.assumptionRow 18, 52576053868800⟩]
  caps := #[0, 389499900500131200, 102018620402899200, 0, 0, 0, 32947050434760, 0, 232395740706285, 0, 110532121046100, 20827523839320, 18444814970400, 3906113349600, 24841839818484, 52576053868800, 52576053868800, 196278562180800, 248743624968000, 369635760000000, 0, 0, 0, 0] }

theorem case_51_28_18_checked :
    (Witness.linear .conditional case_51_28_18).check 51 28 18 = true := by
  change case_51_28_18.check 51 28 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_29_1_checked :
    (Witness.rising).check 51 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_29_2_checked :
    (Witness.rising).check 51 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_29_3_checked :
    (Witness.rising).check 51 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_29_4_checked :
    (Witness.rising).check 51 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_29_5_checked :
    (Witness.rising).check 51 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_29_6_checked :
    (Witness.rising).check 51 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_29_7_checked :
    (Witness.rising).check 51 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_29_8_checked :
    (Witness.rising).check 51 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_29_9_checked :
    (Witness.rising).check 51 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_29_10_checked :
    (Witness.linear .positive case_51_29_10).check 51 29 10 = true := by
  change case_51_29_10.check 51 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_29_11_checked :
    (Witness.linear .positive case_51_29_11).check 51 29 11 = true := by
  change case_51_29_11.check 51 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_29_12 : Certificate := {
  objectiveScale := 123079320000000
  eta := 163593235023898680000
  rows := #[⟨.count 2, 32941222834744224000⟩, ⟨.count 3, 4780928827637202240⟩, ⟨.count 4, 772220984803107840⟩, ⟨.count 5, 131462917113528000⟩, ⟨.count 6, 25082848949558400⟩, ⟨.count 7, 5265790404474600⟩, ⟨.count 8, 1243423281260160⟩, ⟨.count 9, 358326413565120⟩, ⟨.count 10, 148419224553600⟩, ⟨.count 11, 126333030423600⟩, ⟨.path 12, 21191865695000⟩, ⟨.path 13, 24208656472000⟩, ⟨.privateRow 5 20, 4342181103868608⟩, ⟨.privateRow 5 21, 9124307415503280⟩, ⟨.privateRow 5 22, 11627743163836800⟩, ⟨.privateRow 6 16, 80393746633200⟩, ⟨.privateRow 6 17, 1599124592894400⟩, ⟨.privateRow 6 18, 2488377871980000⟩, ⟨.privateRow 6 19, 3528136995102720⟩, ⟨.privateRow 6 20, 5133714963577200⟩, ⟨.privateRow 6 21, 4547989095249600⟩, ⟨.privateRow 7 13, 99343701196740⟩, ⟨.privateRow 7 14, 420472055803800⟩, ⟨.privateRow 7 15, 755126977304700⟩, ⟨.privateRow 7 16, 1103363155323000⟩, ⟨.privateRow 7 17, 1294913561841900⟩, ⟨.privateRow 7 18, 1664150555307240⟩, ⟨.privateRow 7 19, 1527481186030800⟩, ⟨.privateRow 7 20, 576155184204600⟩, ⟨.privateRow 8 10, 35060606170590⟩, ⟨.privateRow 8 11, 133258725479880⟩, ⟨.privateRow 8 12, 234213781858056⟩, ⟨.privateRow 8 13, 338844754328080⟩, ⟨.privateRow 8 14, 423742039545825⟩, ⟨.privateRow 8 15, 478151378785080⟩, ⟨.privateRow 8 16, 280484849364720⟩, ⟨.privateRow 9 7, 9625373746560⟩, ⟨.privateRow 9 8, 43347837012480⟩, ⟨.privateRow 9 9, 64825433793120⟩, ⟨.privateRow 9 10, 146309658374880⟩, ⟨.privateRow 9 11, 132458268262320⟩, ⟨.privateRow 9 12, 40834918924800⟩, ⟨.privateRow 10 4, 1722723142140⟩, ⟨.privateRow 10 5, 15124625740224⟩, ⟨.privateRow 10 6, 29229500345760⟩, ⟨.privateRow 10 7, 39551276872800⟩, ⟨.privateRow 11 2, 5716426716000⟩, ⟨.privateRow 11 3, 8392753769400⟩, ⟨.privateRow 12 0, 2699423727000⟩, ⟨.privateRow 13 0, 1434303430560⟩, ⟨.privateRow 14 0, 1914136824600⟩, ⟨.privateRow 15 0, 3394402635624⟩, ⟨.privateRow 16 0, 7383099180600⟩, ⟨.privateRow 17 0, 18846885657600⟩, ⟨.privateRow 18 0, 65080652036400⟩, ⟨.privateRow 19 0, 298187714784960⟩, ⟨.privateRow 20 0, 1928990526358896⟩, ⟨.privateRow 21 0, 19784518219065600⟩, ⟨.privateRow 22 0, 389507702437854000⟩, ⟨.hall 5 21, 42529648761600⟩, ⟨.hall 6 22, 147804652195200⟩, ⟨.hall 4 24, 40860236574533376⟩, ⟨.hall 3 25, 86975785863046080⟩]
  caps := #[0, 110502644304780000, 0, 1708794413165840, 211223833162160, 465109726553472, 27532643578440, 24313608770880, 45747592314697, 0, 0, 0, 109424879200, 74942227360, 3445446284280, 7324763582136, 0, 41227562376000, 169209695294640, 915862266839520, 6974042672220624, 0, 0] }

theorem case_51_29_12_checked :
    (Witness.linear .positive case_51_29_12).check 51 29 12 = true := by
  change case_51_29_12.check 51 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_29_13 : Certificate := {
  objectiveScale := 28959840000000
  eta := 57222222467233824000
  rows := #[⟨.count 2, 11439048715750656000⟩, ⟨.count 3, 2049721052309330400⟩, ⟨.count 4, 381254292475056000⟩, ⟨.count 5, 73836957946752000⟩, ⟨.count 6, 15410541562416000⟩, ⟨.count 7, 3435005537964000⟩, ⟨.count 8, 828299207736000⟩, ⟨.count 9, 212991224846400⟩, ⟨.count 10, 72282089880000⟩, ⟨.count 11, 30920671782000⟩, ⟨.count 12, 28912835952000⟩, ⟨.path 13, 2013191544000⟩, ⟨.path 14, 6814080000000⟩, ⟨.privateRow 6 18, 1279571465172000⟩, ⟨.privateRow 6 19, 2054738874988800⟩, ⟨.privateRow 6 20, 2822481754092000⟩, ⟨.privateRow 6 22, 3984884843940000⟩, ⟨.privateRow 7 15, 253188098163000⟩, ⟨.privateRow 7 16, 535461132492000⟩, ⟨.privateRow 7 17, 971424438484500⟩, ⟨.privateRow 7 18, 1486762275398400⟩, ⟨.privateRow 7 19, 1714892582403000⟩, ⟨.privateRow 7 20, 1418201374590000⟩, ⟨.privateRow 8 12, 47383587030780⟩, ⟨.privateRow 8 13, 138455896979400⟩, ⟨.privateRow 8 14, 250925936461200⟩, ⟨.privateRow 8 15, 364382046428400⟩, ⟨.privateRow 8 16, 598080751468200⟩, ⟨.privateRow 8 17, 699669213122880⟩, ⟨.privateRow 8 18, 706795022483550⟩, ⟨.privateRow 8 19, 528243759443400⟩, ⟨.privateRow 8 21, 3727346434812000⟩, ⟨.privateRow 9 10, 50874909321600⟩, ⟨.privateRow 9 11, 61530798288960⟩, ⟨.privateRow 9 12, 110594572088000⟩, ⟨.privateRow 9 13, 153478970845200⟩, ⟨.privateRow 9 14, 223332535483200⟩, ⟨.privateRow 9 15, 281552125654800⟩, ⟨.privateRow 9 16, 179441626684320⟩, ⟨.privateRow 9 17, 460436912535600⟩, ⟨.privateRow 10 7, 7598886372000⟩, ⟨.privateRow 10 8, 21162589648200⟩, ⟨.privateRow 10 9, 18793343368800⟩, ⟨.privateRow 10 10, 89677979511120⟩, ⟨.privateRow 10 11, 46528248967200⟩, ⟨.privateRow 10 12, 97460351188200⟩, ⟨.privateRow 10 13, 115031783037600⟩, ⟨.privateRow 10 15, 66114018210240⟩, ⟨.privateRow 10 17, 203514239728800⟩, ⟨.privateRow 11 5, 8232126903000⟩, ⟨.privateRow 11 6, 11151211302000⟩, ⟨.privateRow 11 7, 5320764949500⟩, ⟨.privateRow 11 8, 40594789872000⟩, ⟨.privateRow 11 9, 49031350968600⟩, ⟨.privateRow 11 10, 32259229002000⟩, ⟨.privateRow 11 11, 53257845390750⟩, ⟨.privateRow 11 12, 78764531274000⟩, ⟨.privateRow 11 15, 17568563512500⟩, ⟨.privateRow 12 3, 7495920432000⟩, ⟨.privateRow 12 4, 3728837970000⟩, ⟨.privateRow 12 6, 31255311087000⟩, ⟨.privateRow 12 7, 18399077424000⟩, ⟨.privateRow 12 8, 42686589745800⟩, ⟨.privateRow 12 9, 23870937090000⟩, ⟨.privateRow 12 10, 24495597126000⟩, ⟨.privateRow 12 11, 84157004646000⟩, ⟨.privateRow 13 0, 1700755056000⟩, ⟨.privateRow 13 1, 2319050383650⟩, ⟨.privateRow 13 2, 5686191070560⟩, ⟨.privateRow 13 4, 7042870296000⟩, ⟨.privateRow 13 5, 28270328486400⟩, ⟨.privateRow 13 6, 19538067931200⟩, ⟨.privateRow 13 7, 42019988250240⟩, ⟨.privateRow 13 8, 25111333447200⟩, ⟨.privateRow 13 9, 23672384435700⟩, ⟨.privateRow 13 11, 24334970259600⟩, ⟨.privateRow 14 0, 14399529294150⟩, ⟨.privateRow 14 3, 8620308496800⟩, ⟨.privateRow 14 4, 37702695030000⟩, ⟨.privateRow 14 6, 96681310886160⟩, ⟨.privateRow 14 8, 50463607194000⟩, ⟨.privateRow 15 0, 37354670152800⟩, ⟨.privateRow 15 3, 56539541508450⟩, ⟨.privateRow 15 5, 130213507804380⟩, ⟨.privateRow 15 7, 113586619296150⟩, ⟨.privateRow 16 0, 114848209476000⟩, ⟨.privateRow 16 4, 115892284107600⟩, ⟨.privateRow 16 6, 230022692274375⟩, ⟨.privateRow 16 10, 595122540012000⟩, ⟨.privateRow 17 0, 376402290264000⟩, ⟨.privateRow 17 3, 103711413405600⟩, ⟨.privateRow 17 4, 96673577000000⟩, ⟨.privateRow 17 5, 307131954129000⟩, ⟨.privateRow 17 8, 484450629062400⟩, ⟨.privateRow 18 0, 1390359384414000⟩, ⟨.privateRow 18 3, 943998144689600⟩, ⟨.privateRow 18 5, 6761626185600⟩, ⟨.privateRow 18 6, 966349075692000⟩, ⟨.privateRow 18 9, 1206950274129600⟩, ⟨.privateRow 19 0, 7057754677864800⟩, ⟨.privateRow 19 2, 2875381535426400⟩, ⟨.privateRow 19 6, 4004235027112320⟩, ⟨.privateRow 20 0, 59555896320800880⟩, ⟨.privateRow 20 5, 7149405447344160⟩, ⟨.privateRow 20 8, 70819582261428000⟩, ⟨.privateRow 21 0, 628757984310456000⟩, ⟨.privateRow 22 0, 12287197522357758000⟩, ⟨.privateRow 22 5, 3871470496958064000⟩, ⟨.hall 12 1, 992107116000⟩, ⟨.hall 18 5, 11525499180000⟩, ⟨.hall 18 8, 195349527434880⟩, ⟨.hall 20 8, 169367466572304000⟩, ⟨.hall 15 10, 1054113810750⟩, ⟨.hall 17 10, 328988971038000⟩, ⟨.hall 16 11, 197035622784000⟩, ⟨.hall 13 13, 4165112012490⟩, ⟨.hall 14 13, 29141283050880⟩, ⟨.hall 10 15, 359296938000⟩, ⟨.hall 11 15, 1252272771750⟩, ⟨.hall 12 16, 414984233664000⟩, ⟨.hall 7 18, 310349935350⟩, ⟨.hall 5 19, 3563996147400⟩, ⟨.hall 9 19, 391841209239480⟩, ⟨.hall 7 20, 5220373158000⟩, ⟨.hall 8 20, 66356743252800⟩, ⟨.hall 6 22, 10288220630688000⟩, ⟨.hall 4 24, 86082533433921024⟩, ⟨.hall 3 25, 78835425088820400⟩]
  caps := #[0, 36130677205896000, 2169987840384000, 393943068573600, 0, 0, 0, 1165937379750, 0, 5565009274240, 3129354283920, 490042936800, 5173663216800, 2447266068660, 0, 1624116093600, 30995965625625, 0, 320997958273200, 336913392029760, 0, 95175523250808000, 0] }

theorem case_51_29_13_checked :
    (Witness.linear .positive case_51_29_13).check 51 29 13 = true := by
  change case_51_29_13.check 51 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_29_14 : Certificate := {
  objectiveScale := 17035200000000
  eta := 44474697660176784000
  rows := #[⟨.count 2, 9496568745151488000⟩, ⟨.count 3, 2215641216464676000⟩, ⟨.count 4, 500529378389040000⟩, ⟨.count 5, 115961889083040000⟩, ⟨.count 6, 28022963112144000⟩, ⟨.count 7, 6577670179080000⟩, ⟨.count 8, 1744300684526400⟩, ⟨.count 9, 463569136430400⟩, ⟨.count 10, 134926567776000⟩, ⟨.count 11, 44172388260000⟩, ⟨.count 12, 19275223968000⟩, ⟨.count 13, 18793343368800⟩, ⟨.path 14, 2555280000000⟩, ⟨.path 15, 1703502964800⟩, ⟨.privateRow 3 26, 246856829596977600⟩, ⟨.privateRow 7 16, 456782651325000⟩, ⟨.privateRow 7 17, 1378613544808500⟩, ⟨.privateRow 7 18, 2541277653314400⟩, ⟨.privateRow 7 19, 4289841642586500⟩, ⟨.privateRow 8 15, 1138911410637000⟩, ⟨.privateRow 8 16, 1065826186425000⟩, ⟨.privateRow 9 12, 124438228314400⟩, ⟨.privateRow 9 13, 127551117493800⟩, ⟨.privateRow 9 14, 802744238181600⟩, ⟨.privateRow 9 15, 798137051712000⟩, ⟨.privateRow 9 16, 540969869119680⟩, ⟨.privateRow 9 17, 579983457853800⟩, ⟨.privateRow 10 9, 13755500740800⟩, ⟨.privateRow 10 10, 39466021074480⟩, ⟨.privateRow 10 11, 114205702010400⟩, ⟨.privateRow 10 12, 146973582756000⟩, ⟨.privateRow 10 13, 526213614326400⟩, ⟨.privateRow 10 14, 554724883112400⟩, ⟨.privateRow 10 15, 494891375378400⟩, ⟨.privateRow 10 17, 1563541917537600⟩, ⟨.privateRow 11 6, 710464986000⟩, ⟨.privateRow 11 8, 39828161646000⟩, ⟨.privateRow 11 9, 31763962830600⟩, ⟨.privateRow 11 10, 104362844586000⟩, ⟨.privateRow 11 11, 121072500549000⟩, ⟨.privateRow 11 12, 346552464258000⟩, ⟨.privateRow 11 13, 396413720703000⟩, ⟨.privateRow 12 5, 5807279016000⟩, ⟨.privateRow 12 6, 5822723907000⟩, ⟨.privateRow 12 7, 36615624318000⟩, ⟨.privateRow 12 8, 33289918061400⟩, ⟨.privateRow 12 9, 90040282332000⟩, ⟨.privateRow 12 10, 102249039642750⟩, ⟨.privateRow 12 11, 246963807090000⟩, ⟨.privateRow 12 13, 423573046696800⟩, ⟨.privateRow 13 2, 1028011944960⟩, ⟨.privateRow 13 3, 2271722824800⟩, ⟨.privateRow 13 4, 6746328388800⟩, ⟨.privateRow 13 5, 6585701522400⟩, ⟨.privateRow 13 6, 40740814296000⟩, ⟨.privateRow 13 7, 33008821045200⟩, ⟨.privateRow 13 8, 82240955596800⟩, ⟨.privateRow 13 9, 93484836244800⟩, ⟨.privateRow 13 10, 189034875057600⟩, ⟨.privateRow 13 11, 70113627183600⟩, ⟨.privateRow 13 12, 160948120132800⟩, ⟨.privateRow 14 0, 1957639934250⟩, ⟨.privateRow 14 2, 3828273649200⟩, ⟨.privateRow 14 3, 10601373182400⟩, ⟨.privateRow 14 4, 6670476813000⟩, ⟨.privateRow 14 5, 49609364313600⟩, ⟨.privateRow 14 6, 41206145460480⟩, ⟨.privateRow 14 7, 66975454145600⟩, ⟨.privateRow 14 8, 160526474608500⟩, ⟨.privateRow 14 9, 173515260204000⟩, ⟨.privateRow 14 11, 503661602283840⟩, ⟨.privateRow 15 0, 9176255928840⟩, ⟨.privateRow 15 2, 17240616993600⟩, ⟨.privateRow 15 3, 9947711073300⟩, ⟨.privateRow 15 4, 69098757436800⟩, ⟨.privateRow 15 6, 218578957597000⟩, ⟨.privateRow 15 8, 512292619238400⟩, ⟨.privateRow 15 10, 314753698939680⟩, ⟨.privateRow 15 11, 503679003527700⟩, ⟨.privateRow 16 0, 37661263497000⟩, ⟨.privateRow 16 1, 12649365729000⟩, ⟨.privateRow 16 2, 19576399342500⟩, ⟨.privateRow 16 3, 90644661198000⟩, ⟨.privateRow 16 4, 71258093606700⟩, ⟨.privateRow 16 6, 676364597283375⟩, ⟨.privateRow 16 7, 252069446772000⟩, ⟨.privateRow 16 10, 282552697176750⟩, ⟨.privateRow 17 0, 170799901272000⟩, ⟨.privateRow 17 2, 201854428776000⟩, ⟨.privateRow 17 3, 146866498178400⟩, ⟨.privateRow 17 4, 59550923432000⟩, ⟨.privateRow 17 6, 2509756543008000⟩, ⟨.privateRow 17 10, 519717149952000⟩, ⟨.privateRow 18 0, 991986908312400⟩, ⟨.privateRow 18 2, 494612955476640⟩, ⟨.privateRow 18 4, 647848308907800⟩, ⟨.privateRow 18 5, 23665691649600⟩, ⟨.privateRow 18 7, 1301613040728000⟩, ⟨.privateRow 18 11, 46668743933011200⟩, ⟨.privateRow 19 0, 6321966810213600⟩, ⟨.privateRow 19 3, 1291259300631300⟩, ⟨.privateRow 19 4, 1506152232842400⟩, ⟨.privateRow 19 6, 1320545594047680⟩, ⟨.privateRow 20 0, 6002802686921040⟩, ⟨.privateRow 20 7, 191774932282533600⟩, ⟨.privateRow 21 3, 14613564593628000⟩, ⟨.privateRow 21 5, 330491383886664000⟩, ⟨.privateRow 21 8, 3068848564661880000⟩, ⟨.hall 21 4, 368261827759425600⟩, ⟨.hall 18 6, 63390245490000⟩, ⟨.hall 12 7, 114498675900⟩, ⟨.hall 13 9, 126806566770⟩, ⟨.hall 14 9, 295942832640⟩, ⟨.hall 11 11, 37912809000⟩, ⟨.hall 8 13, 35832076280⟩, ⟨.hall 15 13, 4631776084435500⟩, ⟨.hall 13 15, 1339808771000700⟩, ⟨.hall 12 16, 1484475704712000⟩, ⟨.hall 9 17, 1503833811480⟩, ⟨.hall 11 17, 2145060254337000⟩, ⟨.hall 10 18, 3735335507904000⟩, ⟨.hall 8 20, 24268006703740800⟩, ⟨.hall 7 21, 58968148744323000⟩, ⟨.hall 6 22, 87883847251200000⟩, ⟨.hall 5 23, 187225203062898000⟩, ⟨.hall 4 24, 262967485844359296⟩, ⟨.hall 3 25, 284523508514044800⟩]
  caps := #[0, 0, 0, 0, 180246623356800, 0, 0, 12460803755400, 0, 2640005682600, 905287939920, 3301648865550, 615597602400, 18901493039520, 33798653070, 0, 0, 15339865741200, 645087311548680, 0, 7711465624022160, 8992962826848000, 0] }

theorem case_51_29_14_checked :
    (Witness.linear .positive case_51_29_14).check 51 29 14 = true := by
  change case_51_29_14.check 51 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_29_15 : Certificate := {
  objectiveScale := 791154000000
  eta := 2222645350974048000
  rows := #[⟨.count 2, 493921189105344000⟩, ⟨.count 3, 116735575156200000⟩, ⟨.count 4, 26869662211392000⟩, ⟨.count 5, 6944970280248000⟩, ⟨.count 6, 1805445978336000⟩, ⟨.count 7, 475053957378000⟩, ⟨.count 8, 135676159819200⟩, ⟨.count 9, 42405492729600⟩, ⟨.count 10, 14085740592000⟩, ⟨.count 11, 5436601632000⟩, ⟨.count 12, 2594741688000⟩, ⟨.count 13, 2409402996000⟩, ⟨.path 14, 208039104000⟩, ⟨.privateRow 4 23, 1586511559432800⟩, ⟨.privateRow 5 21, 813280595727600⟩, ⟨.privateRow 5 22, 1806481129252800⟩, ⟨.privateRow 6 18, 59521177716000⟩, ⟨.privateRow 6 19, 289342528675200⟩, ⟨.privateRow 6 20, 703813386276000⟩, ⟨.privateRow 6 21, 1090299474264000⟩, ⟨.privateRow 7 16, 40902484194000⟩, ⟨.privateRow 7 17, 116588333862000⟩, ⟨.privateRow 7 18, 258930508636800⟩, ⟨.privateRow 7 19, 412911438439500⟩, ⟨.privateRow 7 20, 523777440186000⟩, ⟨.privateRow 8 14, 20578644060975⟩, ⟨.privateRow 8 15, 49272291268200⟩, ⟨.privateRow 8 16, 101632187857200⟩, ⟨.privateRow 8 17, 157564247480640⟩, ⟨.privateRow 8 18, 200398747799250⟩, ⟨.privateRow 8 19, 200765735570400⟩, ⟨.privateRow 9 11, 594319405680⟩, ⟨.privateRow 9 12, 8721443931200⟩, ⟨.privateRow 9 13, 21356680445100⟩, ⟨.privateRow 9 14, 42443737221600⟩, ⟨.privateRow 9 15, 64295365134000⟩, ⟨.privateRow 9 16, 80955940665600⟩, ⟨.privateRow 9 17, 81665375992200⟩, ⟨.privateRow 9 18, 18382852488000⟩, ⟨.privateRow 10 9, 630151552800⟩, ⟨.privateRow 10 10, 3766082221440⟩, ⟨.privateRow 10 11, 9147494109600⟩, ⟨.privateRow 10 12, 18830411107200⟩, ⟨.privateRow 10 13, 28531567785600⟩, ⟨.privateRow 10 14, 36097799245200⟩, ⟨.privateRow 10 15, 1386333416160⟩, ⟨.privateRow 11 7, 422160354000⟩, ⟨.privateRow 11 8, 1822497138000⟩, ⟨.privateRow 11 9, 4111429984200⟩, ⟨.privateRow 11 10, 8621681376000⟩, ⟨.privateRow 11 11, 13884957009000⟩, ⟨.privateRow 12 5, 247118256000⟩, ⟨.privateRow 12 6, 962731539000⟩, ⟨.privateRow 12 7, 2072423556000⟩, ⟨.privateRow 12 8, 4238078090400⟩, ⟨.privateRow 12 9, 65211762000⟩, ⟨.privateRow 13 3, 145623258000⟩, ⟨.privateRow 13 4, 556016076000⟩, ⟨.privateRow 13 5, 1010095871400⟩, ⟨.privateRow 14 0, 93699005400⟩, ⟨.privateRow 14 1, 3569485920⟩, ⟨.privateRow 14 2, 225642502800⟩, ⟨.privateRow 15 0, 68712603960⟩, ⟨.privateRow 16 0, 57366738000⟩, ⟨.privateRow 17 0, 123559128000⟩, ⟨.privateRow 18 0, 455109454800⟩, ⟨.privateRow 19 0, 2234173687200⟩, ⟨.privateRow 20 0, 15564743354160⟩, ⟨.privateRow 21 0, 115294395216000⟩, ⟨.privateRow 22 0, 2723830086978000⟩, ⟨.hall 7 21, 370664747271000⟩, ⟨.hall 6 22, 1511289299520000⟩, ⟨.hall 5 23, 3929490884319000⟩, ⟨.hall 4 24, 8188038040710528⟩, ⟨.hall 3 25, 13750852109425200⟩, ⟨.hall 2 26, 12067480032608000⟩, ⟨.assumptionRow 15, 1289251372500⟩]
  caps := #[0, 2868722821692000, 397989567612000, 0, 520079742000, 8775418884960, 406224819000, 104633582625, 203789373060, 272485539040, 360508698000, 0, 273735533400, 0, 0, 119331515940, 0, 1976946048000, 7736860731600, 40215126369600, 0, 2305887904320000, 0] }

theorem case_51_29_15_checked :
    (Witness.linear .conditional case_51_29_15).check 51 29 15 = true := by
  change case_51_29_15.check 51 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_29_16 : Certificate := {
  objectiveScale := 10774764000000
  eta := 22095709665565536000
  rows := #[⟨.count 2, 5314841030667168000⟩, ⟨.count 3, 1272729064069663200⟩, ⟨.count 4, 335248187908233600⟩, ⟨.count 5, 89456314435488000⟩, ⟨.count 6, 24347820408912000⟩, ⟨.count 7, 6796925851716000⟩, ⟨.count 8, 1978173402004800⟩, ⟨.count 9, 601386987801600⟩, ⟨.count 10, 197571045672000⟩, ⟨.count 11, 70675821216000⟩, ⟨.count 12, 28912835952000⟩, ⟨.count 13, 12528895579200⟩, ⟨.count 14, 19489393123200⟩, ⟨.path 12, 2843132292000⟩, ⟨.privateRow 2 27, 229320552084624000⟩, ⟨.privateRow 4 23, 44586163067846400⟩, ⟨.privateRow 5 20, 1798592565369600⟩, ⟨.privateRow 5 21, 15021797774583600⟩, ⟨.privateRow 5 22, 37675781106163200⟩, ⟨.privateRow 6 18, 1165883338620000⟩, ⟨.privateRow 6 19, 5365151506915200⟩, ⟨.privateRow 6 20, 13332833045532000⟩, ⟨.privateRow 6 21, 22765467300576000⟩, ⟨.privateRow 7 16, 545528995011000⟩, ⟨.privateRow 7 17, 1993312484163000⟩, ⟨.privateRow 7 18, 4865387783256000⟩, ⟨.privateRow 7 19, 8380004011879500⟩, ⟨.privateRow 7 20, 11816314643133000⟩, ⟨.privateRow 8 14, 225802890638325⟩, ⟨.privateRow 8 15, 760956393997800⟩, ⟨.privateRow 8 16, 1844183824282800⟩, ⟨.privateRow 8 17, 3207710490664680⟩, ⟨.privateRow 8 18, 4540115032402950⟩, ⟨.privateRow 8 19, 5167125351788400⟩, ⟨.privateRow 9 12, 87934285639200⟩, ⟨.privateRow 9 13, 297039232690200⟩, ⟨.privateRow 9 14, 728863528536000⟩, ⟨.privateRow 9 15, 1291404310996800⟩, ⟨.privateRow 9 16, 1854972595476000⟩, ⟨.privateRow 9 17, 2179853818342200⟩, ⟨.privateRow 9 18, 1865413341792000⟩, ⟨.privateRow 10 10, 33105197165040⟩, ⟨.privateRow 10 11, 118382000536800⟩, ⟨.privateRow 10 12, 301054904350200⟩, ⟨.privateRow 10 13, 551959806340800⟩, ⟨.privateRow 10 14, 816626988777600⟩, ⟨.privateRow 10 15, 994601556748800⟩, ⟨.privateRow 10 16, 206606306907000⟩, ⟨.privateRow 11 8, 12156533298000⟩, ⟨.privateRow 11 9, 48268373353200⟩, ⟨.privateRow 11 10, 130152380358000⟩, ⟨.privateRow 11 11, 251883004873500⟩, ⟨.privateRow 11 12, 391700087064000⟩, ⟨.privateRow 11 13, 157481256933000⟩, ⟨.privateRow 12 6, 4249919173500⟩, ⟨.privateRow 12 7, 20224382724000⟩, ⟨.privateRow 12 8, 59030373402000⟩, ⟨.privateRow 12 9, 123013408518000⟩, ⟨.privateRow 12 10, 97329841859250⟩, ⟨.privateRow 13 4, 1297370844000⟩, ⟨.privateRow 13 5, 8794320935400⟩, ⟨.privateRow 13 6, 28211918716800⟩, ⟨.privateRow 13 7, 45296776324800⟩, ⟨.privateRow 14 3, 4069213948800⟩, ⟨.privateRow 14 4, 14385028257600⟩, ⟨.privateRow 14 5, 1392099508800⟩, ⟨.privateRow 15 0, 812058046800⟩, ⟨.privateRow 15 1, 609043535100⟩, ⟨.privateRow 15 2, 2623572151200⟩, ⟨.privateRow 16 0, 932209492500⟩, ⟨.privateRow 17 0, 1070845776000⟩, ⟨.privateRow 18 0, 1972140970800⟩, ⟨.privateRow 19 0, 9681419311200⟩, ⟨.privateRow 20 0, 67447221201360⟩, ⟨.privateRow 21 0, 749413568904000⟩, ⟨.privateRow 22 7, 141639164522856000⟩, ⟨.hall 7 19, 4472910637650⟩, ⟨.hall 7 20, 576455751144000⟩, ⟨.hall 8 20, 1418085366297600⟩, ⟨.hall 6 22, 38870444588976000⟩, ⟨.hall 5 23, 89781717695670000⟩, ⟨.hall 4 24, 176714559430561152⟩, ⟨.hall 3 25, 301333431336537600⟩, ⟨.hall 2 26, 384199356324784000⟩, ⟨.assumptionRow 16, 11885039761140⟩]
  caps := #[0, 0, 756637721658000, 921919412854440, 0, 0, 0, 27123243147000, 0, 1335165741000, 149050137600, 0, 4591982918250, 0, 6873205630200, 924501248580, 6106314834360, 0, 33526396503600, 174265547601600, 1281497202825840, 14988271378080000, 0] }

theorem case_51_29_16_checked :
    (Witness.linear .conditional case_51_29_16).check 51 29 16 = true := by
  change case_51_29_16.check 51 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_29_17 : Certificate := {
  objectiveScale := 1147608000000
  eta := 1459972926620208000
  rows := #[⟨.count 2, 373553840499840000⟩, ⟨.count 3, 96968351096416800⟩, ⟨.count 4, 26541983403936000⟩, ⟨.count 5, 7390977545952000⟩, ⟨.count 6, 2094574337856000⟩, ⟨.count 7, 605764069911000⟩, ⟨.count 8, 178402906281600⟩, ⟨.count 9, 59271313701600⟩, ⟨.count 10, 20387256120000⟩, ⟨.count 11, 7475327244000⟩, ⟨.count 12, 2594741688000⟩, ⟨.count 13, 1445641797600⟩, ⟨.count 14, 749592043200⟩, ⟨.count 15, 1405485081000⟩, ⟨.path 11, 19679166000⟩, ⟨.path 12, 198347058000⟩, ⟨.privateRow 2 27, 36317734493040000⟩, ⟨.privateRow 4 23, 4314437631504000⟩, ⟨.privateRow 5 20, 49151821118400⟩, ⟨.privateRow 5 21, 1375795881860400⟩, ⟨.privateRow 5 22, 3846585111969600⟩, ⟨.privateRow 6 18, 26592670104000⟩, ⟨.privateRow 6 19, 448041872678400⟩, ⟨.privateRow 6 20, 1317408015924000⟩, ⟨.privateRow 6 21, 2533799580312000⟩, ⟨.privateRow 7 16, 9293411556000⟩, ⟨.privateRow 7 17, 147475541713500⟩, ⟨.privateRow 7 18, 458429076705600⟩, ⟨.privateRow 7 19, 918283716850500⟩, ⟨.privateRow 7 20, 1472546797722000⟩, ⟨.privateRow 8 14, 2190214251225⟩, ⟨.privateRow 8 15, 48482542508400⟩, ⟨.privateRow 8 16, 162239827850100⟩, ⟨.privateRow 8 17, 342226247322960⟩, ⟨.privateRow 8 18, 564044587756650⟩, ⟨.privateRow 8 19, 764864981080200⟩, ⟨.privateRow 9 13, 15667812260100⟩, ⟨.privateRow 9 14, 58284605808000⟩, ⟨.privateRow 9 15, 131535556152000⟩, ⟨.privateRow 9 16, 226141210975680⟩, ⟨.privateRow 9 17, 316301071086000⟩, ⟨.privateRow 9 18, 348310436073600⟩, ⟨.privateRow 10 11, 4382230406400⟩, ⟨.privateRow 10 12, 21123977420700⟩, ⟨.privateRow 10 13, 52180784884800⟩, ⟨.privateRow 10 14, 95307333382800⟩, ⟨.privateRow 10 15, 139863990530880⟩, ⟨.privateRow 10 16, 164515889953800⟩, ⟨.privateRow 10 17, 98303642236800⟩, ⟨.privateRow 11 9, 1223235367200⟩, ⟨.privateRow 11 10, 7286556354000⟩, ⟨.privateRow 11 11, 21298504689000⟩, ⟨.privateRow 11 12, 42288111558000⟩, ⟨.privateRow 11 13, 66449069379000⟩, ⟨.privateRow 11 14, 65331888930000⟩, ⟨.privateRow 12 7, 272391714000⟩, ⟨.privateRow 12 8, 2573118840600⟩, ⟨.privateRow 12 9, 8590791594000⟩, ⟨.privateRow 12 10, 19661346243000⟩, ⟨.privateRow 12 11, 33916980636000⟩, ⟨.privateRow 12 12, 5869058580000⟩, ⟨.privateRow 13 6, 872776749600⟩, ⟨.privateRow 13 7, 3606690946320⟩, ⟨.privateRow 13 8, 9275171875200⟩, ⟨.privateRow 13 9, 9498607965000⟩, ⟨.privateRow 14 4, 178474296000⟩, ⟨.privateRow 14 5, 1528388971200⟩, ⟨.privateRow 14 6, 4615345294560⟩, ⟨.privateRow 14 7, 458084026400⟩, ⟨.privateRow 15 2, 28830463200⟩, ⟨.privateRow 15 3, 523152780150⟩, ⟨.privateRow 15 4, 1201050887400⟩, ⟨.privateRow 16 1, 216228474000⟩, ⟨.privateRow 16 2, 150587687250⟩, ⟨.privateRow 17 0, 41186376000⟩, ⟨.hall 8 20, 680129847196800⟩, ⟨.hall 7 21, 2354634710473500⟩, ⟨.hall 6 22, 5646802569408000⟩, ⟨.hall 5 23, 11450553882768000⟩, ⟨.hall 4 24, 20633279147889408⟩, ⟨.hall 3 25, 33278618579144400⟩, ⟨.hall 2 26, 43542849926576000⟩, ⟨.assumptionRow 17, 918656378640⟩]
  caps := #[0, 3678261797199600, 757653982113600, 0, 0, 0, 1413516424320, 1695212049960, 7176074400, 0, 50060109780, 0, 184336464480, 535854342240, 170756419680, 60755285220, 918656378640, 3261824541360, 1147608000000, 0, 0, 0, 0] }

theorem case_51_29_17_checked :
    (Witness.linear .conditional case_51_29_17).check 51 29 17 = true := by
  change case_51_29_17.check 51 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_29_18 : Certificate := {
  objectiveScale := 1544400000000
  eta := 2298912593409432000
  rows := #[⟨.count 2, 573820204990032000⟩, ⟨.count 3, 144285170893063200⟩, ⟨.count 4, 38109045307132800⟩, ⟨.count 5, 10130736463848000⟩, ⟨.count 6, 2704956430176000⟩, ⟨.count 7, 725230301796000⟩, ⟨.count 8, 192645155102400⟩, ⟨.count 9, 55898149507200⟩, ⟨.count 10, 15939127512000⟩, ⟨.count 11, 4417238826000⟩, ⟨.count 12, 1853386920000⟩, ⟨.count 13, 963761198400⟩, ⟨.count 14, 749592043200⟩, ⟨.path 11, 184416102000⟩, ⟨.path 12, 290104269000⟩, ⟨.privateRow 2 27, 57070725631920000⟩, ⟨.privateRow 4 23, 6414312655951200⟩, ⟨.privateRow 5 20, 69176637129600⟩, ⟨.privateRow 5 21, 1978360800015600⟩, ⟨.privateRow 5 22, 5792633140694400⟩, ⟨.privateRow 6 18, 35962570644000⟩, ⟨.privateRow 6 19, 617556759019200⟩, ⟨.privateRow 6 20, 1922837446530000⟩, ⟨.privateRow 6 21, 3928754677848000⟩, ⟨.privateRow 7 16, 11960964873000⟩, ⟨.privateRow 7 17, 192584920027500⟩, ⟨.privateRow 7 18, 642868876049400⟩, ⟨.privateRow 7 19, 1386009073449000⟩, ⟨.privateRow 7 20, 2396619774549000⟩, ⟨.privateRow 8 14, 2635284526875⟩, ⟨.privateRow 8 15, 58976831113200⟩, ⟨.privateRow 8 16, 216054289951500⟩, ⟨.privateRow 8 17, 498328790319360⟩, ⟨.privateRow 8 18, 898222090515750⟩, ⟨.privateRow 8 19, 1340926466279400⟩, ⟨.privateRow 9 13, 17254002565800⟩, ⟨.privateRow 9 14, 72473312340000⟩, ⟨.privateRow 9 15, 182623823382000⟩, ⟨.privateRow 9 16, 348785177700960⟩, ⟨.privateRow 9 17, 543976268635800⟩, ⟨.privateRow 9 18, 682128759312000⟩, ⟨.privateRow 10 11, 4093925774400⟩, ⟨.privateRow 10 12, 23885523931500⟩, ⟨.privateRow 10 13, 67950459878400⟩, ⟨.privateRow 10 14, 140523796274400⟩, ⟨.privateRow 10 15, 232622299103040⟩, ⟨.privateRow 10 16, 313305791891400⟩, ⟨.privateRow 10 17, 312443966973600⟩, ⟨.privateRow 11 9, 849469005000⟩, ⟨.privateRow 11 10, 7128675246000⟩, ⟨.privateRow 11 11, 25387539581250⟩, ⟨.privateRow 11 12, 58593503628000⟩, ⟨.privateRow 11 13, 105128224740000⟩, ⟨.privateRow 11 14, 153411013324800⟩, ⟨.privateRow 11 15, 124748384607000⟩, ⟨.privateRow 12 7, 56163240000⟩, ⟨.privateRow 12 8, 1976946048000⟩, ⟨.privateRow 12 9, 9002655354000⟩, ⟨.privateRow 12 10, 25009139751750⟩, ⟨.privateRow 12 11, 50081162274000⟩, ⟨.privateRow 12 12, 80498771892000⟩, ⟨.privateRow 12 13, 12201463890000⟩, ⟨.privateRow 13 6, 293172112800⟩, ⟨.privateRow 13 7, 3069208739520⟩, ⟨.privateRow 13 8, 10461339504000⟩, ⟨.privateRow 13 9, 24807583924200⟩, ⟨.privateRow 13 10, 27154766073600⟩, ⟨.privateRow 14 5, 715519677600⟩, ⟨.privateRow 14 6, 4299445790640⟩, ⟨.privateRow 14 7, 12332573853600⟩, ⟨.privateRow 14 8, 5186909227500⟩, ⟨.privateRow 15 3, 46849502700⟩, ⟨.privateRow 15 4, 1371412715400⟩, ⟨.privateRow 15 5, 5556351020220⟩, ⟨.privateRow 16 2, 217515548250⟩, ⟨.privateRow 16 3, 1715786982000⟩, ⟨.privateRow 17 1, 446185740000⟩, ⟨.hall 8 19, 16503518151120⟩, ⟨.hall 9 19, 275105634083280⟩, ⟨.hall 8 20, 1420369837286400⟩, ⟨.hall 7 21, 4711824848367000⟩, ⟨.hall 6 22, 10143377099856000⟩, ⟨.hall 5 23, 19277298731691000⟩, ⟨.hall 4 24, 33307895420287488⟩, ⟨.hall 3 25, 52333456308487200⟩, ⟨.hall 2 26, 67639378526720000⟩, ⟨.assumptionRow 18, 598110337440⟩]
  caps := #[0, 3681322972236000, 0, 100020780702480, 14664262080600, 468818634240, 3904125225000, 1564515655560, 854767104555, 379339003680, 0, 0, 0, 312547965120, 384404786220, 612235480230, 598110337440, 598110337440, 14845889662560, 1544400000000, 0, 0, 0] }

theorem case_51_29_18_checked :
    (Witness.linear .conditional case_51_29_18).check 51 29 18 = true := by
  change case_51_29_18.check 51 29 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_30_1_checked :
    (Witness.rising).check 51 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_30_2_checked :
    (Witness.rising).check 51 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_30_3_checked :
    (Witness.rising).check 51 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_30_4_checked :
    (Witness.rising).check 51 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_30_5_checked :
    (Witness.rising).check 51 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_30_6_checked :
    (Witness.rising).check 51 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_30_7_checked :
    (Witness.rising).check 51 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_30_8_checked :
    (Witness.rising).check 51 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_30_9_checked :
    (Witness.rising).check 51 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_30_10_checked :
    (Witness.linear .positive case_51_30_10).check 51 30 10 = true := by
  change case_51_30_10.check 51 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_30_11_checked :
    (Witness.linear .positive case_51_30_11).check 51 30 11 = true := by
  change case_51_30_11.check 51 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_30_12_checked :
    (Witness.linear .positive case_51_30_12).check 51 30 12 = true := by
  change case_51_30_12.check 51 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_30_13 : Certificate := {
  objectiveScale := 5096931840000
  eta := 17628005733187449600
  rows := #[⟨.count 2, 3445473847850274240⟩, ⟨.count 3, 666321747809477760⟩, ⟨.count 4, 138283369446942720⟩, ⟨.count 5, 28390477382467200⟩, ⟨.count 6, 5834289041380800⟩, ⟨.count 7, 1313097861675600⟩, ⟨.count 8, 300136654097280⟩, ⟨.count 9, 72089337640320⟩, ⟨.count 10, 21202746364800⟩, ⟨.count 11, 7067582121600⟩, ⟨.count 12, 4240549272960⟩, ⟨.path 13, 2038772736000⟩, ⟨.privateRow 6 19, 1156776687666600⟩, ⟨.privateRow 6 20, 1312715034310680⟩, ⟨.privateRow 6 21, 2469236503734000⟩, ⟨.privateRow 6 22, 3889526027587200⟩, ⟨.privateRow 7 16, 148441310747730⟩, ⟨.privateRow 7 17, 349247936054160⟩, ⟨.privateRow 7 18, 761316019704240⟩, ⟨.privateRow 7 19, 1144653821110800⟩, ⟨.privateRow 7 20, 1712195389604700⟩, ⟨.privateRow 7 21, 2457241246299840⟩, ⟨.privateRow 7 23, 19962150116388480⟩, ⟨.privateRow 8 13, 20825808651648⟩, ⟨.privateRow 8 14, 73247635821360⟩, ⟨.privateRow 8 15, 153465919912305⟩, ⟨.privateRow 8 16, 257259989226240⟩, ⟨.privateRow 8 17, 519943366122180⟩, ⟨.privateRow 9 11, 20067649842240⟩, ⟨.privateRow 9 12, 32487319152288⟩, ⟨.privateRow 9 13, 65466751430080⟩, ⟨.privateRow 9 14, 106278766153560⟩, ⟨.privateRow 9 15, 184901410362240⟩, ⟨.privateRow 9 16, 296956242142560⟩, ⟨.privateRow 9 17, 104317512114816⟩, ⟨.privateRow 10 8, 2378513214000⟩, ⟨.privateRow 10 9, 8760857004900⟩, ⟨.privateRow 10 10, 19130659788240⟩, ⟨.privateRow 10 11, 28941748787952⟩, ⟨.privateRow 10 12, 47627650630560⟩, ⟨.privateRow 10 13, 82911572764020⟩, ⟨.privateRow 10 14, 123354549386640⟩, ⟨.privateRow 10 15, 184287203820720⟩, ⟨.privateRow 10 19, 806146085745000⟩, ⟨.privateRow 11 5, 460463683680⟩, ⟨.privateRow 11 6, 1789842225600⟩, ⟨.privateRow 11 7, 4670535038400⟩, ⟨.privateRow 11 8, 9731310989400⟩, ⟨.privateRow 11 9, 16559169681600⟩, ⟨.privateRow 11 10, 23082080701680⟩, ⟨.privateRow 11 11, 41281104664800⟩, ⟨.privateRow 11 12, 62905496553900⟩, ⟨.privateRow 11 13, 88895497204800⟩, ⟨.privateRow 11 14, 126092090124000⟩, ⟨.privateRow 11 17, 141779980742400⟩, ⟨.privateRow 12 3, 739887503355⟩, ⟨.privateRow 12 4, 1154371746528⟩, ⟨.privateRow 12 5, 2789170801560⟩, ⟨.privateRow 12 6, 5531742160560⟩, ⟨.privateRow 12 7, 9747373676040⟩, ⟨.privateRow 12 8, 15211364248080⟩, ⟨.privateRow 12 9, 23393696822496⟩, ⟨.privateRow 12 10, 37458185244480⟩, ⟨.privateRow 12 11, 5234428008810⟩, ⟨.privateRow 12 12, 174165416568000⟩, ⟨.privateRow 12 13, 53095210688520⟩, ⟨.privateRow 12 16, 194594094414720⟩, ⟨.privateRow 13 1, 942344282880⟩, ⟨.privateRow 13 3, 3612319751040⟩, ⟨.privateRow 13 4, 2726067389760⟩, ⟨.privateRow 13 5, 6614531985600⟩, ⟨.privateRow 13 7, 40263801177600⟩, ⟨.privateRow 13 8, 2190950457696⟩, ⟨.privateRow 13 9, 65990276031680⟩, ⟨.privateRow 13 11, 137212058617920⟩, ⟨.privateRow 13 12, 112806463529760⟩, ⟨.privateRow 13 17, 687911326502400⟩, ⟨.privateRow 14 0, 2387041216560⟩, ⟨.privateRow 14 2, 5512714054848⟩, ⟨.privateRow 14 3, 3855618460980⟩, ⟨.privateRow 14 4, 1855240306920⟩, ⟨.privateRow 14 5, 14483635306140⟩, ⟨.privateRow 14 6, 48131840516760⟩, ⟨.privateRow 14 7, 7771395507876⟩, ⟨.privateRow 14 8, 74778945281040⟩, ⟨.privateRow 14 9, 24740218457955⟩, ⟨.privateRow 14 11, 108084926029080⟩, ⟨.privateRow 14 14, 574368656501640⟩, ⟨.privateRow 15 0, 11771941471290⟩, ⟨.privateRow 15 2, 13453647395760⟩, ⟨.privateRow 15 5, 127377105055200⟩, ⟨.privateRow 15 7, 99450042131440⟩, ⟨.privateRow 15 11, 49767557439600⟩, ⟨.privateRow 15 13, 1306462187350320⟩, ⟨.privateRow 16 0, 58955414197680⟩, ⟨.privateRow 16 4, 233524692601200⟩, ⟨.privateRow 16 5, 63740756259180⟩, ⟨.privateRow 16 6, 149302672318800⟩, ⟨.privateRow 16 8, 124418893599000⟩, ⟨.privateRow 16 11, 74651336159400⟩, ⟨.privateRow 16 12, 653358702796800⟩, ⟨.privateRow 16 14, 4789170335149200⟩, ⟨.privateRow 17 0, 235821656790720⟩, ⟨.privateRow 17 3, 454938119475840⟩, ⟨.privateRow 17 4, 314224701126336⟩, ⟨.privateRow 17 5, 332124007255040⟩, ⟨.privateRow 17 6, 179163206782560⟩, ⟨.privateRow 17 7, 174131761415040⟩, ⟨.privateRow 17 10, 577303666299360⟩, ⟨.privateRow 17 13, 2002952773261440⟩, ⟨.privateRow 18 0, 1355680043958240⟩, ⟨.privateRow 18 3, 3030155158814784⟩, ⟨.privateRow 18 12, 30301551588147840⟩, ⟨.privateRow 19 0, 10608146281933200⟩, ⟨.privateRow 19 5, 20104343137644480⟩, ⟨.privateRow 20 0, 111422809424646720⟩, ⟨.privateRow 20 10, 1056493272898103040⟩, ⟨.privateRow 21 2, 2893485789538344000⟩, ⟨.hall 16 9, 1437992899200⟩, ⟨.hall 20 9, 29676777328598400⟩, ⟨.hall 8 11, 2103249720⟩, ⟨.hall 18 11, 1171451736655200⟩, ⟨.hall 10 19, 1112172391610280⟩, ⟨.hall 9 20, 1466321359314240⟩, ⟨.hall 8 21, 3607765087006080⟩, ⟨.hall 7 22, 9470383353390960⟩, ⟨.hall 5 24, 29528546572901376⟩, ⟨.hall 4 25, 82618385899008960⟩, ⟨.hall 3 26, 104302591663670400⟩, ⟨.hall 2 27, 79597356334919280⟩]
  caps := #[0, 5997164683910400, 250856331485760, 104129043258240, 22459205408640, 0, 13985959731744, 0, 2174825231150, 1751781011552, 0, 4135317640110, 917868354975, 1127145509952, 0, 18648333003300, 1009272143880, 0, 0, 2320590106897920, 5125988811303360, 0] }

theorem case_51_30_13_checked :
    (Witness.linear .positive case_51_30_13).check 51 30 13 = true := by
  change case_51_30_13.check 51 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_30_14 : Certificate := {
  objectiveScale := 8848840000000
  eta := 38817224745806707200
  rows := #[⟨.count 2, 8546911870636339200⟩, ⟨.count 3, 1955387238824859840⟩, ⟨.count 4, 455148048081767040⟩, ⟨.count 5, 102168967149849600⟩, ⟨.count 6, 25324030189458000⟩, ⟨.count 7, 6174239741429760⟩, ⟨.count 8, 1534372078599360⟩, ⟨.count 9, 419814378023040⟩, ⟨.count 10, 116615105006400⟩, ⟨.count 11, 37104806138400⟩, ⟨.count 12, 12721647818880⟩, ⟨.count 13, 9187856758080⟩, ⟨.path 13, 3318357474432⟩, ⟨.privateRow 2 28, 396184977336788640⟩, ⟨.privateRow 3 27, 887491835689979520⟩, ⟨.privateRow 6 19, 3483729020772000⟩, ⟨.privateRow 6 20, 7234288714893240⟩, ⟨.privateRow 6 22, 49840294638934800⟩, ⟨.privateRow 6 23, 24184161710408700⟩, ⟨.privateRow 6 24, 200013899212927800⟩, ⟨.privateRow 7 16, 252953181370890⟩, ⟨.privateRow 7 17, 1413289252037520⟩, ⟨.privateRow 7 18, 3210390282219120⟩, ⟨.privateRow 7 19, 6413124017139840⟩, ⟨.privateRow 7 20, 6573911510406240⟩, ⟨.privateRow 8 14, 194348692257720⟩, ⟨.privateRow 8 15, 568642197168045⟩, ⟨.privateRow 8 16, 1216570676092200⟩, ⟨.privateRow 8 17, 2554989833476080⟩, ⟨.privateRow 8 18, 4133157362622288⟩, ⟨.privateRow 8 19, 5092369608165840⟩, ⟨.privateRow 8 22, 33598843682203800⟩, ⟨.privateRow 9 11, 5589814950720⟩, ⟨.privateRow 9 12, 100076962841856⟩, ⟨.privateRow 9 13, 249485648892480⟩, ⟨.privateRow 9 14, 481479032034000⟩, ⟨.privateRow 9 15, 995721355474560⟩, ⟨.privateRow 9 16, 1682555717082240⟩, ⟨.privateRow 9 17, 2500934609549376⟩, ⟨.privateRow 10 9, 9143684369820⟩, ⟨.privateRow 10 10, 44477579306160⟩, ⟨.privateRow 10 11, 113699727381240⟩, ⟨.privateRow 10 12, 211438498471200⟩, ⟨.privateRow 10 13, 416302673156370⟩, ⟨.privateRow 10 14, 712639450139760⟩, ⟨.privateRow 10 15, 1100422536333120⟩, ⟨.privateRow 10 16, 1551510965244240⟩, ⟨.privateRow 10 18, 1961607417850080⟩, ⟨.privateRow 10 20, 12940036106437440⟩, ⟨.privateRow 11 7, 7413547680000⟩, ⟨.privateRow 11 8, 22206664279800⟩, ⟨.privateRow 11 9, 52305948676800⟩, ⟨.privateRow 11 10, 101676806431200⟩, ⟨.privateRow 11 11, 198106468560000⟩, ⟨.privateRow 11 12, 334545605994600⟩, ⟨.privateRow 11 13, 529517938435200⟩, ⟨.privateRow 11 14, 771089272153200⟩, ⟨.privateRow 11 15, 1038259939036320⟩, ⟨.privateRow 12 5, 5452134779520⟩, ⟨.privateRow 12 6, 12395451720960⟩, ⟨.privateRow 12 7, 27121846391640⟩, ⟨.privateRow 12 8, 52043104713600⟩, ⟨.privateRow 12 9, 107550930935448⟩, ⟨.privateRow 12 10, 184993962032880⟩, ⟨.privateRow 12 11, 294320622976380⟩, ⟨.privateRow 12 12, 442152985800240⟩, ⟨.privateRow 12 13, 615851437120920⟩, ⟨.privateRow 12 14, 791604535529808⟩, ⟨.privateRow 13 2, 618413435640⟩, ⟨.privateRow 13 3, 2779915634496⟩, ⟨.privateRow 13 4, 8582064004800⟩, ⟨.privateRow 13 5, 16418536928640⟩, ⟨.privateRow 13 6, 31097361335040⟩, ⟨.privateRow 13 7, 64572000292800⟩, ⟨.privateRow 13 8, 120502275173280⟩, ⟨.privateRow 13 9, 197892299404800⟩, ⟨.privateRow 13 10, 303640996899240⟩, ⟨.privateRow 13 11, 442430640812160⟩, ⟨.privateRow 13 12, 604985029608960⟩, ⟨.privateRow 13 13, 770507802896832⟩, ⟨.privateRow 13 15, 481302342480960⟩, ⟨.privateRow 14 2, 12862999461312⟩, ⟨.privateRow 14 3, 8285477969340⟩, ⟨.privateRow 14 4, 22527918012600⟩, ⟨.privateRow 14 5, 46609231679010⟩, ⟨.privateRow 14 6, 88850751149160⟩, ⟨.privateRow 14 7, 158490529076880⟩, ⟨.privateRow 14 8, 251134751387520⟩, ⟨.privateRow 14 9, 371390397393015⟩, ⟨.privateRow 14 10, 519770182314240⟩, ⟨.privateRow 14 11, 685260983206800⟩, ⟨.privateRow 14 13, 1819769879147220⟩, ⟨.privateRow 15 0, 4881048902730⟩, ⟨.privateRow 15 1, 20060153921808⟩, ⟨.privateRow 15 2, 14109922878480⟩, ⟨.privateRow 15 3, 41875424070480⟩, ⟨.privateRow 15 4, 80010919268280⟩, ⟨.privateRow 15 5, 146170448424000⟩, ⟨.privateRow 15 6, 251747275171392⟩, ⟨.privateRow 15 8, 1353773269198350⟩, ⟨.privateRow 15 9, 406890799286400⟩, ⟨.privateRow 16 0, 59338241562600⟩, ⟨.privateRow 16 2, 68467201803000⟩, ⟨.privateRow 16 3, 324446191769700⟩, ⟨.privateRow 16 4, 192109732214400⟩, ⟨.privateRow 16 5, 489253372367760⟩, ⟨.privateRow 16 6, 151854854751600⟩, ⟨.privateRow 16 7, 1756459803673575⟩, ⟨.privateRow 17 0, 355701311634240⟩, ⟨.privateRow 17 2, 805468775791680⟩, ⟨.privateRow 17 4, 2366791900881408⟩, ⟨.privateRow 17 5, 144963962183040⟩, ⟨.privateRow 17 6, 2992944338944560⟩, ⟨.privateRow 17 7, 2459720509234560⟩, ⟨.privateRow 18 0, 2667305492691840⟩, ⟨.privateRow 18 2, 3152270127726720⟩, ⟨.privateRow 18 4, 2889580950416160⟩, ⟨.privateRow 18 5, 22491873343779840⟩, ⟨.privateRow 18 7, 6000436117756080⟩, ⟨.privateRow 19 0, 26670051204516720⟩, ⟨.privateRow 19 2, 6278981308471872⟩, ⟨.privateRow 19 3, 8694775112063040⟩, ⟨.privateRow 19 5, 168153529284449280⟩, ⟨.privateRow 19 7, 10871072116160256⟩, ⟨.privateRow 20 0, 335482478255564640⟩, ⟨.privateRow 20 3, 38950770243785400⟩, ⟨.privateRow 20 4, 588872052991759680⟩, ⟨.privateRow 20 5, 925173533219055120⟩, ⟨.privateRow 21 9, 240381896361647040000⟩, ⟨.hall 15 6, 3238926027480⟩, ⟨.hall 16 6, 10365787111680⟩, ⟨.hall 17 7, 31448063326680⟩, ⟨.hall 13 8, 233145172260⟩, ⟨.hall 18 9, 660272797023840⟩, ⟨.hall 19 9, 13921106455960704⟩, ⟨.hall 11 11, 99613171350⟩, ⟨.hall 12 11, 242962412220⟩, ⟨.hall 10 12, 34020839160⟩, ⟨.hall 17 12, 5286551426956800⟩, ⟨.hall 13 13, 1185156312912⟩, ⟨.hall 11 18, 769157522733600⟩, ⟨.hall 10 19, 2768548606583760⟩, ⟨.hall 8 21, 16844682476381760⟩, ⟨.hall 4 25, 451819923660705600⟩, ⟨.hall 3 26, 576562512520874880⟩]
  caps := #[0, 17638457616299520, 2594177434648800, 367817438660672, 243648349584640, 139911949777600, 0, 9437606039004, 0, 7969859479296, 0, 14962548893232, 2799145525176, 9153536263608, 0, 51620120632080, 0, 124663173917568, 0, 5730072494724864, 0, 0] }

theorem case_51_30_14_checked :
    (Witness.linear .positive case_51_30_14).check 51 30 14 = true := by
  change case_51_30_14.check 51 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_30_15 : Certificate := {
  objectiveScale := 1639638000000
  eta := 9882366850423267200
  rows := #[⟨.count 2, 2187178489117702080⟩, ⟨.count 3, 533244830525447040⟩, ⟨.count 4, 128286981294151680⟩, ⟨.count 5, 30228048734083200⟩, ⟨.count 6, 7924526453844000⟩, ⟨.count 7, 2095596995572080⟩, ⟨.count 8, 563521881162240⟩, ⟨.count 9, 159020597736000⟩, ⟨.count 10, 51239970381600⟩, ⟨.count 11, 17668955304000⟩, ⟨.count 12, 6360823909440⟩, ⟨.count 13, 6125237838720⟩, ⟨.path 13, 764228296832⟩, ⟨.privateRow 2 28, 140964692310842400⟩, ⟨.privateRow 4 26, 239705057580468480⟩, ⟨.privateRow 5 21, 2479496277113856⟩, ⟨.privateRow 6 19, 1278324376028700⟩, ⟨.privateRow 6 20, 2742575242286880⟩, ⟨.privateRow 6 21, 4028300947370700⟩, ⟨.privateRow 7 16, 68908925685600⟩, ⟨.privateRow 7 17, 475690345724880⟩, ⟨.privateRow 7 18, 1079445559952760⟩, ⟨.privateRow 7 19, 2145823945849584⟩, ⟨.privateRow 7 20, 2941262644680360⟩, ⟨.privateRow 7 21, 2871715673386560⟩, ⟨.privateRow 8 14, 53851049332080⟩, ⟨.privateRow 8 15, 189212425111710⟩, ⟨.privateRow 8 16, 408750246487440⟩, ⟨.privateRow 8 17, 835648333059540⟩, ⟨.privateRow 8 18, 1294492451740488⟩, ⟨.privateRow 8 19, 1674582601001310⟩, ⟨.privateRow 8 20, 1770576562755000⟩, ⟨.privateRow 9 12, 29966548195584⟩, ⟨.privateRow 9 13, 82507477212160⟩, ⟨.privateRow 9 14, 164350732586040⟩, ⟨.privateRow 9 15, 331368636044160⟩, ⟨.privateRow 9 16, 530107923465120⟩, ⟨.privateRow 9 17, 729233123306688⟩, ⟨.privateRow 9 18, 878971629856320⟩, ⟨.privateRow 9 19, 40913447615040⟩, ⟨.privateRow 10 9, 382827364920⟩, ⟨.privateRow 10 10, 14472480662640⟩, ⟨.privateRow 10 11, 38482984652112⟩, ⟨.privateRow 10 12, 72815728025040⟩, ⟨.privateRow 10 14, 514090875252240⟩, ⟨.privateRow 10 15, 186760857563280⟩, ⟨.privateRow 10 16, 416704641889536⟩, ⟨.privateRow 10 17, 472556209605480⟩, ⟨.privateRow 11 7, 728998855200⟩, ⟨.privateRow 11 8, 6639243811200⟩, ⟨.privateRow 11 9, 18618114060000⟩, ⟨.privateRow 11 10, 35771603147280⟩, ⟨.privateRow 11 11, 68409197656800⟩, ⟨.privateRow 11 12, 8272283619600⟩, ⟨.privateRow 11 13, 332405826667200⟩, ⟨.privateRow 11 14, 194064025755600⟩, ⟨.privateRow 11 15, 227865272675040⟩, ⟨.privateRow 11 16, 291698389382400⟩, ⟨.privateRow 11 18, 2409402996000⟩, ⟨.privateRow 12 5, 656275482720⟩, ⟨.privateRow 12 6, 3452242036320⟩, ⟨.privateRow 12 7, 9305649793440⟩, ⟨.privateRow 12 8, 19098534414960⟩, ⟨.privateRow 12 9, 37829233305864⟩, ⟨.privateRow 12 10, 62685526984080⟩, ⟨.privateRow 12 11, 12854164983660⟩, ⟨.privateRow 12 12, 139584746901600⟩, ⟨.privateRow 12 14, 133824667472496⟩, ⟨.privateRow 13 3, 502583617536⟩, ⟨.privateRow 13 4, 2103447060000⟩, ⟨.privateRow 13 5, 5237259572160⟩, ⟨.privateRow 13 6, 10915487943360⟩, ⟨.privateRow 13 7, 23580023987520⟩, ⟨.privateRow 13 8, 8174836653984⟩, ⟨.privateRow 13 9, 88894477351680⟩, ⟨.privateRow 13 10, 77978989408320⟩, ⟨.privateRow 13 12, 187644305328480⟩, ⟨.privateRow 13 14, 2709239813280⟩, ⟨.privateRow 14 0, 157634797320⟩, ⟨.privateRow 14 1, 239267103075⟩, ⟨.privateRow 14 2, 1505787635352⟩, ⟨.privateRow 14 4, 14194060760880⟩, ⟨.privateRow 14 5, 127609121640⟩, ⟨.privateRow 14 6, 57110882348520⟩, ⟨.privateRow 14 8, 101236569834400⟩, ⟨.privateRow 14 9, 110302134517575⟩, ⟨.privateRow 14 11, 215531806449960⟩, ⟨.privateRow 14 12, 102827430217512⟩, ⟨.privateRow 14 14, 15185485475160⟩, ⟨.privateRow 15 0, 1818429983370⟩, ⟨.privateRow 15 2, 4156411390560⟩, ⟨.privateRow 15 3, 23911986178080⟩, ⟨.privateRow 15 5, 89581603391280⟩, ⟨.privateRow 15 6, 16078749326640⟩, ⟨.privateRow 15 7, 129906085829520⟩, ⟨.privateRow 15 9, 445720432014000⟩, ⟨.privateRow 15 11, 285895476122256⟩, ⟨.privateRow 15 12, 106426007447760⟩, ⟨.privateRow 16 0, 9698293244640⟩, ⟨.privateRow 16 2, 59779965445200⟩, ⟨.privateRow 16 4, 164093729599800⟩, ⟨.privateRow 16 5, 71588717240040⟩, ⟨.privateRow 16 8, 1353294734992200⟩, ⟨.privateRow 16 10, 231993383141520⟩, ⟨.privateRow 17 0, 57752242479360⟩, ⟨.privateRow 17 1, 126745306047360⟩, ⟨.privateRow 17 2, 23990514868320⟩, ⟨.privateRow 17 4, 346688461671552⟩, ⟨.privateRow 17 5, 579855848732160⟩, ⟨.privateRow 17 9, 3838074029741952⟩, ⟨.privateRow 17 10, 1598687075905920⟩, ⟨.privateRow 18 0, 594737035532640⟩, ⟨.privateRow 18 2, 702871041993120⟩, ⟨.privateRow 18 3, 403500042625680⟩, ⟨.privateRow 18 4, 1825150730443040⟩, ⟨.privateRow 18 5, 1015258171767840⟩, ⟨.privateRow 18 9, 21749953910564880⟩, ⟨.privateRow 19 0, 5948371596126960⟩, ⟨.privateRow 19 2, 2749006742017536⟩, ⟨.privateRow 19 6, 27620228724248160⟩, ⟨.privateRow 19 7, 27021486725513280⟩, ⟨.privateRow 20 0, 78373671035980320⟩, ⟨.hall 16 4, 6027331939200⟩, ⟨.hall 17 4, 25631764494336⟩, ⟨.hall 14 9, 24294813543⟩, ⟨.hall 12 10, 7147047600⟩, ⟨.hall 15 10, 1147334760000⟩, ⟨.hall 18 11, 78409169573454720⟩, ⟨.hall 13 12, 41672998224⟩, ⟨.hall 10 17, 7311951006360⟩, ⟨.hall 9 19, 115423712591616⟩, ⟨.hall 7 21, 375139041437160⟩, ⟨.hall 8 21, 5035223923329600⟩, ⟨.hall 6 23, 20094129850444650⟩, ⟨.hall 5 24, 54080949925626624⟩, ⟨.hall 4 25, 104657698400935680⟩, ⟨.assumptionRow 15, 3362649919200⟩]
  caps := #[0, 0, 1205650981254720, 18400461951872, 0, 1522835810496, 0, 5289398091978, 0, 0, 893194013712, 829330066632, 3401781161196, 0, 6968842814362, 624413159799, 2710738739280, 127117756406784, 6007444803360, 1066376065730976, 0, 0] }

theorem case_51_30_15_checked :
    (Witness.linear .conditional case_51_30_15).check 51 30 15 = true := by
  change case_51_30_15.check 51 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_30_16 : Certificate := {
  objectiveScale := 4099095000000
  eta := 18696369717016992000
  rows := #[⟨.count 2, 4028622522357232800⟩, ⟨.count 3, 959418972320608800⟩, ⟨.count 4, 226220346478526400⟩, ⟨.count 5, 52677045412992000⟩, ⟨.count 6, 13580800770537000⟩, ⟨.count 7, 3564122767405200⟩, ⟨.count 8, 964724959598400⟩, ⟨.count 9, 270335016151200⟩, ⟨.count 10, 83927537694000⟩, ⟨.count 11, 26503432956000⟩, ⟨.count 12, 10601373182400⟩, ⟨.count 13, 7656547298400⟩, ⟨.path 11, 1546184904264⟩, ⟨.path 12, 671998607280⟩, ⟨.privateRow 2 28, 211447038466263600⟩, ⟨.privateRow 4 23, 8004920200477200⟩, ⟨.privateRow 4 24, 37312907167536000⟩, ⟨.privateRow 5 21, 5114573595331200⟩, ⟨.privateRow 5 22, 13444897055990400⟩, ⟨.privateRow 5 23, 28941748787952000⟩, ⟨.privateRow 6 19, 2359173636319500⟩, ⟨.privateRow 6 20, 5104045842795900⟩, ⟨.privateRow 6 21, 10458365075408250⟩, ⟨.privateRow 6 22, 15900096556344000⟩, ⟨.privateRow 7 16, 99774381982275⟩, ⟨.privateRow 7 17, 863549156012400⟩, ⟨.privateRow 7 18, 1998677867686500⟩, ⟨.privateRow 7 19, 3946950132325200⟩, ⟨.privateRow 7 20, 5938609498321500⟩, ⟨.privateRow 7 21, 7477256482495800⟩, ⟨.privateRow 8 14, 72843540269500⟩, ⟨.privateRow 8 15, 334495410098850⟩, ⟨.privateRow 8 16, 762236628367500⟩, ⟨.privateRow 8 17, 1567359036543300⟩, ⟨.privateRow 8 18, 2348454470101740⟩, ⟨.privateRow 8 19, 2947052908574775⟩, ⟨.privateRow 8 20, 2933733706503600⟩, ⟨.privateRow 9 12, 37222599173760⟩, ⟨.privateRow 9 13, 138995781724800⟩, ⟨.privateRow 9 14, 306261891936000⟩, ⟨.privateRow 9 15, 636166528826400⟩, ⟨.privateRow 9 16, 999964709343600⟩, ⟨.privateRow 9 17, 1269337749039360⟩, ⟨.privateRow 9 18, 1093266609435000⟩, ⟨.privateRow 10 10, 16424097089400⟩, ⟨.privateRow 10 11, 60516171916200⟩, ⟨.privateRow 10 12, 132811647368400⟩, ⟨.privateRow 10 13, 276353504051625⟩, ⟨.privateRow 10 14, 451126290958200⟩, ⟨.privateRow 10 15, 563786915491800⟩, ⟨.privateRow 11 8, 6726250030500⟩, ⟨.privateRow 11 9, 27197048970000⟩, ⟨.privateRow 11 10, 62162597296800⟩, ⟨.privateRow 11 11, 131981741892000⟩, ⟨.privateRow 11 12, 223271344296000⟩, ⟨.privateRow 11 13, 27019733598000⟩, ⟨.privateRow 12 6, 2582385775200⟩, ⟨.privateRow 12 7, 12515510007000⟩, ⟨.privateRow 12 8, 31161612081600⟩, ⟨.privateRow 12 9, 69792373450800⟩, ⟨.privateRow 12 10, 24736537425600⟩, ⟨.privateRow 13 4, 883447765200⟩, ⟨.privateRow 13 5, 5934956781600⟩, ⟨.privateRow 13 6, 16589185813200⟩, ⟨.privateRow 13 7, 13706825932800⟩, ⟨.privateRow 14 0, 112596283800⟩, ⟨.privateRow 14 3, 2939567266350⟩, ⟨.privateRow 14 4, 5300686591200⟩, ⟨.privateRow 15 0, 239267103075⟩, ⟨.privateRow 15 1, 1020872973120⟩, ⟨.privateRow 15 2, 273448117800⟩, ⟨.privateRow 16 0, 319022804100⟩, ⟨.hall 7 22, 3042728541052200⟩, ⟨.hall 6 23, 16778605603134375⟩, ⟨.hall 5 24, 47360338968983040⟩, ⟨.hall 4 25, 105841165027197600⟩, ⟨.hall 3 26, 201923569718270400⟩, ⟨.hall 2 27, 302332169035096200⟩, ⟨.assumptionRow 16, 4770772706700⟩]
  caps := #[0, 11910176952513840, 1358341095711600, 364100949412200, 302897651456400, 0, 6958970455437, 15786896047065, 7863022982815, 1820556017280, 1207779763905, 1521587784024, 504900784080, 0, 9137924259750, 7765390763130, 0, 4099095000000, 0, 0, 0, 0] }

theorem case_51_30_16_checked :
    (Witness.linear .conditional case_51_30_16).check 51 30 16 = true := by
  change case_51_30_16.check 51 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_30_17 : Certificate := {
  objectiveScale := 18944087448000000
  eta := 70674325227959903049600
  rows := #[⟨.count 2, 15860633452321234056480⟩, ⟨.count 3, 3607245241133326752960⟩, ⟨.count 4, 813144011190725934720⟩, ⟨.count 5, 183186385499788070400⟩, ⟨.count 6, 44418458058108334200⟩, ⟨.count 7, 10933230646920221640⟩, ⟨.count 8, 2798680889580095520⟩, ⟨.count 9, 782847801281145600⟩, ⟨.count 10, 293567925480429600⟩, ⟨.count 11, 114165304353500400⟩, ⟨.count 12, 39142390064057280⟩, ⟨.count 13, 28269503935152480⟩, ⟨.path 10, 18087029969500800⟩, ⟨.privateRow 2 28, 1643588958789765187200⟩, ⟨.privateRow 3 25, 86024100474668996640⟩, ⟨.privateRow 4 23, 57729860723573258220⟩, ⟨.privateRow 4 24, 189909815852365168560⟩, ⟨.privateRow 5 21, 25781787588859061760⟩, ⟨.privateRow 5 22, 65924483176775583360⟩, ⟨.privateRow 5 23, 147981429932544848640⟩, ⟨.privateRow 6 19, 9832486837445221950⟩, ⟨.privateRow 6 20, 23622704225811791100⟩, ⟨.privateRow 6 21, 52307416500011823150⟩, ⟨.privateRow 6 22, 86540018921485529400⟩, ⟨.privateRow 7 16, 166966757616994335⟩, ⟨.privateRow 7 17, 3280272081618228840⟩, ⟨.privateRow 7 18, 8598640780275546000⟩, ⟨.privateRow 7 19, 19149761965672289952⟩, ⟨.privateRow 7 20, 32119457002321058370⟩, ⟨.privateRow 7 21, 45294812680098061080⟩, ⟨.privateRow 8 14, 87556935799152820⟩, ⟨.privateRow 8 15, 1115761983440549445⟩, ⟨.privateRow 8 16, 3087433679774867280⟩, ⟨.privateRow 8 17, 7275274627311220530⟩, ⟨.privateRow 8 18, 12517029604887139332⟩, ⟨.privateRow 8 19, 17931699714866407470⟩, ⟨.privateRow 8 20, 21023087759775060960⟩, ⟨.privateRow 9 12, 22615603148121984⟩, ⟨.privateRow 9 13, 384175309887969600⟩, ⟨.privateRow 9 14, 1138662999849555180⟩, ⟨.privateRow 9 15, 2827571701294042560⟩, ⟨.privateRow 9 16, 5161721474928738720⟩, ⟨.privateRow 9 17, 7621023345471952416⟩, ⟨.privateRow 9 18, 9284357465471808720⟩, ⟨.privateRow 9 19, 8005343627174974080⟩, ⟨.privateRow 10 11, 125581834788850440⟩, ⟨.privateRow 10 12, 432559653161595960⟩, ⟨.privateRow 10 13, 1147972908597429915⟩, ⟨.privateRow 10 14, 2236242022826320080⟩, ⟨.privateRow 10 15, 3508136709491133720⟩, ⟨.privateRow 10 16, 4516053253640608680⟩, ⟨.privateRow 10 17, 514559336050419660⟩, ⟨.privateRow 11 9, 31405567785555600⟩, ⟨.privateRow 11 10, 163538091820663560⟩, ⟨.privateRow 11 11, 488785653703947600⟩, ⟨.privateRow 11 12, 1031750404766131050⟩, ⟨.privateRow 11 13, 1743191938458828000⟩, ⟨.privateRow 11 14, 1026005072891198400⟩, ⟨.privateRow 12 7, 6659642753954190⟩, ⟨.privateRow 12 8, 54858652741292400⟩, ⟨.privateRow 12 9, 213162932557178604⟩, ⟨.privateRow 12 10, 508851070832744640⟩, ⟨.privateRow 12 11, 726784482178980225⟩, ⟨.privateRow 13 6, 17940262112692920⟩, ⟨.privateRow 13 7, 86587711353823680⟩, ⟨.privateRow 13 8, 262254013429183776⟩, ⟨.privateRow 13 9, 108970480980801440⟩, ⟨.privateRow 14 4, 2990043685448820⟩, ⟨.privateRow 14 5, 35631353918265105⟩, ⟨.privateRow 14 6, 95088331418240160⟩, ⟨.privateRow 15 2, 504812570270580⟩, ⟨.privateRow 15 3, 10872886128904800⟩, ⟨.privateRow 15 4, 21791075950013370⟩, ⟨.privateRow 16 1, 3786094277029350⟩, ⟨.privateRow 16 2, 2718221532226200⟩, ⟨.hall 7 21, 366246507997810440⟩, ⟨.hall 7 22, 28433282691646352520⟩, ⟨.hall 6 23, 121315925871712947375⟩, ⟨.hall 5 24, 291255045143088970944⟩, ⟨.hall 4 25, 595736303888822896800⟩, ⟨.hall 3 26, 1084352208776600443680⟩, ⟨.hall 2 27, 1624022423566077506400⟩, ⟨.assumptionRow 17, 16411137348666060⟩]
  caps := #[0, 0, 0, 4708439325638848800, 495331065509516940, 35549372504681640, 75887332685882256, 50767613033084750, 0, 1935355253944200, 763336129042080, 32090153294695860, 7558071882606960, 2019820662845700, 82372430341105905, 16411137348666060, 16411137348666060, 210917912027333940, 18944087448000000, 0, 0, 0] }

theorem case_51_30_17_checked :
    (Witness.linear .conditional case_51_30_17).check 51 30 17 = true := by
  change case_51_30_17.check 51 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_30_18 : Certificate := {
  objectiveScale := 16559209889745336000000
  eta := 106002897898178232998276630400
  rows := #[⟨.count 2, 20628327431599208837967971520⟩, ⟨.count 3, 4332766263704457338489970240⟩, ⟨.count 4, 880130496687620651016223680⟩, ⟨.count 5, 172105909183891056146572800⟩, ⟨.count 6, 35222655433467899971173600⟩, ⟨.count 7, 6963680680009971042205080⟩, ⟨.count 8, 1349850268108949459973120⟩, ⟨.count 9, 282300416647785103407840⟩, ⟨.count 10, 105457052196011676560400⟩, ⟨.count 11, 40560404690773721754000⟩, ⟨.count 12, 29203491377357079662880⟩, ⟨.count 13, 14060940292801556874720⟩, ⟨.path 9, 38305290910147351009920⟩, ⟨.path 10, 7162094752029152812800⟩, ⟨.privateRow 2 28, 1055941463638664917399285200⟩, ⟨.privateRow 4 23, 35078530795466684013207720⟩, ⟨.privateRow 4 24, 170552175281536484111916240⟩, ⟨.privateRow 5 21, 19876545197904280798104192⟩, ⟨.privateRow 5 22, 57403788745362355941044400⟩, ⟨.privateRow 5 23, 139606389187129057690136640⟩, ⟨.privateRow 6 19, 7913672958542376228553350⟩, ⟨.privateRow 6 20, 20063204180291221465616100⟩, ⟨.privateRow 6 21, 47947806398453308942795200⟩, ⟨.privateRow 6 22, 85918203914139513153237000⟩, ⟨.privateRow 7 16, 182792223806420239371360⟩, ⟨.privateRow 7 17, 2509375665826049275106280⟩, ⟨.privateRow 7 18, 7062693134571782005197900⟩, ⟨.privateRow 7 19, 16996864625938521950161536⟩, ⟨.privateRow 7 20, 31197711274653454315785000⟩, ⟨.privateRow 7 21, 48267692790114544361695080⟩, ⟨.privateRow 8 14, 88857331017009838583300⟩, ⟨.privateRow 8 15, 799715979153088547249700⟩, ⟨.privateRow 8 16, 2388100055800635847061820⟩, ⟨.privateRow 8 17, 6209955693064587587233110⟩, ⟨.privateRow 8 18, 11809783751924027619077328⟩, ⟨.privateRow 8 19, 18809144067926982611852010⟩, ⟨.privateRow 8 20, 24952896167112962868799980⟩, ⟨.privateRow 9 12, 21091410439202335312080⟩, ⟨.privateRow 9 13, 251895135501812506063360⟩, ⟨.privateRow 9 14, 817562557217028984821460⟩, ⟨.privateRow 9 15, 2280808128154327264041120⟩, ⟨.privateRow 9 16, 4686980097600518958240000⟩, ⟨.privateRow 9 17, 7772887793860700640345216⟩, ⟨.privateRow 9 18, 10772843485869500497862400⟩, ⟨.privateRow 9 19, 11683559772526339796978880⟩, ⟨.privateRow 10 11, 69682775258749253973372⟩, ⟨.privateRow 10 12, 281399074321323465146640⟩, ⟨.privateRow 10 13, 861705797655487718663730⟩, ⟨.privateRow 10 14, 1922447295472129343363160⟩, ⟨.privateRow 10 15, 3428571008511102699865620⟩, ⟨.privateRow 10 16, 5029652423274704592383016⟩, ⟨.privateRow 10 17, 5813117200281689801783280⟩, ⟨.privateRow 11 9, 9989256692438486845200⟩, ⟨.privateRow 11 10, 90634067936292552792120⟩, ⟨.privateRow 11 11, 333414720579309644074800⟩, ⟨.privateRow 11 12, 825404235457245237693900⟩, ⟨.privateRow 11 13, 1602083309435314251202800⟩, ⟨.privateRow 11 14, 2550143262194464178642400⟩, ⟨.privateRow 11 15, 1375956419491738364520240⟩, ⟨.privateRow 12 8, 19395248061224525129640⟩, ⟨.privateRow 12 9, 125088288066346157889336⟩, ⟨.privateRow 12 10, 369550353849271687092000⟩, ⟨.privateRow 12 11, 798735769373061515640645⟩, ⟨.privateRow 12 12, 1205455227409795010528880⟩, ⟨.privateRow 13 6, 721073861169310608960⟩, ⟨.privateRow 13 7, 35594827874085060060480⟩, ⟨.privateRow 13 8, 164729323584129008616912⟩, ⟨.privateRow 13 9, 422429103668354465082400⟩, ⟨.privateRow 13 10, 280948403158092646016040⟩, ⟨.privateRow 14 5, 4101107585400454088460⟩, ⟨.privateRow 14 6, 59279646007152018187740⟩, ⟨.privateRow 14 7, 226029615206785026761124⟩, ⟨.privateRow 14 8, 7421051821200821683880⟩, ⟨.privateRow 15 4, 11717450244001297395600⟩, ⟨.privateRow 15 5, 78613438909754158890480⟩, ⟨.privateRow 16 2, 1352013489692457391800⟩, ⟨.privateRow 16 3, 21970219207502432616750⟩, ⟨.privateRow 17 1, 4326443167015863653760⟩, ⟨.hall 8 21, 10329678046011761918601120⟩, ⟨.hall 7 22, 55219452238137140170897680⟩, ⟨.hall 6 23, 147543204109903336481046300⟩, ⟨.hall 5 24, 319554553470325302157636608⟩, ⟨.hall 4 25, 613237625768370792045336480⟩, ⟨.hall 3 26, 1066020814338554833418980320⟩, ⟨.hall 2 27, 1526492337066586104092883720⟩, ⟨.assumptionRow 18, 8473161479165073113280⟩]
  caps := #[0, 103588653059789117810990400, 0, 193533380795437578931200, 450366373182493273694760, 0, 0, 16369634624265987679956, 5509416128469903875456, 0, 3447218206389760470162, 3123336281447611682640, 2038248898909895485671, 8404823125332811361184, 15742202067407023940732, 8499194006739554577360, 8473161479165073113280, 87749855845213913619840, 173678147308033622886720, 16559209889745336000000, 0, 0] }

theorem case_51_30_18_checked :
    (Witness.linear .conditional case_51_30_18).check 51 30 18 = true := by
  change case_51_30_18.check 51 30 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_30_19 : Certificate := {
  objectiveScale := 99428917087500000
  eta := 1044435598269493510080000
  rows := #[⟨.count 2, 184150487063305434672000⟩, ⟨.count 3, 35021864036155731134400⟩, ⟨.count 4, 6567503623467452265600⟩, ⟨.count 5, 1248035585352716160000⟩, ⟨.count 6, 251025339326625864000⟩, ⟨.count 7, 55842501333253635000⟩, ⟨.count 8, 13189466981568477600⟩, ⟨.count 9, 3240092385050320800⟩, ⟨.count 10, 736384632965982000⟩, ⟨.count 11, 163641029547996000⟩, ⟨.path 7, 2492183470469893200⟩, ⟨.path 11, 28793921973905088⟩, ⟨.path 12, 16114686837369120⟩, ⟨.privateRow 2 28, 8726534275014847090800⟩, ⟨.privateRow 6 19, 45131968670129591250⟩, ⟨.privateRow 6 20, 125672219667122228100⟩, ⟨.privateRow 7 17, 16866714688411302000⟩, ⟨.privateRow 7 18, 49194584507866297500⟩, ⟨.privateRow 7 19, 124931198538319052880⟩, ⟨.privateRow 7 20, 160977089954479248450⟩, ⟨.privateRow 8 14, 37425309535513900⟩, ⟨.privateRow 8 15, 5123327900098508100⟩, ⟨.privateRow 8 16, 16917365483271396000⟩, ⟨.privateRow 8 17, 46041994617782613450⟩, ⟨.privateRow 8 18, 93783492239104247580⟩, ⟨.privateRow 8 19, 138418492193664883200⟩, ⟨.privateRow 8 20, 140817651510204669000⟩, ⟨.privateRow 8 21, 55496809658333493450⟩, ⟨.privateRow 9 13, 1477617889029682400⟩, ⟨.privateRow 9 14, 5520157396752398400⟩, ⟨.privateRow 9 15, 16621253144089308000⟩, ⟨.privateRow 9 16, 36399219672459243600⟩, ⟨.privateRow 9 18, 225352789141037758200⟩, ⟨.privateRow 9 19, 35717382049342593600⟩, ⟨.privateRow 10 11, 387829240028750520⟩, ⟨.privateRow 10 12, 1756413717148490400⟩, ⟨.privateRow 10 13, 5940169372592254800⟩, ⟨.privateRow 10 14, 14413268109688133400⟩, ⟨.privateRow 10 15, 27820338698405553300⟩, ⟨.privateRow 10 16, 17614320420546289440⟩, ⟨.privateRow 10 17, 85457436655702211100⟩, ⟨.privateRow 10 18, 53638802135340622200⟩, ⟨.privateRow 11 9, 91963553795568000⟩, ⟨.privateRow 11 10, 524395117415169000⟩, ⟨.privateRow 11 11, 2113283396738514000⟩, ⟨.privateRow 11 12, 5810186327530835250⟩, ⟨.privateRow 11 13, 12393151478040762000⟩, ⟨.privateRow 11 14, 21651443795876895000⟩, ⟨.privateRow 11 16, 58460757806021571000⟩, ⟨.privateRow 12 7, 17727778201032900⟩, ⟨.privateRow 12 9, 1008028742015655360⟩, ⟨.privateRow 12 11, 10228587103184424975⟩, ⟨.privateRow 12 12, 202213557941452200⟩, ⟨.privateRow 12 13, 35446010675342166900⟩, ⟨.privateRow 12 15, 11045769494489730000⟩, ⟨.privateRow 13 5, 1678369533825600⟩, ⟨.privateRow 13 6, 30909972247954800⟩, ⟨.privateRow 13 7, 55538773664774400⟩, ⟨.privateRow 13 8, 1274218150080395520⟩, ⟨.privateRow 13 9, 421830209501500800⟩, ⟨.privateRow 13 10, 9556636125602966400⟩, ⟨.privateRow 13 11, 4031803270863482400⟩, ⟨.privateRow 13 12, 23720676349812842400⟩, ⟨.privateRow 14 4, 2727350492466600⟩, ⟨.privateRow 14 5, 57615279153356925⟩, ⟨.privateRow 14 6, 125706063607324200⟩, ⟨.privateRow 14 7, 1712503374219778140⟩, ⟨.privateRow 14 8, 967148788523017100⟩, ⟨.privateRow 14 9, 9887668291626099975⟩, ⟨.privateRow 14 10, 8304197817312411300⟩, ⟨.privateRow 15 3, 5454700984933200⟩, ⟨.privateRow 15 4, 115230558306713850⟩, ⟨.privateRow 15 5, 248188894814460600⟩, ⟨.privateRow 15 6, 2552800060948737600⟩, ⟨.privateRow 15 7, 2048543258786024000⟩, ⟨.privateRow 15 8, 11851019727390493650⟩, ⟨.privateRow 15 9, 13802341599375615000⟩, ⟨.privateRow 16 2, 13636752462333000⟩, ⟨.privateRow 16 3, 243756950264202375⟩, ⟨.privateRow 16 4, 523775265030517500⟩, ⟨.privateRow 16 5, 4396488993856159200⟩, ⟨.privateRow 16 6, 4697861223273718500⟩, ⟨.privateRow 16 7, 17195944855001913000⟩, ⟨.privateRow 16 8, 27186814141155454500⟩, ⟨.privateRow 17 1, 21818803939732800⟩, ⟨.privateRow 17 2, 614562977635807200⟩, ⟨.privateRow 17 3, 1315078819276622400⟩, ⟨.privateRow 17 4, 9218444664537108000⟩, ⟨.privateRow 17 5, 12858548455149196800⟩, ⟨.privateRow 17 6, 33292767461539786200⟩, ⟨.privateRow 17 7, 62685423718852334400⟩, ⟨.privateRow 17 8, 44957645517819434400⟩, ⟨.privateRow 18 0, 92729916743864400⟩, ⟨.privateRow 18 1, 1908690786311208900⟩, ⟨.privateRow 18 2, 4274006162649022800⟩, ⟨.privateRow 18 3, 24712522812239862600⟩, ⟨.privateRow 18 5, 174343834718058055050⟩, ⟨.privateRow 18 6, 133464844456347690000⟩, ⟨.privateRow 18 9, 498469667456643082200⟩, ⟨.privateRow 19 0, 8438422423691660400⟩, ⟨.privateRow 19 1, 18411103469872713600⟩, ⟨.privateRow 19 2, 90411668825267790000⟩, ⟨.privateRow 19 3, 57863468048171385600⟩, ⟨.privateRow 19 4, 51534651230402640300⟩, ⟨.privateRow 20 0, 231125102487866386800⟩, ⟨.privateRow 20 2, 1549856918484701626800⟩, ⟨.privateRow 20 4, 255219225141041647200⟩, ⟨.privateRow 21 8, 129180192417542618352000⟩, ⟨.hall 20 1, 6871286830720352040000⟩, ⟨.hall 15 6, 15460889480021700⟩, ⟨.hall 16 10, 151598183217624000⟩, ⟨.hall 10 14, 3437685972896175⟩, ⟨.hall 9 15, 5303013977225250⟩, ⟨.hall 8 21, 313614066073472564400⟩, ⟨.hall 7 22, 869211463747809382200⟩, ⟨.hall 6 23, 2611567645685161663500⟩, ⟨.hall 5 24, 5563629181721922030720⟩, ⟨.hall 4 25, 9527442565931603913600⟩, ⟨.hall 3 26, 12918019241754261835200⟩, ⟨.hall 2 27, 13143790094763644830800⟩]
  caps := #[0, 314064891114487793280, 94593834846376866000, 0, 6154261257345801600, 578354192683643376, 216531301459575102, 94190383305630040, 29865561928770568, 171929888991855280, 5625092389676760, 23442046717888968, 155063141837237205, 0, 306058017628769120, 195988611365146600, 0, 3901137719094844800, 0, 12107627142068858400, 208716853041699631200, 0] }

theorem case_51_30_19_checked :
    (Witness.linear .conditional case_51_30_19).check 51 30 19 = true := by
  change case_51_30_19.check 51 30 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_31_1_checked :
    (Witness.rising).check 51 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_31_2_checked :
    (Witness.rising).check 51 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_31_3_checked :
    (Witness.rising).check 51 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_31_4_checked :
    (Witness.rising).check 51 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_31_5_checked :
    (Witness.rising).check 51 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_31_6_checked :
    (Witness.rising).check 51 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_31_7_checked :
    (Witness.rising).check 51 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_31_8_checked :
    (Witness.rising).check 51 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_31_9_checked :
    (Witness.rising).check 51 31 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_31_10_checked :
    (Witness.linear .positive case_51_31_10).check 51 31 10 = true := by
  change case_51_31_10.check 51 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_31_11_checked :
    (Witness.linear .positive case_51_31_11).check 51 31 11 = true := by
  change case_51_31_11.check 51 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_31_12_checked :
    (Witness.linear .positive case_51_31_12).check 51 31 12 = true := by
  change case_51_31_12.check 51 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_31_13_checked :
    (Witness.linear .positive case_51_31_13).check 51 31 13 = true := by
  change case_51_31_13.check 51 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_31_14 : Certificate := {
  objectiveScale := 25729704000000
  eta := 234327833786612966400
  rows := #[⟨.count 2, 50217793046935113600⟩, ⟨.count 3, 10228335596648769600⟩, ⟨.count 4, 2253597505621862400⟩, ⟨.count 5, 470705386537386000⟩, ⟨.count 6, 107727620488488000⟩, ⟨.count 7, 23474974016894400⟩, ⟨.count 8, 5689403607888000⟩, ⟨.count 9, 1335773020982400⟩, ⟨.count 10, 371048061384000⟩, ⟨.count 11, 111314418415200⟩, ⟨.count 12, 49473074851200⟩, ⟨.path 11, 17919233171840⟩, ⟨.path 12, 8270281603584⟩, ⟨.privateRow 3 28, 8344120558890916800⟩, ⟨.privateRow 5 22, 138534504198330240⟩, ⟨.privateRow 5 25, 1375014445540936200⟩, ⟨.privateRow 6 19, 14367511005447600⟩, ⟨.privateRow 6 20, 38084304307849800⟩, ⟨.privateRow 6 21, 79852428739203120⟩, ⟨.privateRow 6 23, 318323506113412800⟩, ⟨.privateRow 7 17, 9740563766183250⟩, ⟨.privateRow 7 18, 13465132216707600⟩, ⟨.privateRow 7 19, 26206447265598600⟩, ⟨.privateRow 7 21, 139876505526057300⟩, ⟨.privateRow 7 22, 59881856420786400⟩, ⟨.privateRow 7 23, 87497108389290600⟩, ⟨.privateRow 8 14, 842897512777320⟩, ⟨.privateRow 8 15, 3122987849982000⟩, ⟨.privateRow 8 16, 6841198631767500⟩, ⟨.privateRow 8 17, 9703790252956800⟩, ⟨.privateRow 8 18, 19043011061474400⟩, ⟨.privateRow 8 19, 10353477739484880⟩, ⟨.privateRow 9 11, 87265007029200⟩, ⟨.privateRow 9 12, 510097385397600⟩, ⟨.privateRow 9 14, 5373325629672000⟩, ⟨.privateRow 9 15, 3374991325005300⟩, ⟨.privateRow 9 16, 7516962551498400⟩, ⟨.privateRow 9 17, 5839884210560400⟩, ⟨.privateRow 9 18, 21963571580190240⟩, ⟨.privateRow 9 20, 5268882471652800⟩, ⟨.privateRow 10 9, 88221217392000⟩, ⟨.privateRow 10 10, 274631784827400⟩, ⟨.privateRow 10 11, 398033374939200⟩, ⟨.privateRow 10 12, 736024427218080⟩, ⟨.privateRow 10 13, 3768948793209600⟩, ⟨.privateRow 10 14, 2929593102836400⟩, ⟨.privateRow 10 15, 5410073487218400⟩, ⟨.privateRow 10 16, 4674643379406000⟩, ⟨.privateRow 10 17, 6114872051608320⟩, ⟨.privateRow 11 6, 6071695549920⟩, ⟨.privateRow 11 7, 57584731604400⟩, ⟨.privateRow 11 8, 160873984656000⟩, ⟨.privateRow 11 9, 291216508783200⟩, ⟨.privateRow 11 10, 409686123974400⟩, ⟨.privateRow 11 11, 649671423841440⟩, ⟨.privateRow 11 12, 3441751866352800⟩, ⟨.privateRow 11 13, 2356998480837000⟩, ⟨.privateRow 11 15, 11707690724730000⟩, ⟨.privateRow 11 20, 40063071136888800⟩, ⟨.privateRow 12 4, 8245512475200⟩, ⟨.privateRow 12 5, 37654506970080⟩, ⟨.privateRow 12 6, 103363388528400⟩, ⟨.privateRow 12 7, 204235001308800⟩, ⟨.privateRow 12 8, 322605675592200⟩, ⟨.privateRow 12 9, 434388589034400⟩, ⟨.privateRow 12 10, 758587147718400⟩, ⟨.privateRow 12 11, 3502510465854400⟩, ⟨.privateRow 12 12, 2582391438326700⟩, ⟨.privateRow 12 13, 707936142513600⟩, ⟨.privateRow 12 14, 8122516914111600⟩, ⟨.privateRow 12 16, 9652403041281000⟩, ⟨.privateRow 13 2, 8366770011600⟩, ⟨.privateRow 13 3, 28215113001075⟩, ⟨.privateRow 13 4, 74621887900560⟩, ⟨.privateRow 13 5, 157695426088200⟩, ⟨.privateRow 13 6, 273529019610000⟩, ⟨.privateRow 13 8, 1413355797453600⟩, ⟨.privateRow 13 9, 544822236798840⟩, ⟨.privateRow 13 10, 4038239734729200⟩, ⟨.privateRow 13 12, 1894995456354000⟩, ⟨.privateRow 13 13, 9147365402175000⟩, ⟨.privateRow 13 17, 42883879694455800⟩, ⟨.privateRow 14 1, 43912550682000⟩, ⟨.privateRow 14 2, 54552899501100⟩, ⟨.privateRow 14 3, 140880470290560⟩, ⟨.privateRow 14 4, 264150881794800⟩, ⟨.privateRow 14 5, 297721896872400⟩, ⟨.privateRow 14 6, 264150881794800⟩, ⟨.privateRow 14 9, 11825537302378800⟩, ⟨.privateRow 14 12, 8759090109369600⟩, ⟨.privateRow 14 13, 3780803055949920⟩, ⟨.privateRow 14 17, 46180465030299600⟩, ⟨.privateRow 15 0, 156058449346800⟩, ⟨.privateRow 15 1, 103841922734550⟩, ⟨.privateRow 15 2, 303709709503200⟩, ⟨.privateRow 15 4, 1700636948010000⟩, ⟨.privateRow 15 6, 43851134527200⟩, ⟨.privateRow 15 8, 17737242544221200⟩, ⟨.privateRow 15 9, 7881936909496650⟩, ⟨.privateRow 15 12, 27864472583067120⟩, ⟨.privateRow 16 0, 874281994636050⟩, ⟨.privateRow 16 2, 999179422441200⟩, ⟨.privateRow 16 3, 3834163300968000⟩, ⟨.privateRow 16 4, 341673423191100⟩, ⟨.privateRow 16 6, 217063115909640⟩, ⟨.privateRow 16 7, 31826991028232400⟩, ⟨.privateRow 16 9, 55241988757956000⟩, ⟨.privateRow 16 13, 122975634433251600⟩, ⟨.privateRow 17 0, 7953621333577920⟩, ⟨.privateRow 17 3, 15864366002284800⟩, ⟨.privateRow 17 5, 13088101951884960⟩, ⟨.privateRow 17 7, 166535646150673800⟩, ⟨.privateRow 17 9, 535958310888000⟩, ⟨.privateRow 17 10, 239444734972322880⟩, ⟨.privateRow 17 13, 368203359580056000⟩, ⟨.privateRow 18 0, 62347264650871200⟩, ⟨.privateRow 18 3, 108341536371868800⟩, ⟨.privateRow 18 6, 496337592755604600⟩, ⟨.privateRow 18 7, 418078108681833600⟩, ⟨.privateRow 18 11, 1853844066807532800⟩, ⟨.privateRow 19 0, 748107101362420800⟩, ⟨.privateRow 19 3, 892177642636600320⟩, ⟨.privateRow 19 5, 1795835512292421600⟩, ⟨.privateRow 19 11, 39869188405323076800⟩, ⟨.privateRow 20 1, 29517601886563190400⟩, ⟨.privateRow 20 9, 144065915541680932800⟩, ⟨.privateRow 20 11, 605762378831350540800⟩, ⟨.hall 15 1, 301476549874500⟩, ⟨.hall 10 8, 135065810880⟩, ⟨.hall 13 9, 1318321384380⟩, ⟨.hall 14 9, 3075532059600⟩, ⟨.hall 17 9, 1093172910429600⟩, ⟨.hall 16 14, 2829859881488640⟩, ⟨.hall 14 15, 174974625025200⟩, ⟨.hall 15 15, 2286197169881625⟩, ⟨.hall 6 17, 414688498224⟩, ⟨.hall 11 17, 24671441274480⟩, ⟨.hall 8 18, 2027206621440⟩, ⟨.hall 9 21, 45234131846904000⟩, ⟨.hall 4 24, 3031710026881536⟩, ⟨.hall 3 27, 4308209003505607200⟩]
  caps := #[0, 0, 3338749590816640, 3702984693408000, 1010664243388800, 93187986932040, 0, 47941375741116, 8600527595660, 4023027904896, 778773775360, 39311011979120, 0, 72432610103700, 9893161818540, 697675200302080, 0, 8982661290482880, 2033247000264480, 6598358919472320, 0] }

theorem case_51_31_14_checked :
    (Witness.linear .positive case_51_31_14).check 51 31 14 = true := by
  change case_51_31_14.check 51 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_31_15 : Certificate := {
  objectiveScale := 3344861520000
  eta := 41132013377437382400
  rows := #[⟨.count 2, 8987377723618694400⟩, ⟨.count 3, 1887130650969083520⟩, ⟨.count 4, 405956262999006720⟩, ⟨.count 5, 89076271269585600⟩, ⟨.count 6, 18844294210822080⟩, ⟨.count 7, 4373419816846080⟩, ⟨.count 8, 1009250726964480⟩, ⟨.count 9, 237470759285760⟩, ⟨.count 10, 60716955499200⟩, ⟨.count 11, 14841922455360⟩, ⟨.count 12, 9894614970240⟩, ⟨.path 10, 5423135477760⟩, ⟨.path 11, 959477815296⟩, ⟨.privateRow 2 29, 1079141339806770240⟩, ⟨.privateRow 6 19, 1600218385365600⟩, ⟨.privateRow 6 23, 115863467647767840⟩, ⟨.privateRow 7 17, 963576477503640⟩, ⟨.privateRow 7 18, 1933387572093120⟩, ⟨.privateRow 7 20, 11529382052876688⟩, ⟨.privateRow 7 22, 4446922670910720⟩, ⟨.privateRow 8 14, 45515228863104⟩, ⟨.privateRow 8 15, 393310945067040⟩, ⟨.privateRow 8 17, 3557290771354320⟩, ⟨.privateRow 8 18, 628720326234000⟩, ⟨.privateRow 8 20, 18830379908520180⟩, ⟨.privateRow 8 22, 9728261756052840⟩, ⟨.privateRow 8 23, 12395478903968160⟩, ⟨.privateRow 9 12, 37479602160000⟩, ⟨.privateRow 9 13, 162106775262432⟩, ⟨.privateRow 9 14, 321849836948640⟩, ⟨.privateRow 9 15, 277461494790480⟩, ⟨.privateRow 9 16, 2529958813462080⟩, ⟨.privateRow 9 17, 1022855822548560⟩, ⟨.privateRow 9 18, 1111989812405472⟩, ⟨.privateRow 9 19, 7810149416509440⟩, ⟨.privateRow 10 10, 21588250844160⟩, ⟨.privateRow 10 11, 73289658405600⟩, ⟨.privateRow 10 12, 165015192390048⟩, ⟨.privateRow 10 13, 277274096779680⟩, ⟨.privateRow 10 14, 296332474478040⟩, ⟨.privateRow 10 15, 1703447918172000⟩, ⟨.privateRow 10 17, 2130085725479712⟩, ⟨.privateRow 11 8, 11053599590880⟩, ⟨.privateRow 11 9, 36992367331920⟩, ⟨.privateRow 11 10, 83899793053440⟩, ⟨.privateRow 11 11, 157594231162368⟩, ⟨.privateRow 11 12, 289117651062240⟩, ⟨.privateRow 11 13, 299621309567580⟩, ⟨.privateRow 11 14, 1327388298556320⟩, ⟨.privateRow 11 15, 532172871069840⟩, ⟨.privateRow 11 17, 644611677549840⟩, ⟨.privateRow 11 18, 6871135463992800⟩, ⟨.privateRow 12 6, 5536272661920⟩, ⟨.privateRow 12 7, 20169792054720⟩, ⟨.privateRow 12 8, 47411696732400⟩, ⟨.privateRow 12 9, 91375270066080⟩, ⟨.privateRow 12 10, 185111755068240⟩, ⟨.privateRow 12 11, 88043749874080⟩, ⟨.privateRow 12 12, 742920674015520⟩, ⟨.privateRow 12 14, 2311491997214400⟩, ⟨.privateRow 12 18, 10905927075323280⟩, ⟨.privateRow 13 4, 2885929366320⟩, ⟨.privateRow 13 5, 3180411954720⟩, ⟨.privateRow 13 6, 47189702165760⟩, ⟨.privateRow 13 7, 50400695004660⟩, ⟨.privateRow 13 8, 41489919591120⟩, ⟨.privateRow 13 9, 371171744071128⟩, ⟨.privateRow 13 11, 675307471718880⟩, ⟨.privateRow 13 13, 1667242622485440⟩, ⟨.privateRow 14 2, 1722723142140⟩, ⟨.privateRow 14 3, 5206452162912⟩, ⟨.privateRow 14 4, 11812958688960⟩, ⟨.privateRow 14 5, 74739680935920⟩, ⟨.privateRow 14 6, 87667466566680⟩, ⟨.privateRow 14 7, 69744185390880⟩, ⟨.privateRow 14 8, 551041709065848⟩, ⟨.privateRow 14 9, 145219180426320⟩, ⟨.privateRow 14 10, 859064606880480⟩, ⟨.privateRow 14 12, 2867759790615720⟩, ⟨.privateRow 14 17, 23812627752753840⟩, ⟨.privateRow 15 0, 1576347973200⟩, ⟨.privateRow 15 1, 4689635220270⟩, ⟨.privateRow 15 2, 11433777298944⟩, ⟨.privateRow 15 3, 23735296625040⟩, ⟨.privateRow 15 4, 161612044513920⟩, ⟨.privateRow 15 7, 1753119634914648⟩, ⟨.privateRow 15 10, 3197374151811840⟩, ⟨.privateRow 16 0, 26127967655790⟩, ⟨.privateRow 16 1, 22510249057296⟩, ⟨.privateRow 16 2, 65463479401320⟩, ⟨.privateRow 16 3, 420521136235200⟩, ⟨.privateRow 16 4, 32157498653280⟩, ⟨.privateRow 16 6, 3506775228140184⟩, ⟨.privateRow 16 7, 1402424246823600⟩, ⟨.privateRow 16 9, 2200491693560160⟩, ⟨.privateRow 16 12, 13449873811734360⟩, ⟨.privateRow 17 0, 287273654635968⟩, ⟨.privateRow 17 1, 124036066234080⟩, ⟨.privateRow 17 2, 1385246095833600⟩, ⟨.privateRow 17 3, 305496237206160⟩, ⟨.privateRow 17 4, 23387271747840⟩, ⟨.privateRow 17 5, 8766134132884128⟩, ⟨.privateRow 17 9, 22756789880304480⟩, ⟨.privateRow 17 11, 29584898761017600⟩, ⟨.privateRow 17 13, 37238383440498240⟩, ⟨.privateRow 18 0, 3566419731594720⟩, ⟨.privateRow 18 1, 4625732498587200⟩, ⟨.privateRow 18 2, 2611903501727520⟩, ⟨.privateRow 18 3, 496979524641600⟩, ⟨.privateRow 18 4, 28645899800341824⟩, ⟨.privateRow 18 7, 20565486043502400⟩, ⟨.privateRow 18 9, 35278919855891712⟩, ⟨.privateRow 19 0, 85281686428498560⟩, ⟨.privateRow 19 2, 9243819158333760⟩, ⟨.hall 17 5, 615490026671520⟩, ⟨.hall 12 7, 370964604780⟩, ⟨.hall 18 10, 41562779937719040⟩, ⟨.hall 9 11, 50046228540⟩, ⟨.hall 14 11, 2351097018270⟩, ⟨.hall 15 12, 14587931222865⟩, ⟨.hall 14 16, 484254097367040⟩, ⟨.hall 12 18, 1023832264815360⟩, ⟨.hall 10 20, 2216008248854400⟩, ⟨.hall 8 21, 276247481590080⟩, ⟨.hall 5 24, 2223691031874312⟩]
  caps := #[0, 0, 0, 0, 0, 16500150418752, 16947298368, 0, 2884588971264, 785191983576, 201454987608, 3471038489016, 0, 27715817739456, 11610657079164, 0, 11601944704350, 314545954859136, 0, 0, 0] }

theorem case_51_31_15_checked :
    (Witness.linear .positive case_51_31_15).check 51 31 15 = true := by
  change case_51_31_15.check 51 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_31_16 : Certificate := {
  objectiveScale := 356621265000000
  eta := 3903801996913147929600
  rows := #[⟨.count 2, 777145767904006300800⟩, ⟨.count 3, 152670619031325595200⟩, ⟨.count 4, 32789071926830419200⟩, ⟨.count 5, 6749456998590306000⟩, ⟨.count 6, 1506096449426368800⟩, ⟨.count 7, 338055704592606000⟩, ⟨.count 8, 77474835216979200⟩, ⟨.count 9, 19368708804244800⟩, ⟨.count 10, 5869305698256000⟩, ⟨.count 11, 2152078756027200⟩, ⟨.count 12, 1434719170684800⟩, ⟨.path 10, 734813129930880⟩, ⟨.privateRow 2 29, 52317034559021232000⟩, ⟨.privateRow 3 26, 5531161229472278400⟩, ⟨.privateRow 3 27, 20292667950165811200⟩, ⟨.privateRow 4 24, 4107959665463253600⟩, ⟨.privateRow 4 25, 7591099132093276800⟩, ⟨.privateRow 4 26, 13578182231360947200⟩, ⟨.privateRow 5 21, 375746972805804600⟩, ⟨.privateRow 5 22, 1554589957395515040⟩, ⟨.privateRow 5 23, 2859484977122974200⟩, ⟨.privateRow 5 24, 5124458197893434400⟩, ⟨.privateRow 5 25, 6367104339602806800⟩, ⟨.privateRow 6 19, 259564609963058400⟩, ⟨.privateRow 6 20, 585574651518456600⟩, ⟨.privateRow 6 21, 1053956658778143120⟩, ⟨.privateRow 6 22, 1880289143130598200⟩, ⟨.privateRow 6 23, 2470785678470709600⟩, ⟨.privateRow 6 24, 2505109341963828600⟩, ⟨.privateRow 7 16, 14321571721657200⟩, ⟨.privateRow 7 17, 110908915890973200⟩, ⟨.privateRow 7 18, 238946621880938400⟩, ⟨.privateRow 7 19, 400282378623527400⟩, ⟨.privateRow 7 20, 709817061702228480⟩, ⟨.privateRow 7 21, 938895597287247600⟩, ⟨.privateRow 7 22, 1015166293200259200⟩, ⟨.privateRow 7 23, 705920261954707800⟩, ⟨.privateRow 8 14, 11495687355111960⟩, ⟨.privateRow 8 15, 45472627048648800⟩, ⟨.privateRow 8 16, 98749030419789750⟩, ⟨.privateRow 8 17, 164762124762034800⟩, ⟨.privateRow 8 18, 283237476279357600⟩, ⟨.privateRow 8 19, 381204883650951360⟩, ⟨.privateRow 8 20, 416965258980270000⟩, ⟨.privateRow 8 21, 153873631055944800⟩, ⟨.privateRow 9 12, 6260592744806400⟩, ⟨.privateRow 9 13, 19978464451785840⟩, ⟨.privateRow 9 14, 42417206592560800⟩, ⟨.privateRow 9 15, 72259033231885500⟩, ⟨.privateRow 9 16, 124957207770595200⟩, ⟨.privateRow 9 17, 169396495416548400⟩, ⟨.privateRow 9 18, 92419826578279200⟩, ⟨.privateRow 10 10, 2926501035658200⟩, ⟨.privateRow 10 11, 9470925104004000⟩, ⟨.privateRow 10 12, 19887164140924080⟩, ⟨.privateRow 10 13, 34270223827039200⟩, ⟨.privateRow 10 14, 60906274339610700⟩, ⟨.privateRow 10 15, 43991843662166400⟩, ⟨.privateRow 11 8, 1279207652184000⟩, ⟨.privateRow 11 9, 4744355439423600⟩, ⟨.privateRow 11 10, 10413571170693600⟩, ⟨.privateRow 11 11, 18263322897739920⟩, ⟨.privateRow 11 12, 17466618994624800⟩, ⟨.privateRow 12 6, 546559684070400⟩, ⟨.privateRow 12 7, 2483167795416000⟩, ⟨.privateRow 12 8, 6037776509965200⟩, ⟨.privateRow 12 9, 5510625905584800⟩, ⟨.privateRow 13 4, 227163868691760⟩, ⟨.privateRow 13 5, 1357859215112400⟩, ⟨.privateRow 13 6, 2069306496180000⟩, ⟨.privateRow 14 2, 83264951870100⟩, ⟨.privateRow 14 3, 710527589291520⟩, ⟨.privateRow 15 1, 145713665772675⟩, ⟨.hall 6 24, 417044168534657664⟩, ⟨.hall 5 25, 2316623110915113000⟩, ⟨.hall 4 26, 6532116970886707200⟩, ⟨.hall 3 27, 14562707022273009600⟩, ⟨.hall 2 28, 27454142900251267200⟩, ⟨.assumptionRow 16, 428017793243040⟩]
  caps := #[0, 0, 284433075588261600, 0, 5874377937748320, 1897647661990080, 2257728579986880, 1654530510293232, 153740347851090, 130507026890240, 0, 505620299348640, 0, 3125218784965200, 178222937632740, 136590461697690, 4564679916756960, 356621265000000, 0, 0, 0] }

theorem case_51_31_16_checked :
    (Witness.linear .conditional case_51_31_16).check 51 31 16 = true := by
  change case_51_31_16.check 51 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_31_17 : Certificate := {
  objectiveScale := 3560843518732500000
  eta := 35583326896858577984347200
  rows := #[⟨.count 2, 7056051719228562745094400⟩, ⟨.count 3, 1339199243333761725115200⟩, ⟨.count 4, 275793677373319913808000⟩, ⟨.count 5, 55330154196788283813000⟩, ⟨.count 6, 11008891265316223078800⟩, ⟨.count 7, 2342722535698781035800⟩, ⟨.count 8, 550884098450745259200⟩, ⟨.count 9, 167023370274959998800⟩, ⟨.count 10, 63932390535869856000⟩, ⟨.count 11, 26372111096046315600⟩, ⟨.count 12, 11720938264909473600⟩, ⟨.path 9, 14032764033597609300⟩, ⟨.privateRow 2 29, 664418966953790875226400⟩, ⟨.privateRow 3 26, 65333812215079284676800⟩, ⟨.privateRow 3 27, 215644752432370722661200⟩, ⟨.privateRow 4 24, 40111980977086446027600⟩, ⟨.privateRow 4 25, 79335124135750590307200⟩, ⟨.privateRow 4 26, 150048521432804853658800⟩, ⟨.privateRow 5 21, 2660164613706745945800⟩, ⟨.privateRow 5 22, 14422028488057861791120⟩, ⟨.privateRow 5 23, 28965002407836758212950⟩, ⟨.privateRow 5 24, 56555480617899028365600⟩, ⟨.privateRow 5 25, 76567029215521136292000⟩, ⟨.privateRow 6 19, 1705117447585640088000⟩, ⟨.privateRow 6 20, 5143619803989058091700⟩, ⟨.privateRow 6 21, 10417179231909376486560⟩, ⟨.privateRow 6 22, 20560723392575887220700⟩, ⟨.privateRow 6 23, 30222602106878312531400⟩, ⟨.privateRow 6 24, 34493256196345467120600⟩, ⟨.privateRow 7 17, 750977258830271272800⟩, ⟨.privateRow 7 18, 1952463132041642134200⟩, ⟨.privateRow 7 19, 3842863098627849496200⟩, ⟨.privateRow 7 20, 7690986665976973839480⟩, ⟨.privateRow 7 21, 11556478849879962548550⟩, ⟨.privateRow 7 22, 14454498277751247916200⟩, ⟨.privateRow 7 23, 12731241282850866976200⟩, ⟨.privateRow 8 14, 3076746294538736820⟩, ⟨.privateRow 8 15, 278860656219304559400⟩, ⟨.privateRow 8 16, 771933668540522362875⟩, ⟨.privateRow 8 17, 1507396381854964801200⟩, ⟨.privateRow 8 18, 3016432299717223487100⟩, ⟨.privateRow 8 19, 4678119484981993650600⟩, ⟨.privateRow 8 20, 5990498291331076272750⟩, ⟨.privateRow 8 21, 6005027371055286974400⟩, ⟨.privateRow 8 22, 2316350424602734720200⟩, ⟨.privateRow 9 13, 97869834511994104560⟩, ⟨.privateRow 9 14, 307891683866186820400⟩, ⟨.privateRow 9 15, 632198107663554732300⟩, ⟨.privateRow 9 16, 1275628781164314376800⟩, ⟨.privateRow 9 17, 2034885115435672500000⟩, ⟨.privateRow 9 18, 2717694885690343278720⟩, ⟨.privateRow 9 19, 1830175672822843846500⟩, ⟨.privateRow 10 11, 31312341273818077200⟩, ⟨.privateRow 10 12, 124108753127757357960⟩, ⟨.privateRow 10 13, 278549873765310747600⟩, ⟨.privateRow 10 14, 589476619612762531650⟩, ⟨.privateRow 10 15, 975425615604414374400⟩, ⟨.privateRow 10 16, 1187144576762933388600⟩, ⟨.privateRow 11 9, 9390069859955885100⟩, ⟨.privateRow 11 10, 49257000890136093600⟩, ⟨.privateRow 11 11, 128184443024419061280⟩, ⟨.privateRow 11 12, 294621766386133586400⟩, ⟨.privateRow 11 13, 523346553152222149350⟩, ⟨.privateRow 11 14, 98981040347498509200⟩, ⟨.privateRow 12 7, 2479429248346234800⟩, ⟨.privateRow 12 8, 19372106298947602200⟩, ⟨.privateRow 12 9, 60025411114233364800⟩, ⟨.privateRow 12 10, 158037317605196069040⟩, ⟨.privateRow 12 11, 122418688544610057600⟩, ⟨.privateRow 13 5, 313953703524360900⟩, ⟨.privateRow 13 6, 7438287745038704400⟩, ⟨.privateRow 13 7, 28447693913790701550⟩, ⟨.privateRow 13 8, 71923939352853588000⟩, ⟨.privateRow 14 4, 2137875219237314700⟩, ⟨.privateRow 14 5, 13604660486055639000⟩, ⟨.privateRow 14 6, 13604660486055639000⟩, ⟨.privateRow 15 2, 423256104010619880⟩, ⟨.privateRow 15 3, 5441864194422255600⟩, ⟨.privateRow 15 4, 976744855409122800⟩, ⟨.privateRow 16 1, 1269768312031859640⟩, ⟨.hall 6 24, 10295789381279130704976⟩, ⟨.hall 5 25, 35096884516988305011000⟩, ⟨.hall 4 26, 84730228608205958377600⟩, ⟨.hall 3 27, 173228141968946451387000⟩, ⟨.hall 2 28, 311911142381210961388800⟩, ⟨.assumptionRow 17, 3325520319101355375⟩]
  caps := #[0, 32448871029546395198775, 686366513260300973100, 684401892701068241700, 0, 33021245232577151550, 16968280298226457200, 17723088367667916948, 0, 4332881381329836335, 482865985337880690, 12032911504300131900, 0, 5787810031522844325, 16605506065993887900, 2902264215090735495, 3325520319101355375, 42965445424421144625, 3560843518732500000, 0, 0] }

theorem case_51_31_17_checked :
    (Witness.linear .conditional case_51_31_17).check 51 31 17 = true := by
  change case_51_31_17.check 51 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_31_18 : Certificate := {
  objectiveScale := 176232171784949280000000
  eta := 2244279701928250448666735731200
  rows := #[⟨.count 2, 406371633270958928976692889600⟩, ⟨.count 3, 70523625750073713651158524800⟩, ⟨.count 4, 12914756616055665371128128000⟩, ⟨.count 5, 2233871647149849868161000000⟩, ⟨.count 6, 370524843873921764798971200⟩, ⟨.count 7, 64931202543822302834546400⟩, ⟨.count 8, 14663362606932347852544000⟩, ⟨.count 9, 4399008782079704355763200⟩, ⟨.count 10, 1499662084799899212192000⟩, ⟨.count 11, 824814146639944566705600⟩, ⟨.count 12, 366584065173308696313600⟩, ⟨.path 8, 1776310586075248052544000⟩, ⟨.path 9, 179445023623059195926925⟩, ⟨.privateRow 2 29, 33054151988546898529204684800⟩, ⟨.privateRow 3 26, 3087574654703591011851091200⟩, ⟨.privateRow 3 27, 11308354693794128888157240000⟩, ⟨.privateRow 4 24, 1950318872738295591562430400⟩, ⟨.privateRow 4 25, 4061079371334109289211446400⟩, ⟨.privateRow 4 26, 8078871274305670376533195200⟩, ⟨.privateRow 5 21, 126089644083569303669532000⟩, ⟨.privateRow 5 22, 676952463952290504047509440⟩, ⟨.privateRow 5 23, 1441740761070513104911109400⟩, ⟨.privateRow 5 24, 3004706290193024729334422400⟩, ⟨.privateRow 5 25, 4353071216412674109756402000⟩, ⟨.privateRow 6 19, 74036888876966452773336000⟩, ⟨.privateRow 6 20, 230866497933590410078387200⟩, ⟨.privateRow 6 21, 501340367531016973078479360⟩, ⟨.privateRow 6 22, 1070123802169095857954370600⟩, ⟨.privateRow 6 23, 1715944368958810602431820000⟩, ⟨.privateRow 6 24, 2139254772495014004856225200⟩, ⟨.privateRow 7 17, 29189256189424704943970400⟩, ⟨.privateRow 7 18, 82960218340955512926969600⟩, ⟨.privateRow 7 19, 177759449864946466016900400⟩, ⟨.privateRow 7 20, 390097814496568068405715200⟩, ⟨.privateRow 7 21, 648333376907090713165126800⟩, ⟨.privateRow 7 22, 904101043021714476165427200⟩, ⟨.privateRow 7 23, 917972322202111639156293600⟩, ⟨.privateRow 8 15, 9470088350310474654768000⟩, ⟨.privateRow 8 16, 30426477409384621794028800⟩, ⟨.privateRow 8 17, 66358261940389825973767200⟩, ⟨.privateRow 8 18, 147939581801503390756057200⟩, ⟨.privateRow 8 19, 256938771279972065246202240⟩, ⟨.privateRow 8 20, 371131998731865057327240600⟩, ⟨.privateRow 8 21, 434814524303690777414968800⟩, ⟨.privateRow 8 22, 305776933362686116312581600⟩, ⟨.privateRow 9 13, 2636350402038045040988640⟩, ⟨.privateRow 9 14, 10960184689301979448116800⟩, ⟨.privateRow 9 15, 25996919955207141713572800⟩, ⟨.privateRow 9 16, 59709561663109637892412800⟩, ⟨.privateRow 9 17, 108035378873783850376087200⟩, ⟨.privateRow 9 18, 163808089522692990947732160⟩, ⟨.privateRow 9 19, 204164412797459612053155600⟩, ⟨.privateRow 9 20, 93499302400592234709763200⟩, ⟨.privateRow 10 11, 597592618639959837585600⟩, ⟨.privateRow 10 12, 3761652396039747190581600⟩, ⟨.privateRow 10 13, 10417097185341522120244800⟩, ⟨.privateRow 10 14, 25778566378508267499575400⟩, ⟨.privateRow 10 15, 49146068893299554182406400⟩, ⟨.privateRow 10 16, 78611453339608050092431200⟩, ⟨.privateRow 10 17, 89314874897065997414114880⟩, ⟨.privateRow 11 9, 68734512219995380558800⟩, ⟨.privateRow 11 10, 1179279730319920744132800⟩, ⟨.privateRow 11 11, 4136567917239721993629600⟩, ⟨.privateRow 11 12, 11702918565456991259587200⟩, ⟨.privateRow 11 13, 24397627542088360308348600⟩, ⟨.privateRow 11 14, 41683464709414341436022400⟩, ⟨.privateRow 11 15, 14934134927798996321412000⟩, ⟨.privateRow 12 8, 257117990156279016164400⟩, ⟨.privateRow 12 9, 1557982276986561959332800⟩, ⟨.privateRow 12 10, 5419334430145413560502720⟩, ⟨.privateRow 12 11, 13037494391950728727227200⟩, ⟨.privateRow 12 12, 15457628081474516694556800⟩, ⟨.privateRow 13 6, 17624233902562918092000⟩, ⟨.privateRow 13 7, 454411497454413904805400⟩, ⟨.privateRow 13 8, 2449448071839835379913600⟩, ⟨.privateRow 13 9, 7272111392875511263121040⟩, ⟨.privateRow 13 10, 2092584038697637141456800⟩, ⟨.privateRow 14 5, 52369152167615528044800⟩, ⟨.privateRow 14 6, 900640314882637883353800⟩, ⟨.privateRow 14 7, 2970759177508371772723200⟩, ⟨.privateRow 15 4, 168017696537766485810400⟩, ⟨.privateRow 15 5, 976284645791415868307400⟩, ⟨.privateRow 16 3, 274938048879981522235200⟩, ⟨.hall 7 23, 128546902895434138524509100⟩, ⟨.hall 6 24, 853898926370794878671121024⟩, ⟨.hall 5 25, 2341441158774142638735522000⟩, ⟨.hall 4 26, 5118952731704884612456716800⟩, ⟨.hall 3 27, 9847672119486989595951343200⟩, ⟨.hall 2 28, 16988023854154301044294598400⟩, ⟨.assumptionRow 18, 109638268534877891008200⟩]
  caps := #[0, 1218668883213724610336150625, 0, 0, 2933148254993122289087250, 346204013309534333596500, 670156266365998094182500, 0, 0, 92023634716053878883045, 239257330024277916088920, 159130731702998277003600, 16710294818213911992000, 244696668451999365940800, 778248922905855824022600, 109638268534877891008200, 109638268534877891008200, 12144579736487681976893400, 2005147792884513468991800, 176232171784949280000000, 0] }

theorem case_51_31_18_checked :
    (Witness.linear .conditional case_51_31_18).check 51 31 18 = true := by
  change case_51_31_18.check 51 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_31_19 : Certificate := {
  objectiveScale := 9860797436490000000
  eta := 158427011453648357581761600
  rows := #[⟨.count 2, 30773088995754524747328000⟩, ⟨.count 3, 5641732982554996203676800⟩, ⟨.count 4, 1092813400067099680569600⟩, ⟨.count 5, 196369669455727093326000⟩, ⟨.count 6, 34817047115913591328800⟩, ⟨.count 7, 5637771305421456801600⟩, ⟨.count 8, 750140048954206310400⟩, ⟨.count 9, 70325629589456841600⟩, ⟨.path 9, 69338363460129363600⟩, ⟨.privateRow 2 29, 3061766935436182512739200⟩, ⟨.privateRow 3 26, 276589398848859879182400⟩, ⟨.privateRow 3 27, 960148006826010985382400⟩, ⟨.privateRow 4 24, 164790531535494744079200⟩, ⟨.privateRow 4 25, 344005631095671413668800⟩, ⟨.privateRow 4 26, 689255635137134049784800⟩, ⟨.privateRow 5 21, 10875565592552877816600⟩, ⟨.privateRow 5 22, 56827211036673846328560⟩, ⟨.privateRow 5 23, 121012094557416303341100⟩, ⟨.privateRow 5 24, 254931384006636459922800⟩, ⟨.privateRow 5 25, 375502234075621692039000⟩, ⟨.privateRow 6 19, 6764237193666863710800⟩, ⟨.privateRow 6 20, 19302594623404319627400⟩, ⟨.privateRow 6 21, 41615386658532167841360⟩, ⟨.privateRow 6 22, 89740875452851680057000⟩, ⟨.privateRow 6 23, 147005310044968496721600⟩, ⟨.privateRow 6 24, 188497105921129563558000⟩, ⟨.privateRow 7 16, 246093191903317558800⟩, ⟨.privateRow 7 17, 2614815745419893815800⟩, ⟨.privateRow 7 18, 6971805442225541174400⟩, ⟨.privateRow 7 19, 14546102991690689218800⟩, ⟨.privateRow 7 20, 32203863929752024189680⟩, ⟨.privateRow 7 21, 54807735234123747275400⟩, ⟨.privateRow 7 22, 79213589168741826598800⟩, ⟨.privateRow 7 23, 84435964840655717889600⟩, ⟨.privateRow 8 14, 176693144343510314520⟩, ⟨.privateRow 8 15, 917163419229166309200⟩, ⟨.privateRow 8 16, 2538315692994457876500⟩, ⟨.privateRow 8 17, 5369026935204603871200⟩, ⟨.privateRow 8 18, 11975868672171254650800⟩, ⟨.privateRow 8 19, 21336796017441205741440⟩, ⟨.privateRow 8 20, 32075812679207888190600⟩, ⟨.privateRow 8 21, 39779887726247344275600⟩, ⟨.privateRow 8 22, 31130812031599561881600⟩, ⟨.privateRow 9 11, 1465117283113684200⟩, ⟨.privateRow 9 12, 77961998459019074400⟩, ⟨.privateRow 9 13, 332288599810183576560⟩, ⟨.privateRow 9 14, 933768081771121396800⟩, ⟨.privateRow 9 15, 2070210721039635774600⟩, ⟨.privateRow 9 16, 4746421857370960166400⟩, ⟨.privateRow 9 17, 8777354852324847188400⟩, ⟨.privateRow 9 18, 13883451374785271479200⟩, ⟨.privateRow 9 19, 18347663736432667236600⟩, ⟨.privateRow 9 20, 14649219341426023754400⟩, ⟨.privateRow 10 9, 1229469048766728000⟩, ⟨.privateRow 10 10, 28369998300292248600⟩, ⟨.privateRow 10 11, 125539966870435353600⟩, ⟨.privateRow 10 12, 360898344574985337120⟩, ⟨.privateRow 10 13, 833784926571969372000⟩, ⟨.privateRow 10 14, 2008276217708011851600⟩, ⟨.privateRow 10 15, 3907639041538845412800⟩, ⟨.privateRow 10 16, 6501124962616265982000⟩, ⟨.privateRow 10 17, 9221927672846547378720⟩, ⟨.privateRow 10 18, 2483773372318543905600⟩, ⟨.privateRow 11 7, 456659932399070400⟩, ⟨.privateRow 11 8, 9958699295010496800⟩, ⟨.privateRow 11 9, 48482062823034640800⟩, ⟨.privateRow 11 10, 149369312433805027200⟩, ⟨.privateRow 11 11, 360418851645966313200⟩, ⟨.privateRow 11 12, 909793435320170200800⟩, ⟨.privateRow 11 13, 1895994956829390417000⟩, ⟨.privateRow 11 14, 3359190462727561862400⟩, ⟨.privateRow 11 15, 3321021303377872894800⟩, ⟨.privateRow 12 5, 260465294775766080⟩, ⟨.privateRow 12 6, 3627909462948170400⟩, ⟨.privateRow 12 7, 19534897108182456000⟩, ⟨.privateRow 12 8, 65930277740115789000⟩, ⟨.privateRow 12 9, 170486374762319616000⟩, ⟨.privateRow 12 10, 451842170112260207280⟩, ⟨.privateRow 12 11, 1007132473132962176000⟩, ⟨.privateRow 12 12, 1931024579143835775600⟩, ⟨.privateRow 12 13, 162697785915291026400⟩, ⟨.privateRow 13 3, 183139660389210525⟩, ⟨.privateRow 13 4, 1562791768654596480⟩, ⟨.privateRow 13 5, 8372098760649624000⟩, ⟨.privateRow 13 6, 31330969592738785200⟩, ⟨.privateRow 13 7, 88151223200673332700⟩, ⟨.privateRow 13 8, 251201017813855309200⟩, ⟨.privateRow 13 9, 598939945336874100960⟩, ⟨.privateRow 13 10, 422930522392150172400⟩, ⟨.privateRow 14 2, 680233024302781950⟩, ⟨.privateRow 14 3, 4353491355537804480⟩, ⟨.privateRow 14 4, 16325592583266766800⟩, ⟨.privateRow 14 5, 46465148121605413200⟩, ⟨.privateRow 14 6, 164616391881273231900⟩, ⟨.privateRow 14 7, 245873318602532821200⟩, ⟨.privateRow 15 0, 746922536489329200⟩, ⟨.privateRow 15 1, 2380815585059736825⟩, ⟨.privateRow 15 2, 11004658704276116880⟩, ⟨.privateRow 15 3, 32651185166533533600⟩, ⟨.privateRow 15 4, 102558209817957894000⟩, ⟨.privateRow 16 0, 11904077925298684125⟩, ⟨.privateRow 16 1, 30474439488764631360⟩, ⟨.privateRow 17 0, 10158146496254877120⟩, ⟨.hall 7 23, 16900616233144051808400⟩, ⟨.hall 6 24, 82192610745147087241056⟩, ⟨.hall 5 25, 212148982594861472160000⟩, ⟨.hall 4 26, 450976557115955411340800⟩, ⟨.hall 3 27, 854715515968542731302800⟩, ⟨.hall 2 28, 1467911716464152617257600⟩, ⟨.assumptionRow 19, 257845766110732800⟩]
  caps := #[0, 0, 0, 0, 467548691621370559200, 0, 0, 0, 5299609331834017200, 19632069629916023280, 9127861229647170360, 36863387472448681200, 641860904983137840, 0, 49102352700032521890, 35611488747597833070, 0, 244346563566327942720, 637857684178521206400, 108210926035279267200, 9860797436490000000] }

theorem case_51_31_19_checked :
    (Witness.linear .conditional case_51_31_19).check 51 31 19 = true := by
  change case_51_31_19.check 51 31 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_31_20 : Certificate := {
  objectiveScale := 1026185987015689500000
  eta := 26853971581697228921502950400
  rows := #[⟨.count 2, 3053171157407570412035222400⟩, ⟨.count 3, 401864011345821207452068800⟩, ⟨.count 4, 72307711384023193036358400⟩, ⟨.count 5, 14057799826262943652902000⟩, ⟨.count 6, 2549310337257227959615200⟩, ⟨.count 7, 420819170504183562711600⟩, ⟨.count 8, 63803129530177217980800⟩, ⟨.count 9, 5629687899721519233600⟩, ⟨.path 3, 47485166527118949396768000⟩, ⟨.path 9, 3330045540896443243875⟩, ⟨.path 10, 356027693263020979200⟩, ⟨.privateRow 2 29, 360806697493152167681424000⟩, ⟨.privateRow 3 28, 569963989947994784425483200⟩, ⟨.privateRow 5 21, 476725098952806982878600⟩, ⟨.privateRow 5 25, 109888692958614194680255200⟩, ⟨.privateRow 6 19, 286935362635012670779200⟩, ⟨.privateRow 6 20, 1063229111950183590812400⟩, ⟨.privateRow 7 17, 115986650255423264567250⟩, ⟨.privateRow 7 18, 408994911054938535069600⟩, ⟨.privateRow 7 19, 1028378663047145614604400⟩, ⟨.privateRow 8 15, 38730167680491562875600⟩, ⟨.privateRow 8 16, 138279209036909816175300⟩, ⟨.privateRow 8 17, 357753262008493686535200⟩, ⟨.privateRow 8 18, 962363870413506371210400⟩, ⟨.privateRow 8 19, 1045996011768258273602880⟩, ⟨.privateRow 8 20, 1987983539589161479365000⟩, ⟨.privateRow 8 22, 10700629275395677683265200⟩, ⟨.privateRow 9 12, 312760438873417735200⟩, ⟨.privateRow 9 13, 11040443492231646052560⟩, ⟨.privateRow 9 14, 45419765956395219989600⟩, ⟨.privateRow 9 15, 123579468409859182620900⟩, ⟨.privateRow 9 16, 348727889343860774748000⟩, ⟨.privateRow 9 17, 792430698625616068418400⟩, ⟨.privateRow 9 18, 1120182787869032960392320⟩, ⟨.privateRow 9 19, 1846928581657250080789800⟩, ⟨.privateRow 9 21, 6216270102828614195967600⟩, ⟨.privateRow 10 10, 127947452266398164400⟩, ⟨.privateRow 10 11, 2791580776721414496000⟩, ⟨.privateRow 10 12, 13204177073892290566080⟩, ⟨.privateRow 10 13, 39009756557666284790400⟩, ⟨.privateRow 10 14, 116048339205623135110800⟩, ⟨.privateRow 10 15, 276476166140219804959200⟩, ⟨.privateRow 10 16, 553585976805949391304000⟩, ⟨.privateRow 10 17, 751460976651009699154080⟩, ⟨.privateRow 10 18, 960501524163851020150800⟩, ⟨.privateRow 11 8, 39368446851199435200⟩, ⟨.privateRow 11 9, 746360138220655959000⟩, ⟨.privateRow 11 10, 4117581645664086381600⟩, ⟨.privateRow 11 11, 14330114653836594412800⟩, ⟨.privateRow 11 12, 47454288407248563640800⟩, ⟨.privateRow 11 13, 125324529494937002029800⟩, ⟨.privateRow 11 14, 277682527833017273366400⟩, ⟨.privateRow 11 16, 1843671608177890989738240⟩, ⟨.privateRow 11 19, 2955458199901531199475600⟩, ⟨.privateRow 12 6, 22340031348101266800⟩, ⟨.privateRow 12 7, 192467962383641683200⟩, ⟨.privateRow 12 8, 1224978385587552796200⟩, ⟨.privateRow 12 9, 4918868720463751653600⟩, ⟨.privateRow 12 10, 19015834683503798300160⟩, ⟨.privateRow 12 11, 56018869718216598793600⟩, ⟨.privateRow 12 12, 135464365087049056558500⟩, ⟨.privateRow 12 13, 277686589656898746324000⟩, ⟨.privateRow 12 14, 141471971850409288888800⟩, ⟨.privateRow 12 15, 1073206169950245616565280⟩, ⟨.privateRow 12 18, 2539614763652152009824000⟩, ⟨.privateRow 13 5, 67020094044303800400⟩, ⟨.privateRow 13 6, 360877429469328156000⟩, ⟨.privateRow 13 7, 1641992304085443109800⟩, ⟨.privateRow 13 8, 7506250532962025644800⟩, ⟨.privateRow 13 9, 26318790931198102417080⟩, ⟨.privateRow 13 10, 71570013762200425071600⟩, ⟨.privateRow 13 12, 632803727966316483376800⟩, ⟨.privateRow 13 13, 100865241536677219602000⟩, ⟨.privateRow 13 14, 759163413277446868650960⟩, ⟨.privateRow 13 18, 4788049558713152108176800⟩, ⟨.privateRow 14 4, 124465888939421343600⟩, ⟨.privateRow 14 5, 603180846398734203600⟩, ⟨.privateRow 14 6, 2976809177134493801100⟩, ⟨.privateRow 14 7, 12593684944506905038800⟩, ⟨.privateRow 14 8, 40687899094296837222840⟩, ⟨.privateRow 14 10, 241666081612003966267350⟩, ⟨.privateRow 14 11, 530224686881934923736000⟩, ⟨.privateRow 14 12, 523192364156857617822600⟩, ⟨.privateRow 14 13, 572941379965944328859520⟩, ⟨.privateRow 15 3, 290420407525316468400⟩, ⟨.privateRow 15 4, 1251041755493670940800⟩, ⟨.privateRow 15 5, 6098828558031645836400⟩, ⟨.privateRow 15 6, 24210501245519563774800⟩, ⟨.privateRow 15 7, 73592531266915193092560⟩, ⟨.privateRow 15 8, 22814136457822082573200⟩, ⟨.privateRow 15 9, 325524974284939096517850⟩, ⟨.privateRow 15 10, 823922696149322820850800⟩, ⟨.privateRow 15 11, 1059163226244829160254800⟩, ⟨.privateRow 15 16, 9760158635703310553518800⟩, ⟨.privateRow 16 2, 871261222575949405200⟩, ⟨.privateRow 16 3, 3283984608170886219600⟩, ⟨.privateRow 16 4, 15247071395079114591000⟩, ⟨.privateRow 16 5, 56552773901747988664800⟩, ⟨.privateRow 16 6, 162838722499444943831880⟩, ⟨.privateRow 16 7, 100969495016301692180400⟩, ⟨.privateRow 16 8, 543558095234570435169150⟩, ⟨.privateRow 16 9, 1541261102736854497798800⟩, ⟨.privateRow 16 10, 2415136108980531751214400⟩, ⟨.privateRow 16 13, 3197819107261259633552400⟩, ⟨.privateRow 17 0, 1626354282141772223040⟩, ⟨.privateRow 17 1, 1742522445151898810400⟩, ⟨.privateRow 17 2, 11259375799443038467200⟩, ⟨.privateRow 17 3, 46757685611575951412400⟩, ⟨.privateRow 17 4, 166331687946317613720000⟩, ⟨.privateRow 17 5, 463510970410405083566400⟩, ⟨.privateRow 17 6, 430983884767569639105600⟩, ⟨.privateRow 17 7, 1238062197280424104789200⟩, ⟨.privateRow 17 8, 3645356955257772311356800⟩, ⟨.privateRow 17 9, 6696513756718747128367200⟩, ⟨.privateRow 17 13, 26676276112830418888413600⟩, ⟨.privateRow 18 0, 19748587711721519851200⟩, ⟨.privateRow 18 1, 42535419686784811987200⟩, ⟨.privateRow 18 2, 207360170973075958437600⟩, ⟨.privateRow 18 3, 678633286820975863977600⟩, ⟨.privateRow 18 4, 1824769504563068434250880⟩, ⟨.privateRow 18 5, 2211841823712810223334400⟩, ⟨.privateRow 18 7, 20400291106208330006289600⟩, ⟨.privateRow 18 13, 391634242911149460169147200⟩, ⟨.privateRow 19 0, 669932860066860788798400⟩, ⟨.privateRow 19 1, 1140480940351917771406800⟩, ⟨.privateRow 19 2, 4184905268729351161195200⟩, ⟨.privateRow 19 3, 11197449232546101755630400⟩, ⟨.privateRow 19 4, 16312333449881975397091200⟩, ⟨.privateRow 19 5, 8864647309098997223207400⟩, ⟨.privateRow 19 6, 71450390341008458821641600⟩, ⟨.privateRow 19 9, 161740933358999247581328000⟩, ⟨.privateRow 20 0, 33488667612151767287672400⟩, ⟨.privateRow 20 8, 6116606643278308084013106000⟩, ⟨.hall 13 9, 46018075268923037280⟩, ⟨.hall 9 11, 19401641786786836500⟩, ⟨.hall 18 11, 2057650927348215279880800⟩, ⟨.hall 15 15, 40023562412082675801375⟩, ⟨.hall 8 19, 1761171514799009433120⟩, ⟨.hall 7 23, 1331831686360160659523850⟩, ⟨.hall 4 24, 225065191906101388185344⟩, ⟨.hall 5 25, 128082436828539214463442000⟩, ⟨.hall 3 27, 279210470215246778036228400⟩]
  caps := #[0, 15655123262772167249049975, 722985672977868900600, 8027811185575016335500, 115885194242819305654350, 10379481160665763221075, 4913518792020074636400, 0, 0, 7547627613704454190915, 585761916406012191720, 3341910366227605082400, 0, 4042317188564831872080, 0, 16321332524194653260305, 10535558783764557422880, 69380792076214075897440, 708928472849666034485520, 0, 0] }

theorem case_51_31_20_checked :
    (Witness.linear .conditional case_51_31_20).check 51 31 20 = true := by
  change case_51_31_20.check 51 31 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_32_1_checked :
    (Witness.rising).check 51 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_32_2_checked :
    (Witness.rising).check 51 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_32_3_checked :
    (Witness.rising).check 51 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_32_4_checked :
    (Witness.rising).check 51 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_32_5_checked :
    (Witness.rising).check 51 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_32_6_checked :
    (Witness.rising).check 51 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_32_7_checked :
    (Witness.rising).check 51 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_32_8_checked :
    (Witness.rising).check 51 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_32_9_checked :
    (Witness.rising).check 51 32 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_32_10_checked :
    (Witness.linear .positive case_51_32_10).check 51 32 10 = true := by
  change case_51_32_10.check 51 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_32_11_checked :
    (Witness.linear .positive case_51_32_11).check 51 32 11 = true := by
  change case_51_32_11.check 51 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_32_12_checked :
    (Witness.linear .positive case_51_32_12).check 51 32 12 = true := by
  change case_51_32_12.check 51 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_32_13_checked :
    (Witness.linear .positive case_51_32_13).check 51 32 13 = true := by
  change case_51_32_13.check 51 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_51_32_14_checked :
    (Witness.linear .positive case_51_32_14).check 51 32 14 = true := by
  change case_51_32_14.check 51 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_32_15 : Certificate := {
  objectiveScale := 279613917466884000000
  eta := 14250414265232796539941852800
  rows := #[⟨.count 2, 1869257401742978264431814400⟩, ⟨.count 3, 311500964242536962089996800⟩, ⟨.count 4, 55890267917910761473538400⟩, ⟨.count 5, 10641272169701636258796000⟩, ⟨.count 6, 1936546786125857238933600⟩, ⟨.count 7, 370166269487915956255200⟩, ⟨.count 8, 69355771625186867620800⟩, ⟨.count 9, 14516324293643762990400⟩, ⟨.count 10, 3958997534630117179200⟩, ⟨.count 11, 1612924921515973665600⟩, ⟨.path 2, 178263409398641512782636800⟩, ⟨.path 9, 2746538549459932106880⟩, ⟨.privateRow 2 30, 196407480617921629233777600⟩, ⟨.privateRow 3 28, 101548140133724186012510400⟩, ⟨.privateRow 5 22, 1442250582737558385551760⟩, ⟨.privateRow 5 23, 3029460104588162377676544⟩, ⟨.privateRow 5 26, 48864931483509710776967760⟩, ⟨.privateRow 6 19, 145278451859403056594400⟩, ⟨.privateRow 6 20, 674507097918657048474000⟩, ⟨.privateRow 6 21, 1341204676702014816291600⟩, ⟨.privateRow 6 24, 14604727940532567070833600⟩, ⟨.privateRow 7 17, 114786490247886792535200⟩, ⟨.privateRow 7 18, 269243252970202175464800⟩, ⟨.privateRow 7 19, 540313390290284688448800⟩, ⟨.privateRow 7 20, 909977678042422714124400⟩, ⟨.privateRow 7 21, 840149549833077597072960⟩, ⟨.privateRow 8 14, 6799944839573025340200⟩, ⟨.privateRow 8 15, 51795051542181704336580⟩, ⟨.privateRow 8 16, 119983692772771596568800⟩, ⟨.privateRow 8 17, 219282183470476357256025⟩, ⟨.privateRow 8 18, 368466937874175912571800⟩, ⟨.privateRow 8 19, 683913769325304416999100⟩, ⟨.privateRow 8 20, 693315777513641280158160⟩, ⟨.privateRow 8 21, 540481060419243300507150⟩, ⟨.privateRow 8 22, 540867490348356502531200⟩, ⟨.privateRow 9 12, 5571922456146090844800⟩, ⟨.privateRow 9 13, 23527375921286723304000⟩, ⟨.privateRow 9 14, 55191358223510226157440⟩, ⟨.privateRow 9 15, 99919884279368348395200⟩, ⟨.privateRow 9 16, 161255834767017458067600⟩, ⟨.privateRow 9 17, 299270887710372931953600⟩, ⟨.privateRow 9 18, 469678849494174210290400⟩, ⟨.privateRow 9 20, 743778333126343310796000⟩, ⟨.privateRow 10 10, 3400677369489972448800⟩, ⟨.privateRow 10 11, 11800012096272543703560⟩, ⟨.privateRow 10 12, 27413058686757023498400⟩, ⟨.privateRow 10 13, 50793938369304403409136⟩, ⟨.privateRow 10 14, 81936586013011462212480⟩, ⟨.privateRow 10 15, 146812825242533512062000⟩, ⟨.privateRow 10 16, 234900520388053619299200⟩, ⟨.privateRow 10 18, 831547842173709812319168⟩, ⟨.privateRow 10 20, 333567536723335317443040⟩, ⟨.privateRow 11 8, 1948078151960851310400⟩, ⟨.privateRow 11 9, 6699841981681736764800⟩, ⟨.privateRow 11 10, 15457197164528080962000⟩, ⟨.privateRow 11 11, 29299247747868678652800⟩, ⟨.privateRow 11 12, 48563703091462770731520⟩, ⟨.privateRow 11 14, 310414732622665113643200⟩, ⟨.privateRow 11 16, 304671742371812783167200⟩, ⟨.privateRow 11 18, 552280156080901346498400⟩, ⟨.privateRow 11 20, 878824137918726196797600⟩, ⟨.privateRow 12 6, 1142488486073814679800⟩, ⟨.privateRow 12 7, 4277131265091465881100⟩, ⟨.privateRow 12 8, 10189343013807641329800⟩, ⟨.privateRow 12 9, 19724727686039094618900⟩, ⟨.privateRow 12 10, 33614821659776087530800⟩, ⟨.privateRow 12 11, 61230662333050150280340⟩, ⟨.privateRow 12 13, 309227949796890576201750⟩, ⟨.privateRow 12 14, 74165744158993431945000⟩, ⟨.privateRow 12 15, 221205932465409471680100⟩, ⟨.privateRow 12 16, 138832512619487433266520⟩, ⟨.privateRow 12 18, 888452810935048827468000⟩, ⟨.privateRow 12 20, 1653449660169062503948200⟩, ⟨.privateRow 13 4, 734456883904595151300⟩, ⟨.privateRow 13 5, 3110640920066520640800⟩, ⟨.privateRow 13 6, 7974103310964175928400⟩, ⟨.privateRow 13 7, 16084938090942264852000⟩, ⟨.privateRow 13 8, 28110977203564112457600⟩, ⟨.privateRow 13 9, 51906856565150425238400⟩, ⟨.privateRow 13 10, 84160118226244197337200⟩, ⟨.privateRow 13 12, 9591142836871771975800⟩, ⟨.privateRow 13 14, 908479962043872167149200⟩, ⟨.privateRow 14 2, 528605646547251873600⟩, ⟨.privateRow 14 3, 2574199372508752613625⟩, ⟨.privateRow 14 4, 7338808392897680178480⟩, ⟨.privateRow 14 5, 15993467270236198056600⟩, ⟨.privateRow 14 7, 108147576062004079500900⟩, ⟨.privateRow 14 9, 271386138937359111906240⟩, ⟨.privateRow 14 10, 26376442863362410618800⟩, ⟨.privateRow 14 12, 55522471660552420009200⟩, ⟨.privateRow 14 13, 1006839580025605204078200⟩, ⟨.privateRow 14 18, 11348194121017494431090400⟩, ⟨.privateRow 15 1, 3453556890775378907520⟩, ⟨.privateRow 15 2, 7600908692644025899140⟩, ⟨.privateRow 15 3, 19430368887862429424928⟩, ⟨.privateRow 15 4, 38341529562894002565120⟩, ⟨.privateRow 15 6, 259654030282046493933840⟩, ⟨.privateRow 15 8, 586056270232829031395760⟩, ⟨.privateRow 15 10, 343089292367966548343940⟩, ⟨.privateRow 15 13, 2782456782107206170526560⟩, ⟨.privateRow 16 2, 169316793636139335546360⟩, ⟨.privateRow 16 3, 71890367930426254809600⟩, ⟨.privateRow 16 6, 1687687657366697035849800⟩, ⟨.privateRow 16 8, 1957889239105202533330200⟩, ⟨.privateRow 16 10, 514465445502112885981200⟩, ⟨.privateRow 16 12, 3478595178233500404599520⟩, ⟨.privateRow 16 14, 9291455626007955797397000⟩, ⟨.privateRow 17 1, 847108168780189369173120⟩, ⟨.privateRow 17 2, 332492951678221428494400⟩, ⟨.privateRow 17 5, 6076914586118910236102400⟩, ⟨.privateRow 17 6, 2038091930827584323852160⟩, ⟨.privateRow 17 8, 10274331750056752249872000⟩, ⟨.privateRow 18 0, 6344924056259537205737280⟩, ⟨.privateRow 18 2, 4524254404852306132008000⟩, ⟨.privateRow 18 4, 32340317712701829067036800⟩, ⟨.privateRow 18 5, 26163900321879215219163840⟩, ⟨.privateRow 18 6, 7921253503445115113280000⟩, ⟨.privateRow 18 7, 44601608007835651284712200⟩, ⟨.privateRow 18 14, 1161334976140088326757980800⟩, ⟨.privateRow 19 4, 1671424095494436514477646400⟩, ⟨.hall 16 3, 4118718996014004181800⟩, ⟨.hall 16 5, 19335897571030779538800⟩, ⟨.hall 11 8, 3329050405605724800⟩, ⟨.hall 12 8, 49074227105492302560⟩, ⟨.hall 16 9, 9893828098117302098760⟩, ⟨.hall 18 10, 3967669624467878388259200⟩, ⟨.hall 14 14, 1110928394676504574170⟩, ⟨.hall 7 17, 6887170401126819804⟩, ⟨.hall 9 17, 53810064309191954400⟩, ⟨.hall 8 18, 91657442145644575200⟩, ⟨.hall 10 19, 3656217059398665216000⟩, ⟨.hall 5 20, 122246938417552668720⟩, ⟨.hall 9 22, 27024461432040365092800⟩, ⟨.hall 4 25, 92986401824539942118400⟩, ⟨.hall 2 28, 2465695012951691521640640⟩, ⟨.hall 3 28, 153950124200252202853430400⟩]
  caps := #[0, 279027167115258574812800, 207696073390978274822720, 63457348614391456845120, 0, 6668547477167998277856, 4356403115421319522560, 152628097776838675992, 511728073961005661760, 0, 2193940863412069483656, 0, 5323136364846683300610, 279613917466884000000, 8774478699538538316330, 6878747729723075197992, 166042241839308366932400, 0, 6215047349997194527258440, 0] }

theorem case_51_32_15_checked :
    (Witness.linear .positive case_51_32_15).check 51 32 15 = true := by
  change case_51_32_15.check 51 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_32_16 : Certificate := {
  objectiveScale := 27589161600000
  eta := 516511813919064163200
  rows := #[⟨.count 2, 99983666046129465600⟩, ⟨.count 3, 19546613981409715200⟩, ⟨.count 4, 3790886728741912800⟩, ⟨.count 5, 797345179108077600⟩, ⟨.count 6, 161200946820513600⟩, ⟨.count 7, 35509299474448800⟩, ⟨.count 8, 7890955438766400⟩, ⟨.count 9, 1760791709476800⟩, ⟨.count 10, 586930569825600⟩, ⟨.count 11, 239119861780800⟩, ⟨.path 10, 78272618424000⟩, ⟨.privateRow 2 30, 9089424186011769600⟩, ⟨.privateRow 3 27, 1363620865115308800⟩, ⟨.privateRow 3 28, 2953130292992880000⟩, ⟨.privateRow 4 24, 150842786807873160⟩, ⟨.privateRow 4 25, 676985691179848050⟩, ⟨.privateRow 4 26, 1118692383358750200⟩, ⟨.privateRow 4 27, 1845317863345156200⟩, ⟨.privateRow 5 21, 1953950870551680⟩, ⟨.privateRow 5 22, 124653183946331040⟩, ⟨.privateRow 5 23, 253658349377072640⟩, ⟨.privateRow 5 24, 416624513177232360⟩, ⟨.privateRow 5 25, 694762758404114400⟩, ⟨.privateRow 5 26, 783822950924373360⟩, ⟨.privateRow 6 19, 11851378149510900⟩, ⟨.privateRow 6 20, 54098428729316400⟩, ⟨.privateRow 6 21, 100380525310065000⟩, ⟨.privateRow 6 22, 154917218452716720⟩, ⟨.privateRow 6 23, 256067481984514200⟩, ⟨.privateRow 6 24, 303898571003227200⟩, ⟨.privateRow 6 25, 266392336016406600⟩, ⟨.privateRow 7 16, 102479940763200⟩, ⟨.privateRow 7 17, 8858821545974400⟩, ⟨.privateRow 7 18, 22289387115996000⟩, ⟨.privateRow 7 19, 40779696427984800⟩, ⟨.privateRow 7 20, 61368404527029600⟩, ⟨.privateRow 7 21, 98483223073435200⟩, ⟨.privateRow 7 22, 118056891759206400⟩, ⟨.privateRow 7 23, 109209456873316800⟩, ⟨.privateRow 7 24, 24953865575839200⟩, ⟨.privateRow 8 14, 502695163971000⟩, ⟨.privateRow 8 15, 4363937477499600⟩, ⟨.privateRow 8 16, 9960006465008600⟩, ⟨.privateRow 8 17, 17347398722628975⟩, ⟨.privateRow 8 18, 26123844899552400⟩, ⟨.privateRow 8 19, 41422534389736500⟩, ⟨.privateRow 8 20, 50143435015433760⟩, ⟨.privateRow 8 21, 14907628882896750⟩, ⟨.privateRow 9 12, 425705814534000⟩, ⟨.privateRow 9 13, 2067102276220800⟩, ⟨.privateRow 9 14, 4743268530960960⟩, ⟨.privateRow 9 15, 8175966991192000⟩, ⟨.privateRow 9 16, 12173374781568000⟩, ⟨.privateRow 9 17, 19477399650508800⟩, ⟨.privateRow 9 18, 7423584799831200⟩, ⟨.privateRow 10 10, 264871231511040⟩, ⟨.privateRow 10 11, 1051583937604200⟩, ⟨.privateRow 10 12, 2440208308487040⟩, ⟨.privateRow 10 13, 4327634734847424⟩, ⟨.privateRow 10 14, 6521450775840000⟩, ⟨.privateRow 10 15, 2413751968407780⟩, ⟨.privateRow 11 8, 150614458394400⟩, ⟨.privateRow 11 9, 595291404153600⟩, ⟨.privateRow 11 10, 1405734945014400⟩, ⟨.privateRow 11 11, 2596723127107200⟩, ⟨.privateRow 11 12, 202164974051040⟩, ⟨.privateRow 12 6, 83691951623280⟩, ⟨.privateRow 12 7, 373624784032500⟩, ⟨.privateRow 12 8, 871407957835800⟩, ⟨.privateRow 13 4, 51239970381600⟩, ⟨.privateRow 13 5, 263031847958880⟩, ⟨.privateRow 13 6, 7319995768800⟩, ⟨.privateRow 14 2, 32652922302000⟩, ⟨.privateRow 14 3, 34693729945875⟩, ⟨.privateRow 15 0, 17269767795280⟩, ⟨.hall 5 26, 160781538174056800⟩, ⟨.hall 4 27, 626985087581853000⟩, ⟨.hall 3 28, 1611733832502393600⟩, ⟨.hall 2 29, 3427910749220717760⟩, ⟨.assumptionRow 16, 34652954381760⟩]
  caps := #[0, 0, 19032876271094400, 0, 0, 0, 1063029557947500, 52790206428960, 68160953721575, 71513249121600, 188607539433516, 0, 601073010115380, 34652954381760, 500459864307975, 0, 379184469618240, 27589161600000, 0, 0] }

theorem case_51_32_16_checked :
    (Witness.linear .conditional case_51_32_16).check 51 32 16 = true := by
  change case_51_32_16.check 51 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_32_17 : Certificate := {
  objectiveScale := 37829931150913059658500000
  eta := 872912058027244322332399676121600
  rows := #[⟨.count 2, 155422866433812627519111235593600⟩, ⟨.count 3, 27661388745479214435852052310400⟩, ⟨.count 4, 4805084858153828035982752958400⟩, ⟨.count 5, 894377108634471641734016061600⟩, ⟨.count 6, 163676856482125529206225161600⟩, ⟨.count 7, 31026656860622696470410813600⟩, ⟨.count 8, 7194587098115407877196710400⟩, ⟨.count 9, 2207430132376318325958081600⟩, ⟨.count 10, 735810044125439441986027200⟩, ⟨.count 11, 299774462421475328216529600⟩, ⟨.path 8, 405137146618861291716681600⟩, ⟨.path 9, 111665593907700875665983360⟩, ⟨.privateRow 2 30, 14641284519127276505423522193600⟩, ⟨.privateRow 3 27, 2083632363470867847990358406400⟩, ⟨.privateRow 3 28, 4645305069683181686043342681600⟩, ⟨.privateRow 4 24, 209272552216431926627959313760⟩, ⟨.privateRow 4 25, 986079990279591078856253819550⟩, ⟨.privateRow 4 26, 1732246731102495184099216293600⟩, ⟨.privateRow 4 27, 3023637643406408213639998744200⟩, ⟨.privateRow 5 22, 160559202072942185792773253760⟩, ⟨.privateRow 5 23, 357828784814018240278942722336⟩, ⟨.privateRow 5 24, 633760685366801528265770640600⟩, ⟨.privateRow 5 25, 1142490438698646055054563727200⟩, ⟨.privateRow 5 26, 1407426112345705592210195645520⟩, ⟨.privateRow 6 19, 10212405905081599239376506150⟩, ⟨.privateRow 6 20, 66409220195614585465110792000⟩, ⟨.privateRow 6 21, 136977301236812818872273183000⟩, ⟨.privateRow 6 22, 232543615484979025678368197280⟩, ⟨.privateRow 6 23, 421231297740776287536258887400⟩, ⟨.privateRow 6 24, 559461227981278842601436854800⟩, ⟨.privateRow 6 25, 564448547162636125591705903800⟩, ⟨.privateRow 7 17, 7151762174912339973165777600⟩, ⟨.privateRow 7 18, 25759191306645344274606079200⟩, ⟨.privateRow 7 19, 53913519389576557753227900000⟩, ⟨.privateRow 7 20, 90617537497691684929453804800⟩, ⟨.privateRow 7 21, 162019531954166801320228062240⟩, ⟨.privateRow 7 22, 220350289225985516703160855800⟩, ⟨.privateRow 7 23, 241725279019716784302600189600⟩, ⟨.privateRow 7 24, 165539740641458983031570738400⟩, ⟨.privateRow 8 15, 3436164775506160949681970540⟩, ⟨.privateRow 8 16, 10579540402957900124975023800⟩, ⟨.privateRow 8 17, 22066210819805785487938608525⟩, ⟨.privateRow 8 18, 37712697995701672987240197000⟩, ⟨.privateRow 8 19, 67430518140930606640705626900⟩, ⟨.privateRow 8 20, 93627058975787281885227607320⟩, ⟨.privateRow 8 21, 106644765006439848013030405200⟩, ⟨.privateRow 8 22, 22208291424390963898707901200⟩, ⟨.privateRow 9 13, 1424548065226019121690120000⟩, ⟨.privateRow 9 14, 4649229389918517363067268160⟩, ⟨.privateRow 9 15, 9759324165499141240827019200⟩, ⟨.privateRow 9 16, 16933850598831293824595098200⟩, ⟨.privateRow 9 17, 30833944706208890902271616000⟩, ⟨.privateRow 9 18, 44271237654880606426159303200⟩, ⟨.privateRow 9 19, 24069164110058819080076267520⟩, ⟨.privateRow 10 11, 553901449883316913272814920⟩, ⟨.privateRow 10 12, 2142768037589537284086582240⟩, ⟨.privateRow 10 13, 4760690985491593189649595984⟩, ⟨.privateRow 10 14, 8448189395514304704284016000⟩, ⟨.privateRow 10 15, 15694215066158852098026971820⟩, ⟨.privateRow 10 16, 14372822861916917100127064640⟩, ⟨.privateRow 11 9, 211728816115867189859227200⟩, ⟨.privateRow 11 10, 1021958394618665891647260000⟩, ⟨.privateRow 11 11, 2546844193134517664517292800⟩, ⟨.privateRow 11 12, 4785490509201006148620236160⟩, ⟨.privateRow 11 13, 6631374471747787563577776000⟩, ⟨.privateRow 12 7, 80296731005752320057999000⟩, ⟨.privateRow 12 8, 507310628713265940058742400⟩, ⟨.privateRow 12 9, 1473891106905587030397937200⟩, ⟨.privateRow 12 10, 2646872242062344659366403400⟩, ⟨.privateRow 13 5, 29977446242147532821652960⟩, ⟨.privateRow 13 6, 261537923847307556760339600⟩, ⟨.privateRow 13 7, 914147399142411028352604000⟩, ⟨.privateRow 13 8, 139181000409970688100531600⟩, ⟨.privateRow 14 3, 8698812525623168006283225⟩, ⟨.privateRow 14 4, 139181000409970688100531600⟩, ⟨.privateRow 14 5, 198830000585672411572188000⟩, ⟨.privateRow 15 2, 73070025215234611252779090⟩, ⟨.hall 6 25, 38510312190358812699816320400⟩, ⟨.hall 5 26, 403418707114233557435096408000⟩, ⟨.hall 4 27, 1222357136100567568242918777000⟩, ⟨.hall 3 28, 2828465086400474662342058457600⟩, ⟨.hall 2 29, 5666596693224825265899963491520⟩, ⟨.assumptionRow 17, 37664257669575575264658432⟩]
  caps := #[0, 0, 124039045588957853719709504160, 3069118601998692711406114176, 0, 3091911190352125438503790584, 0, 545010526261110168907053120, 30851669565844015561771098, 187251386736123976657512576, 83559483032244196407015600, 269838721721056093371198720, 118780593949390648666999608, 320199884225916114589161696, 124568054090303050586897109, 0, 3369348974651324575514123520, 491954778443207259954341568, 37829931150913059658500000, 0] }

theorem case_51_32_17_checked :
    (Witness.linear .conditional case_51_32_17).check 51 32 17 = true := by
  change case_51_32_17.check 51 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_32_18 : Certificate := {
  objectiveScale := 224335002511620000000
  eta := 10802125743501416730124118400
  rows := #[⟨.count 2, 1008771206566489646030150400⟩, ⟨.count 3, 138989166983785222152048000⟩, ⟨.count 4, 22954271517019074567535200⟩, ⟨.count 5, 3954405592636313559544800⟩, ⟨.count 6, 655167790495957276137600⟩, ⟨.count 7, 115194336790497982617600⟩, ⟨.count 8, 26398702181155787683200⟩, ⟨.count 9, 7854159326624862451200⟩, ⟨.count 10, 2945309747484323419200⟩, ⟨.count 11, 1199941008234353985600⟩, ⟨.path 2, 212116831124621464625584000⟩, ⟨.path 8, 3828728881587895084800⟩, ⟨.privateRow 2 30, 95467306615125203094336000⟩, ⟨.privateRow 3 27, 13997711841389817360019200⟩, ⟨.privateRow 3 28, 29139367443963052186310400⟩, ⟨.privateRow 4 24, 1274067364018031203060440⟩, ⟨.privateRow 4 25, 5810226856340263968961350⟩, ⟨.privateRow 4 26, 10740071994201585348112800⟩, ⟨.privateRow 4 27, 19643334290048433332768400⟩, ⟨.privateRow 5 22, 841838613343614944497440⟩, ⟨.privateRow 5 23, 2017916794727548410503808⟩, ⟨.privateRow 5 24, 3821032149571065114045360⟩, ⟨.privateRow 5 25, 7407555828099529647504960⟩, ⟨.privateRow 5 26, 9854815515376690695236400⟩, ⟨.privateRow 6 19, 37953491264912491017750⟩, ⟨.privateRow 6 20, 326788016007823199200800⟩, ⟨.privateRow 6 21, 739756489070477837158200⟩, ⟨.privateRow 6 22, 1368609858956095786190160⟩, ⟨.privateRow 6 23, 2699642279588252526227700⟩, ⟨.privateRow 6 24, 3958676811225147748136400⟩, ⟨.privateRow 6 25, 4456088071668294449988600⟩, ⟨.privateRow 7 17, 23484559732586642289600⟩, ⟨.privateRow 7 18, 117990627890044111101900⟩, ⟨.privateRow 7 19, 278104695102315123213600⟩, ⟨.privateRow 7 20, 517174574549006567793600⟩, ⟨.privateRow 7 21, 1022709721318139901926880⟩, ⟨.privateRow 7 22, 1553966460699496781137200⟩, ⟨.privateRow 7 23, 1943304462835536279679200⟩, ⟨.privateRow 7 24, 1666203800005417248576000⟩, ⟨.privateRow 8 15, 9479533965051396486240⟩, ⟨.privateRow 8 16, 43897841884573449973200⟩, ⟨.privateRow 8 17, 107600960097764961302475⟩, ⟨.privateRow 8 18, 206775548740384213590000⟩, ⟨.privateRow 8 19, 414304631863915595903100⟩, ⟨.privateRow 8 20, 650098039736167130548440⟩, ⟨.privateRow 8 21, 849145754108342062622250⟩, ⟨.privateRow 8 22, 838458779503754847438000⟩, ⟨.privateRow 9 13, 3014727822340856294400⟩, ⟨.privateRow 9 14, 16853716888382517343200⟩, ⟨.privateRow 9 15, 43912992654879439291200⟩, ⟨.privateRow 9 16, 87854771773340258286600⟩, ⟨.privateRow 9 17, 181549516180911999120000⟩, ⟨.privateRow 9 18, 296712685672494803712000⟩, ⟨.privateRow 9 19, 407609051942589736599360⟩, ⟨.privateRow 9 20, 183972773671567090610400⟩, ⟨.privateRow 10 11, 728146020905846623080⟩, ⟨.privateRow 10 12, 6461831082359545925760⟩, ⟨.privateRow 10 13, 19056154066223572522224⟩, ⟨.privateRow 10 14, 40361652095155543152000⟩, ⟨.privateRow 10 15, 86776188435256878738180⟩, ⟨.privateRow 10 16, 149972367284999382483360⟩, ⟨.privateRow 10 17, 159324894506971428515280⟩, ⟨.privateRow 11 9, 67129566894229593600⟩, ⟨.privateRow 11 10, 2372610629917927198800⟩, ⟨.privateRow 11 11, 8637591885720019185600⟩, ⟨.privateRow 11 12, 20224460266059020811840⟩, ⟨.privateRow 11 13, 45997738648983569448000⟩, ⟨.privateRow 11 14, 84759469399826640619200⟩, ⟨.privateRow 11 15, 6856805761339165632000⟩, ⟨.privateRow 12 8, 669197869976851261200⟩, ⟨.privateRow 12 9, 3962305204273856389950⟩, ⟨.privateRow 12 10, 10894918927036918573800⟩, ⟨.privateRow 12 11, 27298657937331553172400⟩, ⟨.privateRow 12 12, 16832505809954132298000⟩, ⟨.privateRow 13 6, 146931552028696406400⟩, ⟨.privateRow 13 7, 1602119038466747354400⟩, ⟨.privateRow 13 8, 6106842631192694391000⟩, ⟨.privateRow 13 9, 11757863515750910157600⟩, ⟨.privateRow 14 5, 557115468108807207600⟩, ⟨.privateRow 14 6, 3128417628610994319600⟩, ⟨.privateRow 14 7, 2274888161444296097700⟩, ⟨.privateRow 15 3, 103994887380310678752⟩, ⟨.privateRow 15 4, 1448500217082898739760⟩, ⟨.privateRow 16 2, 389980827676165045320⟩, ⟨.hall 6 25, 807388878397686753168000⟩, ⟨.hall 5 26, 3565869138395986162540800⟩, ⟨.hall 4 27, 9198254936210461401079800⟩, ⟨.hall 3 28, 19584030309012161337945600⟩, ⟨.hall 2 29, 37320645234172093283730240⟩, ⟨.assumptionRow 18, 160018045124037290190⟩]
  caps := #[0, 0, 0, 122005448119482043596480, 11032379378608781162970, 0, 2234430623977592747850, 722447108119991156760, 0, 334706095281898562040, 0, 228686175982363037400, 1755184056849038533410, 160018045124037290190, 2488957401953839356540, 11869573597353910646208, 160018045124037290190, 17949897594309277937340, 2756336987527022709810, 224335002511620000000] }

theorem case_51_32_18_checked :
    (Witness.linear .conditional case_51_32_18).check 51 32 18 = true := by
  change case_51_32_18.check 51 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_32_19 : Certificate := {
  objectiveScale := 72857645179536263046000000
  eta := 2318225465580550495374569631667200
  rows := #[⟨.count 2, 401343446230194755972197726012800⟩, ⟨.count 3, 67621924135186718637771881049600⟩, ⟨.count 4, 10855282945975253847712861610400⟩, ⟨.count 5, 1763423275194328618233735372000⟩, ⟨.count 6, 253031058745326710966766448800⟩, ⟨.count 7, 32825303635151548439709991200⟩, ⟨.count 8, 3297519086636228610381825600⟩, ⟨.count 9, 245270014708479813995342400⟩, ⟨.path 8, 1639303677462832908650323200⟩, ⟨.path 9, 115174963197492307956887040⟩, ⟨.privateRow 2 30, 40611345747624527139477914500800⟩, ⟨.privateRow 3 27, 5097364959014766480993869318400⟩, ⟨.privateRow 3 28, 12451132296675977757473556936000⟩, ⟨.privateRow 4 24, 437543310988824852181641190920⟩, ⟨.privateRow 4 25, 2379525371134115115446751065850⟩, ⟨.privateRow 4 26, 4526444495333066718405488695200⟩, ⟨.privateRow 4 27, 8551385050938906554912736902700⟩, ⟨.privateRow 5 22, 334823093319586152007178852400⟩, ⟨.privateRow 5 23, 825554887551749335882065196032⟩, ⟨.privateRow 5 24, 1601597526017655699179247280680⟩, ⟨.privateRow 5 25, 3195465867145877692812645039840⟩, ⟨.privateRow 5 26, 4413624376400744478631197780240⟩, ⟨.privateRow 6 19, 21277295437674268943368768350⟩, ⟨.privateRow 6 20, 131207917386485224396486861200⟩, ⟨.privateRow 6 21, 298334474378772169943489484600⟩, ⟨.privateRow 6 22, 563989249861283222320974149520⟩, ⟨.privateRow 6 23, 1150296173138305244478868541100⟩, ⟨.privateRow 6 24, 1762495401858262146979731828000⟩, ⟨.privateRow 6 25, 2090985759659194632678336492600⟩, ⟨.privateRow 7 16, 276220754659787980999516560⟩, ⟨.privateRow 7 17, 13632600552976616116513608000⟩, ⟨.privateRow 7 18, 47575813120908249634364407500⟩, ⟨.privateRow 7 19, 109900988631415975430239545600⟩, ⟨.privateRow 7 20, 208268307767319984278433939600⟩, ⟨.privateRow 7 21, 427512643351586272359995955840⟩, ⟨.privateRow 7 22, 683100350012136137197409092800⟩, ⟨.privateRow 7 23, 909858318372380689041198268800⟩, ⟨.privateRow 7 24, 857151544140204866155127725200⟩, ⟨.privateRow 8 14, 473507389506648529796563800⟩, ⟨.privateRow 8 15, 5733186593810715652141128600⟩, ⟨.privateRow 8 16, 18119700839698064283310233600⟩, ⟨.privateRow 8 17, 41701438108412419486121297325⟩, ⟨.privateRow 8 18, 81056873392606775354548057200⟩, ⟨.privateRow 8 19, 168922909574501347450014429600⟩, ⟨.privateRow 8 20, 280101763325066009802319845000⟩, ⟨.privateRow 8 21, 391749014673164227354963587900⟩, ⟨.privateRow 8 22, 433923534355085537593426596000⟩, ⟨.privateRow 8 23, 161035094032036277876316994500⟩, ⟨.privateRow 9 12, 254354089327312399698873600⟩, ⟨.privateRow 9 13, 2239637306024906584361510400⟩, ⟨.privateRow 9 14, 7238190656285804288573660160⟩, ⟨.privateRow 9 15, 16935743114376883946616667200⟩, ⟨.privateRow 9 16, 33547487567348739003140721600⟩, ⟨.privateRow 9 17, 71856327959911300427175153600⟩, ⟨.privateRow 9 18, 124342813382580433109935065600⟩, ⟨.privateRow 9 19, 183233052321548319708787128960⟩, ⟨.privateRow 9 20, 185941923372884196765580132800⟩, ⟨.privateRow 10 10, 101881390725060845813449920⟩, ⟨.privateRow 10 11, 887059886529001993949821680⟩, ⟨.privateRow 10 12, 3056956274230234772614676640⟩, ⟨.privateRow 10 13, 7478282748461549528717989776⟩, ⟨.privateRow 10 14, 15212191356697048019133347520⟩, ⟨.privateRow 10 15, 33319931498146982731267265040⟩, ⟨.privateRow 10 16, 60718344069760667096075549280⟩, ⟨.privateRow 10 17, 94911320025024738689064330720⟩, ⟨.privateRow 10 18, 34107248245361202934192314144⟩, ⟨.privateRow 11 8, 38931748366425367300848000⟩, ⟨.privateRow 11 9, 366856859606700576488760000⟩, ⟨.privateRow 11 10, 1389863416681385612640273600⟩, ⟨.privateRow 11 11, 3627023247810246946355366400⟩, ⟨.privateRow 11 12, 7706928906617565710875870080⟩, ⟨.privateRow 11 13, 17338470422478461912806550400⟩, ⟨.privateRow 11 14, 33091012817752401571538278800⟩, ⟨.privateRow 11 15, 33173742783031055477052580800⟩, ⟨.privateRow 12 6, 17486843641252727479297560⟩, ⟨.privateRow 12 7, 163270019711696384117931300⟩, ⟨.privateRow 12 8, 688904774218582725420678600⟩, ⟨.privateRow 12 9, 1957901957690260737414208950⟩, ⟨.privateRow 12 10, 4418266792734698871554987400⟩, ⟨.privateRow 12 11, 10353460495881704148278391060⟩, ⟨.privateRow 12 12, 18144682044899853893994944400⟩, ⟨.privateRow 13 4, 8029673100575232005799900⟩, ⟨.privateRow 13 5, 85649846406135808061865600⟩, ⟨.privateRow 13 6, 385424308827611136278395200⟩, ⟨.privateRow 13 7, 1195803624824126858709892800⟩, ⟨.privateRow 13 8, 2906741662408233986099563800⟩, ⟨.privateRow 13 9, 7194587098115407877196710400⟩, ⟨.privateRow 13 10, 860780956381664871021749280⟩, ⟨.privateRow 14 2, 8187117671174746358854800⟩, ⟨.privateRow 14 3, 52192875153739008037699350⟩, ⟨.privateRow 14 4, 250525800737947238580956880⟩, ⟨.privateRow 14 5, 845027502489107749181799000⟩, ⟨.privateRow 14 6, 2226896006559531009608505600⟩, ⟨.privateRow 14 7, 823487585758993237928145300⟩, ⟨.privateRow 15 1, 45847858958578579609586880⟩, ⟨.privateRow 15 2, 219210075645703833758337270⟩, ⟨.privateRow 15 3, 727452695476113463138778496⟩, ⟨.privateRow 15 4, 306198200901935513821169520⟩, ⟨.privateRow 16 0, 343858942189339347071901600⟩, ⟨.hall 6 25, 492508029296882430307742666400⟩, ⟨.hall 5 26, 1765732648830760724465921970400⟩, ⟨.hall 4 27, 4269168416075235901451656032600⟩, ⟨.hall 3 28, 8776465925162248203988969872000⟩, ⟨.hall 2 29, 16306371778165280500157961972480⟩, ⟨.assumptionRow 19, 18905998480665202289182800⟩]
  caps := #[0, 750211719188721370936226071200, 6863277597272217810146858400, 3621016493067520922846911440, 16739268115845378376307844810, 0, 795184861416803950837022850, 157168406697220275876158640, 0, 46854631539039116856635040, 487223557653944739893447280, 3073754144985552920171280, 82695552344747386282278810, 478123319014051265444126160, 743067134579767639254674490, 157602015170113867407954900, 0, 23798635949577823860073548000, 5364260698575644624782623600, 855385743673769954262817200] }

theorem case_51_32_19_checked :
    (Witness.linear .conditional case_51_32_19).check 51 32 19 = true := by
  change case_51_32_19.check 51 32 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_32_20 : Certificate := {
  objectiveScale := 129702621088844775972000000
  eta := 14306456229717008381177320921353600
  rows := #[⟨.count 2, 988982331681140197615214205004800⟩, ⟨.count 3, 108237166950822724956516610435200⟩, ⟨.count 4, 17361437991139743633660311784000⟩, ⟨.count 5, 2788352162213352765406050074400⟩, ⟨.count 6, 385809733136438747414673595200⟩, ⟨.count 7, 47214477831382364194103412000⟩, ⟨.count 8, 3597293549057703938598355200⟩, ⟨.path 2, 368208553294666895752784412169600⟩, ⟨.path 8, 2918455245385249036673606400⟩, ⟨.path 9, 86508067071244222496252160⟩, ⟨.privateRow 2 30, 103151493195842396013323185771200⟩, ⟨.privateRow 4 24, 988199021010832882582584413160⟩, ⟨.privateRow 5 22, 619438960424615544460225938960⟩, ⟨.privateRow 5 23, 1302400129436341710969534500160⟩, ⟨.privateRow 6 19, 30167481838861146645790224300⟩, ⟨.privateRow 6 21, 989507322414686607050729410200⟩, ⟨.privateRow 6 23, 3348277326862664843634488701200⟩, ⟨.privateRow 7 17, 19206978056575954957873360800⟩, ⟨.privateRow 7 18, 42300317893830322206553873200⟩, ⟨.privateRow 7 19, 175505712055430070983912100000⟩, ⟨.privateRow 7 20, 536157332271609391491270922800⟩, ⟨.privateRow 7 21, 483052286253645037097712704160⟩, ⟨.privateRow 7 22, 1932228416230021528947664736400⟩, ⟨.privateRow 7 23, 1746036356373883049197176655200⟩, ⟨.privateRow 7 24, 2075028122650651454938810158000⟩, ⟨.privateRow 7 25, 11533244305203021836426558767200⟩, ⟨.privateRow 8 14, 490540029416959627990684800⟩, ⟨.privateRow 8 15, 7745422672814868792794583540⟩, ⟨.privateRow 8 16, 21683686115153382074328974400⟩, ⟨.privateRow 8 17, 56263919415730650664639899300⟩, ⟨.privateRow 8 18, 139989320835428594789115456600⟩, ⟨.privateRow 8 19, 411084467499349386024929747100⟩, ⟨.privateRow 8 20, 470773310148245392314443497080⟩, ⟨.privateRow 8 21, 1119517097864950284328636557750⟩, ⟨.privateRow 8 22, 1295925001048037843880057460800⟩, ⟨.privateRow 8 23, 986557755829075305160598913600⟩, ⟨.privateRow 9 11, 6288974736114867025521600⟩, ⟨.privateRow 9 12, 292961406457350888938881200⟩, ⟨.privateRow 9 13, 2883780778996671752430086400⟩, ⟨.privateRow 9 15, 40905588008603133423000993600⟩, ⟨.privateRow 9 17, 213583464713046207549182212800⟩, ⟨.privateRow 9 18, 266840149890897788748377234400⟩, ⟨.privateRow 9 20, 1476791197727649333383789535600⟩, ⟨.privateRow 9 21, 475142522938038395223199416000⟩, ⟨.privateRow 9 22, 706255007353067624399588440800⟩, ⟨.privateRow 10 10, 130181777037577747428297120⟩, ⟨.privateRow 10 11, 1097583315820447167629157240⟩, ⟨.privateRow 10 12, 2013443848015975200343583520⟩, ⟨.privateRow 10 13, 6085149064917384185224444944⟩, ⟨.privateRow 10 14, 34198815717519035398083908640⟩, ⟨.privateRow 10 15, 12987047278814006151053380080⟩, ⟨.privateRow 10 16, 175469672379799437215325029280⟩, ⟨.privateRow 10 17, 225979528051657876624608720240⟩, ⟨.privateRow 10 18, 116464013784174554877548385216⟩, ⟨.privateRow 10 19, 654300686487443887800025036920⟩, ⟨.privateRow 11 8, 58397622549638050951272000⟩, ⟨.privateRow 11 9, 452806181000270425837555200⟩, ⟨.privateRow 11 10, 1294480633183643462753196000⟩, ⟨.privateRow 11 11, 2742564709922092465584283200⟩, ⟨.privateRow 11 12, 6998371086348624026000436480⟩, ⟨.privateRow 11 13, 38162197473715692540534571200⟩, ⟨.privateRow 11 14, 19785114519817371662290953600⟩, ⟨.privateRow 11 15, 152347717707495747321678393600⟩, ⟨.privateRow 11 16, 210250907052880196108229624000⟩, ⟨.privateRow 11 17, 160635508299740379512682915840⟩, ⟨.privateRow 11 18, 290317940743270606499153620800⟩, ⟨.privateRow 12 6, 29977446242147532821652960⟩, ⟨.privateRow 12 7, 216801173715531264156597300⟩, ⟨.privateRow 12 8, 735023922283425083607837000⟩, ⟨.privateRow 12 9, 1751807014775496449265344850⟩, ⟨.privateRow 12 10, 3525756461434397326183047000⟩, ⟨.privateRow 12 11, 9937523429271907130377956240⟩, ⟨.privateRow 12 12, 45465793467257091446173656000⟩, ⟨.privateRow 12 13, 28834556104165658132827440900⟩, ⟨.privateRow 12 14, 143490258307279395943644213000⟩, ⟨.privateRow 12 15, 216961767177542768796713298000⟩, ⟨.privateRow 12 19, 368553965643302573834209610100⟩, ⟨.privateRow 13 4, 12044509650862848008699850⟩, ⟨.privateRow 13 5, 128474769609203712092798400⟩, ⟨.privateRow 13 6, 454250078261113124899537200⟩, ⟨.privateRow 13 7, 1200744962116788539944231200⟩, ⟨.privateRow 13 9, 10651726353053980493512012800⟩, ⟨.privateRow 13 10, 11582000480269714645165775760⟩, ⟨.privateRow 13 11, 59162631405038309418733663200⟩, ⟨.privateRow 13 12, 43287967685201075743267260900⟩, ⟨.privateRow 13 13, 148526010437497291444424436000⟩, ⟨.privateRow 13 14, 251071818508786354357351273200⟩, ⟨.privateRow 14 2, 24561353013524239076564400⟩, ⟨.privateRow 14 3, 78289312730608512056549025⟩, ⟨.privateRow 14 4, 334034400983929651441275840⟩, ⟨.privateRow 14 5, 954384002811227575546502400⟩, ⟨.privateRow 14 6, 2216189775758764033600772400⟩, ⟨.privateRow 14 7, 139181000409970688100531600⟩, ⟨.privateRow 14 8, 265709182600853131828287600⟩, ⟨.privateRow 14 9, 61879872782272967929496349360⟩, ⟨.privateRow 14 10, 75900038890237348577489899200⟩, ⟨.privateRow 14 11, 93477439400346563395519535850⟩, ⟨.privateRow 14 12, 213722367629539275198944881200⟩, ⟨.privateRow 14 13, 395134860163906783517409212400⟩, ⟨.privateRow 14 16, 792635797334783068732527462000⟩, ⟨.privateRow 15 1, 68771788437867869414380320⟩, ⟨.privateRow 15 2, 292280100860938445011116360⟩, ⟨.privateRow 15 3, 935296322755003024035572352⟩, ⟨.privateRow 15 4, 2254732206641525147228611920⟩, ⟨.privateRow 15 5, 5665737339765883703292409440⟩, ⟨.privateRow 15 8, 122757642361594146904668871200⟩, ⟨.privateRow 15 10, 550071149820286153510920989520⟩, ⟨.privateRow 15 11, 214784119832666765876740365120⟩, ⟨.privateRow 15 14, 2434693240171617246942599278800⟩, ⟨.privateRow 15 16, 577545479301214367341965927360⟩, ⟨.privateRow 16 0, 515788413284009020607852400⟩, ⟨.privateRow 16 1, 1096050378228519168791686350⟩, ⟨.privateRow 16 2, 2922801008609384450111163600⟩, ⟨.privateRow 16 3, 7828931273060851205654902500⟩, ⟨.privateRow 16 4, 18548544862328785933397769000⟩, ⟨.privateRow 16 5, 1461400504304692225055581800⟩, ⟨.privateRow 16 7, 306455685752693959594155503460⟩, ⟨.privateRow 16 8, 122270508860159249496317010600⟩, ⟨.privateRow 16 9, 1098790504174090466713665565875⟩, ⟨.privateRow 16 10, 1198139642029232668513426278600⟩, ⟨.privateRow 16 13, 3519417764491775050990104869850⟩, ⟨.privateRow 16 14, 5315113634156165622527151006600⟩, ⟨.privateRow 17 0, 11691204034437537800444654400⟩, ⟨.privateRow 17 1, 10911790432141701947081677440⟩, ⟨.privateRow 17 2, 33403440098392965144127584000⟩, ⟨.privateRow 17 3, 73744517755682930741266281600⟩, ⟨.privateRow 17 8, 7926636335348650628701475683200⟩, ⟨.privateRow 18 0, 265000624780584190143412166400⟩, ⟨.privateRow 18 1, 141964620418170101862542232000⟩, ⟨.privateRow 18 2, 519808917838838219127462326400⟩, ⟨.privateRow 18 3, 115937773341505583187742822800⟩, ⟨.privateRow 18 10, 95121974264990695051977797129280⟩, ⟨.privateRow 19 2, 26831313259034149252020481848000⟩, ⟨.privateRow 19 7, 2044290534021649466820608140800⟩, ⟨.privateRow 19 9, 470800109985185872208786054826240⟩, ⟨.privateRow 19 12, 2085687417335587868523725455651200⟩, ⟨.hall 16 3, 4342447212791085468736585920⟩, ⟨.hall 17 3, 37129208417059872794818737600⟩, ⟨.hall 14 5, 42300107967736189520749800⟩, ⟨.hall 15 5, 174999640221360203420521350⟩, ⟨.hall 18 6, 119131150001261623940594880000⟩, ⟨.hall 12 8, 11550184693373279665404000⟩, ⟨.hall 18 8, 65522132500693893167327184000⟩, ⟨.hall 11 11, 2403738768140763665465700⟩, ⟨.hall 15 15, 37459133514751155121645280550⟩, ⟨.hall 14 17, 72095758212364816436075368800⟩, ⟨.hall 7 19, 32744562574409005395351276⟩, ⟨.hall 8 19, 31949423931142556861022000⟩, ⟨.hall 12 19, 34466568816909125861695490760⟩, ⟨.hall 5 26, 20492948642141679684505339214400⟩, ⟨.hall 4 27, 45489222268992769845337245486000⟩, ⟨.hall 3 28, 75173635651499958571493579884800⟩, ⟨.hall 2 29, 98262231668640617705177231301120⟩]
  caps := #[0, 0, 0, 62110518089291384058154448640, 5829815419405915195582604280, 0, 5261194277856099290740932900, 278870610683315540859460920, 298734602190894529339014720, 86508067071244222496252160, 18659973905411590159511040, 218856892692025765911258000, 0, 5939550482935080061063743840, 0, 1251233922297304578494429568, 14881345923924897622043038200, 428672813121262708394100344640, 0, 0] }

theorem case_51_32_20_checked :
    (Witness.linear .conditional case_51_32_20).check 51 32 20 = true := by
  change case_51_32_20.check 51 32 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_33_1_checked :
    (Witness.rising).check 51 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_33_2_checked :
    (Witness.rising).check 51 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_33_3_checked :
    (Witness.rising).check 51 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_33_4_checked :
    (Witness.rising).check 51 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_33_5_checked :
    (Witness.rising).check 51 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_33_6_checked :
    (Witness.rising).check 51 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_33_7_checked :
    (Witness.rising).check 51 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_33_8_checked :
    (Witness.rising).check 51 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_33_9_checked :
    (Witness.rising).check 51 33 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_33_10_checked :
    (Witness.linear .positive case_51_33_10).check 51 33 10 = true := by
  change case_51_33_10.check 51 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_33_11_checked :
    (Witness.linear .positive case_51_33_11).check 51 33 11 = true := by
  change case_51_33_11.check 51 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_33_12_checked :
    (Witness.linear .positive case_51_33_12).check 51 33 12 = true := by
  change case_51_33_12.check 51 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_51_33_13_checked :
    (Witness.linear .positive case_51_33_13).check 51 33 13 = true := by
  change case_51_33_13.check 51 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_51_33_14_checked :
    (Witness.linear .positive case_51_33_14).check 51 33 14 = true := by
  change case_51_33_14.check 51 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_15 : Certificate := {
  objectiveScale := 187
  eta := 354214720
  rows := #[⟨.assumptionRow 15, 776⟩]
  caps := #[0, 0, 100291500, 28705656, 8322418, 2450448, 735306, 225940, 71577, 23616, 8246, 3132, 1365, 45730, 14456, 2403, 187, 0, 0] }

theorem case_51_33_15_checked :
    (Witness.linear .conditional case_51_33_15).check 51 33 15 = true := by
  change case_51_33_15.check 51 33 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_16 : Certificate := {
  objectiveScale := 4953809077932000000
  eta := 706152704297845249010966400
  rows := #[⟨.count 2, 86227497962553066396076800⟩, ⟨.count 3, 10064604687293564691683400⟩, ⟨.count 4, 1181515958111285971574400⟩, ⟨.count 5, 146862102636381834702000⟩, ⟨.count 6, 26540193629196630583200⟩, ⟨.count 7, 7128301406402931955200⟩, ⟨.count 8, 2106089051891775350400⟩, ⟨.count 9, 656127743089360782240⟩, ⟨.count 10, 243010275218281771200⟩, ⟨.count 11, 111379709475045811800⟩, ⟨.path 5, 14794885632606772492800⟩, ⟨.path 6, 2447075646381452486400⟩, ⟨.privateRow 2 31, 8733951298195192378108800⟩, ⟨.privateRow 3 27, 56107528648054327694250⟩, ⟨.privateRow 3 30, 14986139909867413977690000⟩, ⟨.privateRow 4 25, 179254504429138729510920⟩, ⟨.privateRow 4 27, 1567149638883719587296600⟩, ⟨.privateRow 4 29, 6005170691998464998171160⟩, ⟨.privateRow 5 22, 15897748736091232810800⟩, ⟨.privateRow 5 23, 78229925657858605470840⟩, ⟨.privateRow 5 24, 128295423294633055148688⟩, ⟨.privateRow 6 20, 9880971369143349875400⟩, ⟨.privateRow 6 21, 29236037209551821048400⟩, ⟨.privateRow 6 24, 450554791907162104262100⟩, ⟨.privateRow 7 18, 4476403561758984055200⟩, ⟨.privateRow 7 19, 11436309455027025318750⟩, ⟨.privateRow 7 20, 17625270760602147442800⟩, ⟨.privateRow 7 21, 19459626383997289690200⟩, ⟨.privateRow 7 22, 33286621745970834040800⟩, ⟨.privateRow 7 23, 200563033990421779677000⟩, ⟨.privateRow 7 24, 99196890776751515147400⟩, ⟨.privateRow 8 16, 1865103862300312593960⟩, ⟨.privateRow 8 17, 4845579885949720317400⟩, ⟨.privateRow 8 18, 8945815756472997702300⟩, ⟨.privateRow 8 19, 13990448701852507684800⟩, ⟨.privateRow 8 20, 21145269086701879119000⟩, ⟨.privateRow 8 21, 32889415665167618717160⟩, ⟨.privateRow 8 23, 312939857055053715887400⟩, ⟨.privateRow 9 14, 771741722511391806720⟩, ⟨.privateRow 9 15, 2211393504486364117920⟩, ⟨.privateRow 9 16, 4309382213870863409280⟩, ⟨.privateRow 9 17, 7170828204566131265160⟩, ⟨.privateRow 9 19, 43358433327279652021440⟩, ⟨.privateRow 9 20, 13415787260550608982048⟩, ⟨.privateRow 9 22, 145687360107529013854080⟩, ⟨.privateRow 10 12, 330088957171499405880⟩, ⟨.privateRow 10 14, 4434937522733642324400⟩, ⟨.privateRow 10 15, 2818919192532068545920⟩, ⟨.privateRow 10 16, 7276132657160720032680⟩, ⟨.privateRow 10 18, 33806779454116632403440⟩, ⟨.privateRow 10 19, 18716651397312062017824⟩, ⟨.privateRow 10 20, 8738244479724048689400⟩, ⟨.privateRow 10 21, 55052627793617189255520⟩, ⟨.privateRow 11 10, 149544784749711859200⟩, ⟨.privateRow 11 11, 302919058345010957850⟩, ⟨.privateRow 11 12, 656311841782707965400⟩, ⟨.privateRow 11 13, 4605044715386439564240⟩, ⟨.privateRow 11 14, 3437020327740050051000⟩, ⟨.privateRow 11 15, 7670011811577018403500⟩, ⟨.privateRow 11 17, 29061666316208544318300⟩, ⟨.privateRow 11 19, 61881554041522043528700⟩, ⟨.privateRow 12 8, 73874297100795691500⟩, ⟨.privateRow 12 9, 255806145937193128200⟩, ⟨.privateRow 12 10, 474689714191266674100⟩, ⟨.privateRow 12 11, 896823634734135108000⟩, ⟨.privateRow 12 12, 6657324349194166808160⟩, ⟨.privateRow 12 13, 4527673586755433714600⟩, ⟨.privateRow 12 14, 9403629757107439253400⟩, ⟨.privateRow 12 16, 29929319074651595999400⟩, ⟨.privateRow 12 17, 14568465999335992183440⟩, ⟨.privateRow 12 18, 36047247402245183804700⟩, ⟨.privateRow 12 20, 109605589816979010654900⟩, ⟨.privateRow 13 6, 40308847238588008080⟩, ⟨.privateRow 13 7, 190936644814364248800⟩, ⟨.privateRow 13 8, 474893706333162362400⟩, ⟨.privateRow 13 9, 806176944771760161600⟩, ⟨.privateRow 13 10, 1666356172925360716800⟩, ⟨.privateRow 13 11, 11125241837850290230080⟩, ⟨.privateRow 13 12, 7938014214967550714000⟩, ⟨.privateRow 13 14, 32941117341068651114400⟩, ⟨.privateRow 14 4, 25856003985278492025⟩, ⟨.privateRow 14 5, 154446530472063525696⟩, ⟨.privateRow 14 6, 484615388981219736240⟩, ⟨.privateRow 14 7, 1050151546479003368400⟩, ⟨.privateRow 14 8, 1944371499692942600280⟩, ⟨.privateRow 14 9, 3678134094196707665520⟩, ⟨.privateRow 14 10, 22587805081539290633040⟩, ⟨.privateRow 14 11, 18745028311460567196080⟩, ⟨.privateRow 14 12, 4767847134885353929410⟩, ⟨.privateRow 14 13, 46133021053504893427920⟩, ⟨.privateRow 14 14, 32957786413234984501200⟩, ⟨.privateRow 15 2, 17034543802065830040⟩, ⟨.privateRow 15 3, 144793622317559555340⟩, ⟨.privateRow 15 4, 540562856652222339936⟩, ⟨.privateRow 15 5, 1447936223175595553400⟩, ⟨.privateRow 15 7, 12645309682400201166360⟩, ⟨.privateRow 15 9, 72657439678951384869612⟩, ⟨.privateRow 15 11, 132160378770352484136585⟩, ⟨.privateRow 15 14, 249160865284056482829072⟩, ⟨.privateRow 16 1, 170345438020658300400⟩, ⟨.privateRow 16 2, 723968111587797776700⟩, ⟨.privateRow 16 3, 2316697957080952885440⟩, ⟨.privateRow 16 4, 6722561036172407926500⟩, ⟨.privateRow 16 6, 723968111587797776700⟩, ⟨.privateRow 16 7, 3422394709324134944400⟩, ⟨.privateRow 16 9, 67731238884102858664600⟩, ⟨.privateRow 16 11, 1549498606829769470074200⟩, ⟨.privateRow 17 0, 2044145256247899604800⟩, ⟨.privateRow 17 1, 5067776781114584436900⟩, ⟨.privateRow 17 2, 16216885699566670198080⟩, ⟨.privateRow 17 3, 44679174886561234219200⟩, ⟨.privateRow 17 6, 13689578837296539777600⟩, ⟨.privateRow 17 8, 296022516738121757584000⟩, ⟨.privateRow 17 9, 194023453905529804155600⟩, ⟨.privateRow 17 11, 12676198988494613871499200⟩, ⟨.privateRow 17 15, 961429652188595447457600⟩, ⟨.privateRow 18 1, 511990248514890587682240⟩, ⟨.privateRow 18 6, 3879310729132055606669280⟩, ⟨.privateRow 18 8, 3766082116479724034393400⟩, ⟨.privateRow 18 9, 1716011272494962958715200⟩, ⟨.privateRow 18 11, 223030829026140415234194240⟩, ⟨.hall 16 3, 1124279890936344782640⟩, ⟨.hall 15 13, 260249974753783514500⟩, ⟨.hall 16 16, 209865579641451026092800⟩, ⟨.hall 10 17, 1408006279146521600⟩, ⟨.hall 6 19, 742864664294706800⟩, ⟨.hall 13 19, 703283308399574983080⟩, ⟨.hall 7 20, 2264957809482917010⟩, ⟨.hall 12 20, 981959887616730422400⟩, ⟨.hall 5 21, 2357259166365513410⟩, ⟨.hall 8 22, 621871512022358549952⟩, ⟨.hall 7 24, 1704966321964162811400⟩]
  caps := #[0, 50469497660100319257600, 0, 5955535621262797069500, 460620575489099625600, 405948575383259820912, 0, 0, 111065407667798490940, 6123959374184458560, 0, 62464356875350952900, 24769045389660000000, 1013876139090497728320, 4953809077932000000, 3605183524139247022830, 3808350496327375953240, 229589393666698691826200, 0] }

theorem case_51_33_16_checked :
    (Witness.linear .positive case_51_33_16).check 51 33 16 = true := by
  change case_51_33_16.check 51 33 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_17 : Certificate := {
  objectiveScale := 2933009970183216000000
  eta := 177341659461826494979252708800
  rows := #[⟨.count 2, 26663499839723444585900812800⟩, ⟨.count 3, 3993145223241645504073240200⟩, ⟨.count 4, 609363047381150647728823680⟩, ⟨.count 5, 91139324526731197312596000⟩, ⟨.count 6, 13511564195571338342846400⟩, ⟨.count 7, 2230682768136777556602000⟩, ⟨.count 8, 540771580154370316752000⟩, ⟨.count 9, 194677768855573314030720⟩, ⟨.count 10, 54077158015437031675200⟩, ⟨.path 7, 217994131544046493053600⟩, ⟨.path 8, 45849010166682229584000⟩, ⟨.privateRow 2 31, 2242579742900173703570544000⟩, ⟨.privateRow 3 27, 19815898590281707294481100⟩, ⟨.privateRow 3 28, 424672428325061629497985200⟩, ⟨.privateRow 3 29, 711922405450852557189528300⟩, ⟨.privateRow 4 25, 75822394410814493667273048⟩, ⟨.privateRow 4 26, 169401767216920448944283550⟩, ⟨.privateRow 4 27, 266854101015793658232345480⟩, ⟨.privateRow 4 28, 428796712909705627113747120⟩, ⟨.privateRow 5 22, 9697855397692869393695280⟩, ⟨.privateRow 5 23, 34973565038086042281873960⟩, ⟨.privateRow 5 24, 62074165395842739115088112⟩, ⟨.privateRow 5 25, 96980526689580787685812380⟩, ⟨.privateRow 5 26, 161583578191230906588958080⟩, ⟨.privateRow 5 27, 177942626644160334631835160⟩, ⟨.privateRow 6 19, 783689607430063649515200⟩, ⟨.privateRow 6 20, 5943176232250128775803900⟩, ⟨.privateRow 6 21, 13805953622114559326506800⟩, ⟨.privateRow 6 22, 23988691673216933247585000⟩, ⟨.privateRow 6 23, 36311266545708382854706080⟩, ⟨.privateRow 6 24, 60233745889140938736722100⟩, ⟨.privateRow 6 25, 71353522449987843366100800⟩, ⟨.privateRow 6 26, 60132834049629989275828200⟩, ⟨.privateRow 7 17, 659644761434732791738020⟩, ⟨.privateRow 7 18, 2735832093407963162012400⟩, ⟨.privateRow 7 19, 5724091317522409551494775⟩, ⟨.privateRow 7 20, 9757340271509850128538000⟩, ⟨.privateRow 7 21, 14660542859476710274778700⟩, ⟨.privateRow 7 22, 23963906309126524608067200⟩, ⟨.privateRow 7 23, 29182110641732200677975450⟩, ⟨.privateRow 7 24, 23861224086466260244350600⟩, ⟨.privateRow 8 15, 369322408719064273145400⟩, ⟨.privateRow 8 16, 1247154456731016543009300⟩, ⟨.privateRow 8 17, 2568665005733259004572000⟩, ⟨.privateRow 8 18, 4329552463610927348495700⟩, ⟨.privateRow 8 19, 6478636662956554384087800⟩, ⟨.privateRow 8 20, 10570957784559284754341700⟩, ⟨.privateRow 8 21, 13258367216434774240967160⟩, ⟨.privateRow 8 22, 850025327555150841644550⟩, ⟨.privateRow 9 13, 183411694269023932431720⟩, ⟨.privateRow 9 14, 610580275047025394005440⟩, ⟨.privateRow 9 15, 1270272441782615874050448⟩, ⟨.privateRow 9 16, 2157678604815937563840480⟩, ⟨.privateRow 9 17, 3235165978273520419968840⟩, ⟨.privateRow 9 18, 5286428461423365825048480⟩, ⟨.privateRow 9 19, 1175276900868831488407680⟩, ⟨.privateRow 10 11, 90267256071921814411680⟩, ⟨.privateRow 10 12, 328068091960317992162880⟩, ⟨.privateRow 10 13, 709885601584464306718080⟩, ⟨.privateRow 10 14, 1233499974332118692511312⟩, ⟨.privateRow 10 15, 1880683384314643434926400⟩, ⟨.privateRow 10 16, 404226756165391811772120⟩, ⟨.privateRow 11 9, 46351849727517455721600⟩, ⟨.privateRow 11 10, 194989752459508527675000⟩, ⟨.privateRow 11 11, 455149413296595016599600⟩, ⟨.privateRow 11 12, 774901093834842010709400⟩, ⟨.privateRow 12 7, 26201670609860561775960⟩, ⟨.privateRow 12 8, 128985058021514348511000⟩, ⟨.privateRow 12 9, 285984970273945840590000⟩, ⟨.privateRow 13 5, 17261235705820302521325⟩, ⟨.privateRow 13 6, 97725149842182635813040⟩, ⟨.privateRow 13 7, 6069885083365381106400⟩, ⟨.privateRow 14 3, 12996695119676463074880⟩, ⟨.privateRow 14 4, 17261235705820302521325⟩, ⟨.privateRow 15 1, 10740324439177077124380⟩, ⟨.hall 5 27, 22370561474743112067637200⟩, ⟨.hall 4 28, 114848881720226493950990880⟩, ⟨.hall 3 29, 318117669563985847347011220⟩, ⟨.hall 2 30, 726905158043504579778038400⟩, ⟨.assumptionRow 17, 3079038018798704584160⟩]
  caps := #[0, 75891364641036172421827200, 0, 1710317445729222466197320, 218749177136871558693824, 192072125673071005190688, 190317181778752928218800, 38275336012445729876850, 8078814490398217311760, 4132864913602264777952, 14525397691953956364480, 25557160481653517901800, 61386365130721729369920, 41950270539505986703980, 276113868086704182948105, 0, 299763578151023430653440, 40916111533949535415840, 2933009970183216000000] }

theorem case_51_33_17_checked :
    (Witness.linear .conditional case_51_33_17).check 51 33 17 = true := by
  change case_51_33_17.check 51 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_18 : Certificate := {
  objectiveScale := 3735288869143293000000
  eta := 254862327286374972582078460800
  rows := #[⟨.count 2, 35386290275055772557766060800⟩, ⟨.count 3, 4791893474747135867197487400⟩, ⟨.count 4, 640044648104804367934148640⟩, ⟨.count 5, 80126172242227644453320400⟩, ⟨.count 6, 10265714889794022880821600⟩, ⟨.count 7, 1731566366953208678692800⟩, ⟨.count 8, 472245372805420548734400⟩, ⟨.count 9, 141673611841626164620320⟩, ⟨.count 10, 52471708089491172081600⟩, ⟨.path 6, 819816724374678337507200⟩, ⟨.path 7, 314071785254236988815200⟩, ⟨.privateRow 2 31, 3113933516570853607182552000⟩, ⟨.privateRow 3 27, 26496572844315245302080450⟩, ⟨.privateRow 3 28, 549002736455664551627767200⟩, ⟨.privateRow 3 29, 969352496799993133440713100⟩, ⟨.privateRow 4 25, 88690829315343348522645216⟩, ⟨.privateRow 4 26, 213942239496931237288656660⟩, ⟨.privateRow 4 27, 359665574042480922660924480⟩, ⟨.privateRow 4 28, 614345317275273829127883000⟩, ⟨.privateRow 5 22, 9440570508807136704342480⟩, ⟨.privateRow 5 23, 39527125102771162397541000⟩, ⟨.privateRow 5 24, 76535233419331823598221760⟩, ⟨.privateRow 5 25, 129354191777000949757918920⟩, ⟨.privateRow 5 26, 233196639080891291649763920⟩, ⟨.privateRow 5 27, 282156678106493267039802840⟩, ⟨.privateRow 6 19, 435182023440621228772000⟩, ⟨.privateRow 6 20, 5576055979295749376028600⟩, ⟨.privateRow 6 21, 15030467239675471251782400⟩, ⟨.privateRow 6 22, 28835389916345794524342600⟩, ⟨.privateRow 6 23, 47886055600384568578611600⟩, ⟨.privateRow 6 24, 87047284238710261285119300⟩, ⟨.privateRow 6 25, 115568312403912764948151600⟩, ⟨.privateRow 6 26, 113572201175341704943547400⟩, ⟨.privateRow 7 17, 304054808482855095365700⟩, ⟨.privateRow 7 18, 2434728899565159822024400⟩, ⟨.privateRow 7 19, 5952259386401654833006500⟩, ⟨.privateRow 7 20, 11389171639781521368783000⟩, ⟨.privateRow 7 21, 18975081437862245104008600⟩, ⟨.privateRow 7 22, 34425188485855458254964000⟩, ⟨.privateRow 7 23, 47450587272981157467452250⟩, ⟨.privateRow 7 24, 51864535467312774233227200⟩, ⟨.privateRow 7 25, 26973268942360399477018200⟩, ⟨.privateRow 8 15, 129390461993404367519400⟩, ⟨.privateRow 8 16, 1015327551531654179778960⟩, ⟨.privateRow 8 17, 2528116046700623277098200⟩, ⟨.privateRow 8 18, 4851173386961238518856675⟩, ⟨.privateRow 8 19, 8133114753871131672648000⟩, ⟨.privateRow 8 20, 14860424995177979026609800⟩, ⟨.privateRow 8 21, 21220870544092467269101080⟩, ⟨.privateRow 8 22, 22838310945951032648516400⟩, ⟨.privateRow 9 13, 42851894939751123866640⟩, ⟨.privateRow 9 14, 430268006333827611069120⟩, ⟨.privateRow 9 15, 1158575314615965079561728⟩, ⟨.privateRow 9 16, 2283102320871638109683840⟩, ⟨.privateRow 9 17, 3867164886195499382413920⟩, ⟨.privateRow 9 18, 7129405937702150538115680⟩, ⟨.privateRow 9 19, 10625520888121962346524000⟩, ⟨.privateRow 9 20, 3323557990388370839648544⟩, ⟨.privateRow 10 11, 10494341617898234416320⟩, ⟨.privateRow 10 12, 187586356419930940191720⟩, ⟨.privateRow 10 13, 576711773456316609515040⟩, ⟨.privateRow 10 14, 1204225700653822399272720⟩, ⟨.privateRow 10 15, 2094787190728242014324320⟩, ⟨.privateRow 10 16, 3906518667262617761475120⟩, ⟨.privateRow 10 17, 2643824491880505199025760⟩, ⟨.privateRow 11 10, 83752918681303216976400⟩, ⟨.privateRow 11 11, 311550766781353834234500⟩, ⟨.privateRow 11 12, 716715830949640782296400⟩, ⟨.privateRow 11 13, 1314416287641753860644080⟩, ⟨.privateRow 11 14, 1314707797131139922711200⟩, ⟨.privateRow 12 8, 35338089121494054667200⟩, ⟨.privateRow 12 9, 181560759172291569331800⟩, ⟨.privateRow 12 10, 480990657487002410748000⟩, ⟨.privateRow 12 11, 556574903663531361008400⟩, ⟨.privateRow 13 6, 16491108256697225511360⟩, ⟨.privateRow 13 7, 110431528504668920835000⟩, ⟨.privateRow 13 8, 267980509171329914559600⟩, ⟨.privateRow 14 4, 10049269093924871795985⟩, ⟨.privateRow 14 5, 75034542567972376076688⟩, ⟨.privateRow 14 6, 30626343905294847378240⟩, ⟨.privateRow 15 2, 11034491554113584717160⟩, ⟨.privateRow 15 3, 23448294552491367523965⟩, ⟨.hall 5 27, 57089419185963676441000500⟩, ⟨.hall 4 28, 200600968458444769559504160⟩, ⟨.hall 3 29, 490632115216329374071443660⟩, ⟨.hall 2 30, 1043706282429344792395737600⟩, ⟨.assumptionRow 18, 2954022964109223061440⟩]
  caps := #[0, 33033703930077678923793600, 11900370417468432114482400, 0, 383527304497726452238560, 0, 32825568525828692315300, 89036870501389432358100, 18090394015631200623360, 28107269769648240414152, 0, 110072770204769522982160, 11876970458370553926720, 92150863170665265632160, 112829234594804072416269, 0, 1680468412084953847688640, 344159697929264126078400, 49340021203896878938560] }

theorem case_51_33_18_checked :
    (Witness.linear .conditional case_51_33_18).check 51 33 18 = true := by
  change case_51_33_18.check 51 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_19 : Certificate := {
  objectiveScale := 14126183359669180800000
  eta := 1148283618734708460051987139200
  rows := #[⟨.count 2, 159883603303835538944206790400⟩, ⟨.count 3, 21542417171264869171617124800⟩, ⟨.count 4, 2788283601825853495009726080⟩, ⟨.count 5, 326400260170679835933592800⟩, ⟨.count 6, 31415561229008214599140800⟩, ⟨.count 7, 2308755155937611571590400⟩, ⟨.count 8, 209886832357964688326400⟩, ⟨.count 9, 94449074561084109746880⟩, ⟨.path 6, 2707146579166028365766400⟩, ⟨.path 7, 1710722148100083673027200⟩, ⟨.privateRow 2 31, 14541694349673046483662134400⟩, ⟨.privateRow 3 27, 83006962715819441034836100⟩, ⟨.privateRow 3 28, 2474889329033622204262759200⟩, ⟨.privateRow 3 29, 4483313918436349470582108000⟩, ⟨.privateRow 4 25, 379749819936508195324117968⟩, ⟨.privateRow 4 26, 952375931543989383353362440⟩, ⟨.privateRow 4 27, 1649009130502139584912013280⟩, ⟨.privateRow 4 28, 2910027147142388675194152360⟩, ⟨.privateRow 5 22, 42953447327176023447981600⟩, ⟨.privateRow 5 23, 167505683599359285260720640⟩, ⟨.privateRow 5 24, 333989468190411899113920672⟩, ⟨.privateRow 5 25, 584653076859090474594679320⟩, ⟨.privateRow 5 26, 1099720548170025614708715840⟩, ⟨.privateRow 5 27, 1401055698049547059300500720⟩, ⟨.privateRow 6 19, 3545588275189903484942400⟩, ⟨.privateRow 6 20, 23577131335746814598272500⟩, ⟨.privateRow 6 21, 62465962203760990633387200⟩, ⟨.privateRow 6 22, 122831271331966501350446400⟩, ⟨.privateRow 6 23, 212323018804976778458760000⟩, ⟨.privateRow 6 24, 405794639484016541004846600⟩, ⟨.privateRow 6 25, 574426528351406107624447200⟩, ⟨.privateRow 6 26, 611758274667504451875788400⟩, ⟨.privateRow 7 16, 84329530858110812274000⟩, ⟨.privateRow 7 17, 2385026531624836239580440⟩, ⟨.privateRow 7 18, 9983991790408778611669200⟩, ⟨.privateRow 7 19, 24061557640787295597668700⟩, ⟨.privateRow 7 20, 47223466429356555053601600⟩, ⟨.privateRow 7 21, 82084491347710439982794400⟩, ⟨.privateRow 7 22, 157667363265217998807735120⟩, ⟨.privateRow 7 23, 233472865144190970177079200⟩, ⟨.privateRow 7 24, 280060245969360632246671200⟩, ⟨.privateRow 7 25, 215239883577880100221081800⟩, ⟨.privateRow 8 14, 45912744578304775571400⟩, ⟨.privateRow 8 15, 1154377577968805785795200⟩, ⟨.privateRow 8 16, 4181995134732446414903520⟩, ⟨.privateRow 8 17, 9924440566148483075100400⟩, ⟨.privateRow 8 18, 19506357482268343221334800⟩, ⟨.privateRow 8 19, 34172199893281125818142000⟩, ⟨.privateRow 8 20, 66343915915650400700673000⟩, ⟨.privateRow 8 21, 102277853408036192621454720⟩, ⟨.privateRow 8 22, 130877557902213355964530800⟩, ⟨.privateRow 8 23, 58191124271245709838494400⟩, ⟨.privateRow 9 12, 8072570475306334166400⟩, ⟨.privateRow 9 13, 525591609363069907017360⟩, ⟨.privateRow 9 14, 1867992807985885726104960⟩, ⟨.privateRow 9 15, 4478985002518966448885376⟩, ⟨.privateRow 9 16, 8894537540147525791965440⟩, ⟨.privateRow 9 17, 15706094023886945083324920⟩, ⟨.privateRow 9 18, 30788899115253720029709120⟩, ⟨.privateRow 9 19, 49552532062779146541460320⟩, ⟨.privateRow 9 20, 56640060580120350791762304⟩, ⟨.privateRow 10 11, 237333571974006224492160⟩, ⟨.privateRow 10 12, 920003948502411883830720⟩, ⟨.privateRow 10 13, 2269639882634536334220480⟩, ⟨.privateRow 10 14, 4590225023668687733698368⟩, ⟨.privateRow 10 15, 8206575145196419313562240⟩, ⟨.privateRow 10 16, 16204575250737111218100120⟩, ⟨.privateRow 10 17, 27132370657246035209508480⟩, ⟨.privateRow 10 18, 5981774722201993617302400⟩, ⟨.privateRow 11 9, 112439374477481083032000⟩, ⟨.privateRow 11 10, 505544726016059177170800⟩, ⟨.privateRow 11 11, 1323817468674454362308700⟩, ⟨.privateRow 11 12, 2753572135878070825827600⟩, ⟨.privateRow 11 13, 5016295293355356051000960⟩, ⟨.privateRow 11 14, 9990030201260347040202400⟩, ⟨.privateRow 11 15, 4940539264801153171308150⟩, ⟨.privateRow 12 7, 61841655962614595667600⟩, ⟨.privateRow 12 8, 313625540953259735171400⟩, ⟨.privateRow 12 9, 900668220173463854851200⟩, ⟨.privateRow 12 10, 1966908224366492001094500⟩, ⟨.privateRow 12 11, 3686137493286754838732400⟩, ⟨.privateRow 12 12, 1894416060988093780617480⟩, ⟨.privateRow 13 5, 38651034976634122292250⟩, ⟨.privateRow 13 6, 228126997550978286240480⟩, ⟨.privateRow 13 7, 721485986230503616122000⟩, ⟨.privateRow 13 8, 1696681330256349163188000⟩, ⟨.privateRow 13 9, 309208279813072978338000⟩, ⟨.privateRow 14 3, 31527118726038813477600⟩, ⟨.privateRow 14 4, 200985381878497435919700⟩, ⟨.privateRow 14 5, 693176250389840045660832⟩, ⟨.privateRow 14 6, 30626343905294847378240⟩, ⟨.privateRow 15 1, 41685856982206875598160⟩, ⟨.privateRow 15 2, 220689831082271694343200⟩, ⟨.privateRow 15 3, 23448294552491367523965⟩, ⟨.privateRow 16 0, 104214642455517188995400⟩, ⟨.hall 6 26, 18240998077268986662843200⟩, ⟨.hall 5 27, 346135110524654203212946200⟩, ⟨.hall 4 28, 1051259815357488841377873600⟩, ⟨.hall 3 29, 2421552275024888506934913480⟩, ⟨.hall 2 30, 4970675374760905532615692800⟩, ⟨.assumptionRow 19, 5921254621143330929460⟩]
  caps := #[0, 124511754362253389914091400, 15230770662259824237902700, 1927548075282015687801300, 685017320945310952208064, 438313991829821003040768, 0, 0, 40519819024662627329680, 0, 160827357872954463144552, 77582126967601112318140, 0, 23321798994937829906520, 957902501691557461046436, 990170020674653896187110, 0, 5599710197655533135336160, 1188458937674219638987560] }

theorem case_51_33_19_checked :
    (Witness.linear .conditional case_51_33_19).check 51 33 19 = true := by
  change case_51_33_19.check 51 33 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_20 : Certificate := {
  objectiveScale := 3694031563954160000000
  eta := 458100405192161931246775728000
  rows := #[⟨.count 2, 61751008064326169628014976000⟩, ⟨.count 3, 7956687098598941718002988000⟩, ⟨.count 4, 959231910312498472231982400⟩, ⟨.count 5, 101919038810644506214764000⟩, ⟨.count 6, 8498240464539941211096000⟩, ⟨.count 7, 418927346843518228716000⟩, ⟨.path 6, 2062657049119108329888000⟩, ⟨.path 7, 429397623021746852928000⟩, ⟨.privateRow 2 31, 6041490911279324215723008000⟩, ⟨.privateRow 3 30, 10658838306964108212925974000⟩, ⟨.privateRow 4 25, 129688735186837416457707840⟩, ⟨.privateRow 4 26, 289866304464701350404318300⟩, ⟨.privateRow 5 22, 14989619448486647478914400⟩, ⟨.privateRow 5 23, 57079848453493271801194800⟩, ⟨.privateRow 5 24, 115363015838491354057444320⟩, ⟨.privateRow 5 27, 1660580125476638427975513600⟩, ⟨.privateRow 6 19, 1416373410756656868516000⟩, ⟨.privateRow 6 20, 7829951601718138322430000⟩, ⟨.privateRow 6 21, 20915019037310069935692000⟩, ⟨.privateRow 6 22, 42404756997160567373364000⟩, ⟨.privateRow 6 23, 77070662466440396420066400⟩, ⟨.privateRow 6 24, 92852254089674075978982000⟩, ⟨.privateRow 6 25, 152496203891466722843556000⟩, ⟨.privateRow 6 26, 479911199191167525153372000⟩, ⟨.privateRow 6 27, 640360373032235006751600000⟩, ⟨.privateRow 7 16, 99744606391313863980000⟩, ⟨.privateRow 7 17, 858801061029212368867800⟩, ⟨.privateRow 7 18, 3240591434313352647528000⟩, ⟨.privateRow 7 19, 7824964371398572629231000⟩, ⟨.privateRow 7 20, 15715475198425722940506000⟩, ⟨.privateRow 7 21, 28227723608741823506340000⟩, ⟨.privateRow 7 22, 57075858669237619246635600⟩, ⟨.privateRow 7 23, 67843787652211907432596500⟩, ⟨.privateRow 7 24, 83891863615521047198112000⟩, ⟨.privateRow 7 25, 100098699744003028197129000⟩, ⟨.privateRow 8 12, 453384574505972109000⟩, ⟨.privateRow 8 13, 3906082488051452016000⟩, ⟨.privateRow 8 14, 67176481122634867483500⟩, ⟨.privateRow 8 15, 413156997713442220056000⟩, ⟨.privateRow 8 16, 1345645417133725219512000⟩, ⟨.privateRow 8 17, 3163113048136665413790000⟩, ⟨.privateRow 8 18, 6357698542153620391479750⟩, ⟨.privateRow 8 19, 11629314336078184595850000⟩, ⟨.privateRow 8 21, 88700883571667592960134400⟩, ⟨.privateRow 8 22, 27784086802587729797683500⟩, ⟨.privateRow 8 23, 61863720678573886310238000⟩, ⟨.privateRow 9 10, 338527148964459174720⟩, ⟨.privateRow 9 11, 2538953617233443810400⟩, ⟨.privateRow 9 12, 37498391885293939353600⟩, ⟨.privateRow 9 13, 198461541080414191179600⟩, ⟨.privateRow 9 14, 604270960901559626875200⟩, ⟨.privateRow 9 15, 1405056931776987804675360⟩, ⟨.privateRow 9 16, 2818802727044063394835200⟩, ⟨.privateRow 9 17, 5147728458940807325586000⟩, ⟨.privateRow 9 18, 10720913002598018878257600⟩, ⟨.privateRow 9 19, 4326376963765788252921600⟩, ⟨.privateRow 9 20, 50358621625655017912997760⟩, ⟨.privateRow 9 21, 34622441001403856520519600⟩, ⟨.privateRow 10 8, 317369202154180476300⟩, ⟨.privateRow 10 9, 1692635744822295873600⟩, ⟨.privateRow 10 10, 21762459576286661232000⟩, ⟨.privateRow 10 11, 104683010679778914028800⟩, ⟨.privateRow 10 12, 307636546621452275026800⟩, ⟨.privateRow 10 13, 711368640755770347604800⟩, ⟨.privateRow 10 14, 1426384142161748732682720⟩, ⟨.privateRow 10 16, 10609652428014253322709000⟩, ⟨.privateRow 10 17, 7154771293363844657707200⟩, ⟨.privateRow 10 18, 6102798177956787772264800⟩, ⟨.privateRow 10 19, 31016872969570642965370560⟩, ⟨.privateRow 10 20, 12604635232755431796730800⟩, ⟨.privateRow 11 7, 1190134508078176786125⟩, ⟨.privateRow 11 8, 14387403830989514925600⟩, ⟨.privateRow 11 9, 63473840430836095260000⟩, ⟨.privateRow 11 10, 184562397560431107756000⟩, ⟨.privateRow 11 11, 424745782216344870781500⟩, ⟨.privateRow 11 12, 851126496686211277350000⟩, ⟨.privateRow 11 13, 1553204875342559251012200⟩, ⟨.privateRow 11 14, 264474335128483730250000⟩, ⟨.privateRow 11 15, 11071424617148585915725500⟩, ⟨.privateRow 11 16, 8246158641114620718492000⟩, ⟨.privateRow 11 17, 7026554135693555745282000⟩, ⟨.privateRow 11 20, 35486108390199432990024000⟩, ⟨.privateRow 12 5, 1173465957544868988000⟩, ⟨.privateRow 12 6, 11221268219022809697750⟩, ⟨.privateRow 12 7, 46547482982613136524000⟩, ⟨.privateRow 12 8, 133942757154050045916000⟩, ⟨.privateRow 12 9, 309208279813072978338000⟩, ⟨.privateRow 12 10, 621741379839189752142000⟩, ⟨.privateRow 12 11, 1134368205413942216718000⟩, ⟨.privateRow 12 14, 20826673814506334799024000⟩, ⟨.privateRow 12 15, 6519022489146584681550000⟩, ⟨.privateRow 12 17, 15785581407489332113474800⟩, ⟨.privateRow 13 3, 1108273404347931822000⟩, ⟨.privateRow 13 4, 10561193617903820892000⟩, ⟨.privateRow 13 5, 42391457716308392191500⟩, ⟨.privateRow 13 6, 121023455754794154962400⟩, ⟨.privateRow 13 7, 282134743792573500972000⟩, ⟨.privateRow 13 8, 570846055039519344624000⟩, ⟨.privateRow 13 9, 1047318367108795571790000⟩, ⟨.privateRow 13 10, 2109145040601782251068000⟩, ⟨.privateRow 13 11, 55856979579135763828800⟩, ⟨.privateRow 13 13, 28013272705000498698783000⟩, ⟨.privateRow 13 15, 37181464442468764696278000⟩, ⟨.privateRow 14 1, 2729852385446484698400⟩, ⟨.privateRow 14 2, 11526043405218490948800⟩, ⟨.privateRow 14 3, 48816183833866549900800⟩, ⟨.privateRow 14 4, 139393087431861124912050⟩, ⟨.privateRow 14 5, 331950050070292539325440⟩, ⟨.privateRow 14 6, 681683138537207893257600⟩, ⟨.privateRow 14 7, 1260771824786207240707200⟩, ⟨.privateRow 14 8, 2519881239465892583681400⟩, ⟨.privateRow 14 9, 4649186780814040394529600⟩, ⟨.privateRow 14 10, 539418831364225376403840⟩, ⟨.privateRow 14 13, 15745398580343117099700000⟩, ⟨.privateRow 15 1, 121023455754794154962400⟩, ⟨.privateRow 15 2, 192213723845849540234400⟩, ⟨.privateRow 15 3, 521913652942549793275350⟩, ⟨.privateRow 15 4, 1077108756217667979165360⟩, ⟨.privateRow 15 5, 2035787416446715963831800⟩, ⟨.privateRow 15 7, 15778433044031287953222900⟩, ⟨.privateRow 15 10, 24829979005691934126452400⟩, ⟨.privateRow 15 12, 16649369698838110175541600⟩, ⟨.privateRow 15 15, 38213156154576254429377800⟩, ⟨.privateRow 16 0, 907675918160956162218000⟩, ⟨.privateRow 16 2, 4198001121494422250258250⟩, ⟨.privateRow 16 3, 3812238856276015881315600⟩, ⟨.privateRow 16 6, 20120149519234528262499000⟩, ⟨.privateRow 16 7, 98854159086984134757924000⟩, ⟨.privateRow 16 10, 118792085789315137730280750⟩, ⟨.privateRow 16 14, 165650855064374499604785000⟩, ⟨.privateRow 17 0, 17085664341853292465280000⟩, ⟨.privateRow 17 4, 170363787716364079677840000⟩, ⟨.privateRow 17 6, 573651180277724294521776000⟩, ⟨.privateRow 17 8, 395343288798994239543840000⟩, ⟨.privateRow 17 10, 785269337197535788341744000⟩, ⟨.privateRow 18 7, 28762434494684378868363984000⟩, ⟨.hall 13 7, 210760662111677127450⟩, ⟨.hall 8 13, 2591536219117189344⟩, ⟨.hall 11 14, 94014524084004123600⟩, ⟨.hall 16 15, 28511702370467681801436000⟩, ⟨.hall 17 15, 1350167928264422291299275000⟩, ⟨.hall 12 16, 1249344207431228937600⟩, ⟨.hall 6 17, 63635760326208174720⟩, ⟨.hall 15 17, 24204691150958830992480000⟩, ⟨.hall 4 26, 1390544271047968747110400⟩, ⟨.hall 3 29, 3141466352755069277436498000⟩]
  caps := #[0, 3558488076824759905008000, 8101970778486782852928000, 1165286091910064590284000, 658663638174426111956820, 69664831831638141396480, 52194639456829028075200, 80493746708863850182740, 211579468102786984200, 127571496701986185375296, 0, 37799638805730789059250, 2758343491871837877150, 233001270973570897208400, 73450903201986576084390, 1924784881094993978200140, 20022262900609327107750, 0, 18470157819770800000000] }

theorem case_51_33_20_checked :
    (Witness.linear .conditional case_51_33_20).check 51 33 20 = true := by
  change case_51_33_20.check 51 33 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_33_21 : Certificate := {
  objectiveScale := 343531820542776096000000
  eta := 42682070218153075472225861798400
  rows := #[⟨.count 2, 5160903915266875138798551916800⟩, ⟨.count 3, 576729653921758993441554568800⟩, ⟨.count 4, 56608721429304965983662600000⟩, ⟨.count 5, 4431654191894160194149586400⟩, ⟨.count 6, 223946590269777887407896000⟩, ⟨.path 5, 710096482108700790373670400⟩, ⟨.path 6, 192886063527740911148620800⟩, ⟨.path 7, 1935017182085838870801600⟩, ⟨.privateRow 2 31, 576956088807476213305489219200⟩, ⟨.privateRow 3 30, 971179224841155996415715565600⟩, ⟨.privateRow 4 25, 8423377748680578938368994880⟩, ⟨.privateRow 5 22, 798529556161950867100154880⟩, ⟨.privateRow 5 23, 3539932046712537206178367920⟩, ⟨.privateRow 5 24, 6600253440248791576746581088⟩, ⟨.privateRow 5 25, 14019554209977584147039640480⟩, ⟨.privateRow 6 19, 59166136194731441858382400⟩, ⟨.privateRow 6 20, 389107200593739079371219300⟩, ⟨.privateRow 6 21, 1220686652359392484696372800⟩, ⟨.privateRow 6 22, 2691091526408497613684883600⟩, ⟨.privateRow 6 23, 5466287438940534033974065920⟩, ⟨.privateRow 6 24, 12951577803935487821756652000⟩, ⟨.privateRow 7 15, 207357953953498043896200⟩, ⟨.privateRow 7 16, 2601399785962066368879600⟩, ⟨.privateRow 7 17, 32347840816745694847807200⟩, ⟨.privateRow 7 18, 150818351842177577260502800⟩, ⟨.privateRow 7 19, 425965076908973356673768850⟩, ⟨.privateRow 7 20, 973278990728018818607649600⟩, ⟨.privateRow 7 21, 2006602920408000570783527400⟩, ⟨.privateRow 7 22, 4774292475006920361883667280⟩, ⟨.privateRow 7 23, 9402957458952299047539033300⟩, ⟨.privateRow 7 24, 10437155254295370541471330800⟩, ⟨.privateRow 8 13, 182707008378606668048400⟩, ⟨.privateRow 8 14, 1517483208477872048513100⟩, ⟨.privateRow 8 15, 14395097629829616270480000⟩, ⟨.privateRow 8 17, 273586827731372873673956000⟩, ⟨.privateRow 8 18, 302441001202720237842784800⟩, ⟨.privateRow 8 19, 742869295399950083078313600⟩, ⟨.privateRow 8 20, 1765030904052175349644454400⟩, ⟨.privateRow 8 21, 3460336753551332647946793840⟩, ⟨.privateRow 8 22, 5888296691609767248419505900⟩, ⟨.privateRow 8 23, 6564764314936881253350150000⟩, ⟨.privateRow 9 11, 90483470816071873700160⟩, ⟨.privateRow 9 12, 828271771316350228486080⟩, ⟨.privateRow 9 13, 6439407006410448344994720⟩, ⟨.privateRow 9 14, 6564164519202305019338880⟩, ⟨.privateRow 9 15, 64098490726105315329193344⟩, ⟨.privateRow 9 16, 198249284558013475277050560⟩, ⟨.privateRow 9 18, 1268216326958063381781442560⟩, ⟨.privateRow 9 19, 1234677120442239407263249920⟩, ⟨.privateRow 9 20, 2718992104634633375940327936⟩, ⟨.privateRow 9 21, 4277244148946533541680263360⟩, ⟨.privateRow 9 22, 5037938688097249783877508480⟩, ⟨.privateRow 9 23, 2891399309927576724088612800⟩, ⟨.privateRow 10 9, 84451239428333748786816⟩, ⟨.privateRow 10 10, 497659089488395305350880⟩, ⟨.privateRow 10 11, 3166921478562515579505600⟩, ⟨.privateRow 10 12, 5436548538198985078151280⟩, ⟨.privateRow 10 13, 19922815119684188918344320⟩, ⟨.privateRow 10 14, 72712517147795357705448576⟩, ⟨.privateRow 10 15, 178543995358068933893460160⟩, ⟨.privateRow 10 16, 62309180090717494026772680⟩, ⟨.privateRow 10 17, 1123804707535612671355987200⟩, ⟨.privateRow 10 18, 1226759816745833118314485920⟩, ⟨.privateRow 10 19, 2215071558965765896929396864⟩, ⟨.privateRow 10 20, 3379263563700132249111450480⟩, ⟨.privateRow 10 21, 4080261632979945072635015040⟩, ⟨.privateRow 10 22, 3287264494747891171526812800⟩, ⟨.privateRow 11 7, 49483148102539305929775⟩, ⟨.privateRow 11 8, 316692147856251557950560⟩, ⟨.privateRow 11 9, 1809669416321437474003200⟩, ⟨.privateRow 11 11, 17550023193700607169760200⟩, ⟨.privateRow 11 12, 24327714994412051497111200⟩, ⟨.privateRow 11 13, 79331383037991015266615280⟩, ⟨.privateRow 11 14, 219221342349383022892443200⟩, ⟨.privateRow 11 15, 105300139162203643018561200⟩, ⟨.privateRow 11 16, 1077431928742375836084655200⟩, ⟨.privateRow 11 17, 1351351785914946752071535400⟩, ⟨.privateRow 11 18, 2070058224462388308543835440⟩, ⟨.privateRow 11 19, 3081414598641327658858948800⟩, ⟨.privateRow 11 20, 3928830004280014119341655600⟩, ⟨.privateRow 11 22, 11450004605742775077702496800⟩, ⟨.privateRow 12 5, 73185160218881662551600⟩, ⟨.privateRow 12 6, 233277698197685299383225⟩, ⟨.privateRow 12 7, 1244147723720988263377200⟩, ⟨.privateRow 12 10, 38775937389304134208589400⟩, ⟨.privateRow 12 12, 168333187019449712034935160⟩, ⟨.privateRow 12 13, 270533010591330447936575600⟩, ⟨.privateRow 12 14, 179779346077682804058005400⟩, ⟨.privateRow 12 15, 1156701912282313088294116800⟩, ⟨.privateRow 12 16, 1690174682674962555797926200⟩, ⟨.privateRow 12 17, 2320833163829131506503828880⟩, ⟨.privateRow 12 18, 3239449635638523190768384500⟩, ⟨.privateRow 12 20, 9021315144700885897748077200⟩, ⟨.privateRow 13 4, 292740640875526650206400⟩, ⟨.privateRow 13 5, 1088629258255864730455050⟩, ⟨.privateRow 13 6, 1492977268465185916052640⟩, ⟨.privateRow 13 8, 6507849631771323223819200⟩, ⟨.privateRow 13 9, 65110397541398385783406800⟩, ⟨.privateRow 13 10, 1357252062241078105502400⟩, ⟨.privateRow 13 12, 1005271360766558516808777600⟩, ⟨.privateRow 13 14, 1469160726325384140725133600⟩, ⟨.privateRow 13 15, 2236977607250336897552205600⟩, ⟨.privateRow 13 17, 6692270605895195868705958800⟩, ⟨.privateRow 14 2, 359420453519396609420080⟩, ⟨.privateRow 14 3, 1141688499414553935804960⟩, ⟨.privateRow 14 4, 2830436071465248299183130⟩, ⟨.privateRow 14 5, 2587827265339655587824576⟩, ⟨.privateRow 14 6, 1386336035003386922048880⟩, ⟨.privateRow 14 7, 12441477237209882633772000⟩, ⟨.privateRow 14 8, 159582681362612094582515520⟩, ⟨.privateRow 14 11, 1807884881202564945383002400⟩, ⟨.privateRow 14 12, 608948103375237705509970540⟩, ⟨.privateRow 14 13, 2095215860901785434856540640⟩, ⟨.privateRow 14 14, 4297949783184944655445316640⟩, ⟨.privateRow 14 15, 3119625768366954811122526368⟩, ⟨.privateRow 14 16, 6497063828043372810182076120⟩, ⟨.privateRow 15 1, 2515943174635776265940560⟩, ⟨.privateRow 15 2, 3995909747950938775317360⟩, ⟨.privateRow 15 3, 8491308214395744897549390⟩, ⟨.privateRow 15 4, 7547829523907328797821680⟩, ⟨.privateRow 15 5, 3234784081674569484780720⟩, ⟨.privateRow 15 7, 558539384769142331038804320⟩, ⟨.privateRow 15 10, 4065764170211414445759944960⟩, ⟨.privateRow 15 12, 10445117799727184866356944880⟩, ⟨.privateRow 15 13, 6525098623417885745716842360⟩, ⟨.privateRow 15 14, 11330801681289681991289906016⟩, ⟨.privateRow 15 15, 12567136157305702448373097200⟩, ⟨.privateRow 15 18, 41143218734818849276925977680⟩, ⟨.privateRow 16 1, 59938646219264081629760400⟩, ⟨.privateRow 16 2, 14152180357326241495915650⟩, ⟨.privateRow 16 4, 64695681633491389695614400⟩, ⟨.privateRow 16 6, 160391377383030736953710700⟩, ⟨.privateRow 16 7, 3478863244200923364086901600⟩, ⟨.privateRow 16 9, 11233686274748741027424600400⟩, ⟨.privateRow 16 10, 6892111834017879608510921550⟩, ⟨.privateRow 16 13, 167471241476455811366067435840⟩, ⟨.privateRow 17 0, 426230373114766802700518400⟩, ⟨.privateRow 17 4, 1602462268152632883229833600⟩, ⟨.privateRow 17 6, 19349890234016970190779216000⟩, ⟨.privateRow 17 12, 1031093895601932372412824061440⟩, ⟨.privateRow 17 15, 877208747268509752882835649600⟩, ⟨.privateRow 18 2, 27495664694233840620636120000⟩, ⟨.privateRow 18 7, 449951277351862227400809750400⟩, ⟨.hall 13 7, 38890850930349571205052⟩, ⟨.hall 14 7, 179303642536260073251420⟩, ⟨.hall 12 11, 104338588744675129086000⟩, ⟨.hall 15 12, 5751133840533783982179900⟩, ⟨.hall 17 15, 5392037324862727314909846312600⟩, ⟨.hall 9 16, 19716962704580866921560⟩, ⟨.hall 7 17, 17574806867478890072736⟩, ⟨.hall 8 17, 34716598026559846490912⟩, ⟨.hall 7 23, 33221615333482050451240572⟩, ⟨.hall 6 26, 48153493498897129745751148800⟩, ⟨.hall 5 27, 112904361970705000420762494600⟩, ⟨.hall 4 28, 201473953211674744588916248320⟩, ⟨.hall 3 29, 357268962684629501316091401120⟩]
  caps := #[0, 14362925695232140156188240000, 0, 118943461254378282414631200, 16376617503735171100017600, 43429988623833032550843072, 8866887290614539454248500, 4717173216297946213149356, 965216781906160328864368, 5766869833355694365957928, 0, 3013000002064167120612425, 2641303065924780422237215, 27325080849909386212707390, 0, 135450490163039579107696116, 161668211085939431166447000, 19040184553381618147837155840, 0] }

theorem case_51_33_21_checked :
    (Witness.linear .conditional case_51_33_21).check 51 33 21 = true := by
  change case_51_33_21.check 51 33 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_34_1_checked :
    (Witness.rising).check 51 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_34_2_checked :
    (Witness.rising).check 51 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_34_3_checked :
    (Witness.rising).check 51 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_34_4_checked :
    (Witness.rising).check 51 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_34_5_checked :
    (Witness.rising).check 51 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_34_6_checked :
    (Witness.rising).check 51 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_34_7_checked :
    (Witness.rising).check 51 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_34_8_checked :
    (Witness.rising).check 51 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_34_9_checked :
    (Witness.rising).check 51 34 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_34_10_checked :
    (Witness.linear .positive case_51_34_10).check 51 34 10 = true := by
  change case_51_34_10.check 51 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_34_11_checked :
    (Witness.linear .positive case_51_34_11).check 51 34 11 = true := by
  change case_51_34_11.check 51 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_51_34_12_checked :
    (Witness.linear .positive case_51_34_12).check 51 34 12 = true := by
  change case_51_34_12.check 51 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_51_34_13_checked :
    (Witness.linear .positive case_51_34_13).check 51 34 13 = true := by
  change case_51_34_13.check 51 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_51_34_14_checked :
    (Witness.linear .positive case_51_34_14).check 51 34 14 = true := by
  change case_51_34_14.check 51 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_51_34_15_checked :
    (Witness.linear .positive case_51_34_15).check 51 34 15 = true := by
  change case_51_34_15.check 51 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_16 : Certificate := {
  objectiveScale := 443
  eta := 1289414385
  rows := #[⟨.assumptionRow 16, 1202⟩]
  caps := #[0, 0, 366398280, 105224356, 30595852, 9027850, 2711228, 831974, 262262, 85569, 29220, 10626, 1483867, 715925, 216510, 45700, 6329, 443] }

theorem case_51_34_16_checked :
    (Witness.linear .conditional case_51_34_16).check 51 34 16 = true := by
  change case_51_34_16.check 51 34 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_17 : Certificate := {
  objectiveScale := 1294644668539200000
  eta := 225754120104750335584886400
  rows := #[⟨.count 2, 27439203148704945999601200⟩, ⟨.count 3, 3194037093375950302681200⟩, ⟨.count 4, 351178430068492037051040⟩, ⟨.count 5, 36141862442726453212800⟩, ⟨.count 6, 3591018383732436056400⟩, ⟨.count 7, 737159199006658428000⟩, ⟨.count 8, 235890943682130696960⟩, ⟨.count 9, 117945471841065348480⟩, ⟨.path 6, 1598059131000529317120⟩, ⟨.privateRow 2 32, 1929071907880524440233200⟩, ⟨.privateRow 3 28, 135456688613468519437140⟩, ⟨.privateRow 3 29, 394481735624869843030080⟩, ⟨.privateRow 3 30, 599804325455747763110760⟩, ⟨.privateRow 4 25, 34460261898516264070260⟩, ⟨.privateRow 4 26, 91950921698036551382232⟩, ⟨.privateRow 4 27, 152737016593897104879510⟩, ⟨.privateRow 4 28, 219260632152540482824320⟩, ⟨.privateRow 4 29, 328890948228810724236480⟩, ⟨.privateRow 5 22, 5728253518566740741580⟩, ⟨.privateRow 5 23, 20116322337627415991520⟩, ⟨.privateRow 5 24, 36782839917672242874480⟩, ⟨.privateRow 5 25, 56501778285462355189344⟩, ⟨.privateRow 5 26, 79419425931837360008640⟩, ⟨.privateRow 5 27, 122249077450504221016800⟩, ⟨.privateRow 5 28, 117322045775619717352320⟩, ⟨.privateRow 6 19, 594641753865371131920⟩, ⟨.privateRow 6 20, 3719728720066931972400⟩, ⟨.privateRow 6 21, 8830333512148510437075⟩, ⟨.privateRow 6 22, 14772269173019145559200⟩, ⟨.privateRow 6 23, 22180008708842008724700⟩, ⟨.privateRow 6 24, 30423262199384799664920⟩, ⟨.privateRow 6 25, 46244014965780201419850⟩, ⟨.privateRow 6 26, 47597082376496589736800⟩, ⟨.privateRow 6 27, 22366638696527027802900⟩, ⟨.privateRow 7 17, 473888056504280418000⟩, ⟨.privateRow 7 18, 1925038593977388009120⟩, ⟨.privateRow 7 19, 3947897043568992914400⟩, ⟨.privateRow 7 20, 6463306548433380145500⟩, ⟨.privateRow 7 21, 9497318414957213583600⟩, ⟨.privateRow 7 22, 12840611190315983474400⟩, ⟨.privateRow 7 23, 19233536586653727898560⟩, ⟨.privateRow 7 24, 15296053379388162381000⟩, ⟨.privateRow 8 15, 293020781605146725130⟩, ⟨.privateRow 8 16, 1002536510649055462080⟩, ⟨.privateRow 8 17, 1957894832561684784768⟩, ⟨.privateRow 8 18, 3168146424175283110560⟩, ⟨.privateRow 8 19, 4602637748797823559825⟩, ⟨.privateRow 8 20, 6157385480845616897880⟩, ⟨.privateRow 8 21, 7000555193233232871240⟩, ⟨.privateRow 9 13, 176918207761598022720⟩, ⟨.privateRow 9 14, 572253955969613357440⟩, ⟨.privateRow 9 15, 1116312193081598298240⟩, ⟨.privateRow 9 16, 1799978950818925068192⟩, ⟨.privateRow 9 17, 2607905432930222705280⟩, ⟨.privateRow 9 18, 1824059484653142576840⟩, ⟨.privateRow 10 11, 113733133561027300320⟩, ⟨.privateRow 10 12, 374250054880303509600⟩, ⟨.privateRow 10 13, 749445185656769401800⟩, ⟨.privateRow 10 14, 1223684270351052990480⟩, ⟨.privateRow 10 15, 143746043806298393460⟩, ⟨.privateRow 11 9, 81438540080735597760⟩, ⟨.privateRow 11 10, 286589443695445776600⟩, ⟨.privateRow 11 11, 441485454350141586000⟩, ⟨.privateRow 12 7, 67572926575610355900⟩, ⟨.privateRow 12 8, 168610540598189649960⟩, ⟨.privateRow 13 5, 62689504991154481440⟩, ⟨.privateRow 14 3, 16732343723484469080⟩, ⟨.hall 4 29, 48811593110148893200176⟩, ⟨.hall 3 30, 186684378181986236151600⟩, ⟨.hall 2 31, 510597926436955751769375⟩, ⟨.assumptionRow 17, 1422176096974232160⟩]
  caps := #[0, 10270901235717672390720, 0, 0, 573113726625893696496, 0, 220418666232102540345, 0, 22191220983813298560, 0, 57563236028388453660, 43631247734778337920, 58509617019721010220, 78668492421613248000, 0, 816955678754198311680, 150600036604230053280, 19292138599652967840] }

theorem case_51_34_17_checked :
    (Witness.linear .conditional case_51_34_17).check 51 34 17 = true := by
  change case_51_34_17.check 51 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_18 : Certificate := {
  objectiveScale := 3300074645296000000
  eta := 536007914600595118781299200
  rows := #[⟨.count 2, 66326341226143496054356800⟩, ⟨.count 3, 7859650352544912692010240⟩, ⟨.count 4, 868609427373525758880960⟩, ⟨.count 5, 85257726787970094758400⟩, ⟨.count 6, 8803787005279520654400⟩, ⟨.count 7, 1621750237814648541600⟩, ⟨.count 8, 707672831046392090880⟩, ⟨.count 9, 235890943682130696960⟩, ⟨.count 10, 147431839801331685600⟩, ⟨.path 6, 3708312119018226720000⟩, ⟨.privateRow 2 32, 5228522766714426898118400⟩, ⟨.privateRow 3 28, 228396491825563002942000⟩, ⟨.privateRow 3 29, 1001196519038416691870880⟩, ⟨.privateRow 3 30, 1636021639907417448766080⟩, ⟨.privateRow 4 25, 50046440076942047018280⟩, ⟨.privateRow 4 26, 201129464493772712129232⟩, ⟨.privateRow 4 27, 390407409928201374809100⟩, ⟨.privateRow 4 28, 606781712788440786717120⟩, ⟨.privateRow 4 29, 976131468140636957189040⟩, ⟨.privateRow 5 22, 6232154485316292252720⟩, ⟨.privateRow 5 23, 36313966549596579180480⟩, ⟨.privateRow 5 24, 83466078906193911607680⟩, ⟨.privateRow 5 25, 143455392464975768136960⟩, ⟨.privateRow 5 26, 222040775417365594609920⟩, ⟨.privateRow 5 27, 373002554697369164568000⟩, ⟨.privateRow 5 28, 404649852195295020394080⟩, ⟨.privateRow 6 19, 123561922881116079360⟩, ⟨.privateRow 6 20, 5032574150678790315600⟩, ⟨.privateRow 6 21, 16651899763275409132500⟩, ⟨.privateRow 6 22, 33102459786141856796400⟩, ⟨.privateRow 6 23, 55937512170971925093600⟩, ⟨.privateRow 6 24, 85080106523828490394320⟩, ⟨.privateRow 6 25, 143360790367769913638700⟩, ⟨.privateRow 6 26, 170193677735103949726800⟩, ⟨.privateRow 6 27, 136941362343086929828200⟩, ⟨.privateRow 7 17, 88076164037159188800⟩, ⟨.privateRow 7 18, 2695896499224350822400⟩, ⟨.privateRow 7 19, 7324788231399494856000⟩, ⟨.privateRow 7 20, 14085006123877223535000⟩, ⟨.privateRow 7 21, 23486794724269288526400⟩, ⟨.privateRow 7 22, 35517032264520809402400⟩, ⟨.privateRow 7 23, 59554038603177924886080⟩, ⟨.privateRow 7 24, 74100295768719314694600⟩, ⟨.privateRow 7 25, 40972010337170081769600⟩, ⟨.privateRow 8 15, 15971782645144265940⟩, ⟨.privateRow 8 16, 1341629742192118338960⟩, ⟨.privateRow 8 17, 3463173916933281294744⟩, ⟨.privateRow 8 18, 6618051475526444553600⟩, ⟨.privateRow 8 19, 10967085983221560762570⟩, ⟨.privateRow 8 20, 16061645861785077634080⟩, ⟨.privateRow 8 21, 28589490934808236032600⟩, ⟨.privateRow 8 22, 29539443422594816526816⟩, ⟨.privateRow 9 14, 660713059850412368800⟩, ⟨.privateRow 9 15, 1833515971347470417280⟩, ⟨.privateRow 9 16, 3534432639503924942784⟩, ⟨.privateRow 9 17, 5871063487199697346560⟩, ⟨.privateRow 9 18, 8845910388079901136000⟩, ⟨.privateRow 9 19, 14475466480557417054720⟩, ⟨.privateRow 10 12, 337959140467668017760⟩, ⟨.privateRow 10 13, 1093452811859876668200⟩, ⟨.privateRow 10 14, 2206116439209017768160⟩, ⟨.privateRow 10 15, 3713808044595545160264⟩, ⟨.privateRow 10 16, 5094589130912683802400⟩, ⟨.privateRow 11 10, 192564035658882201600⟩, ⟨.privateRow 11 11, 735539068898951486400⟩, ⟨.privateRow 11 12, 1630525942564727808600⟩, ⟨.privateRow 11 13, 1702167604979011279200⟩, ⟨.privateRow 12 8, 126136129607805997680⟩, ⟨.privateRow 12 9, 568164198962274829200⟩, ⟨.privateRow 12 10, 698006054737074006000⟩, ⟨.privateRow 13 6, 98463407295889375740⟩, ⟨.privateRow 13 7, 327439095634957610304⟩, ⟨.privateRow 14 4, 106299595419783685920⟩, ⟨.privateRow 14 5, 18823886688920027715⟩, ⟨.hall 5 28, 20036204908567184937600⟩, ⟨.hall 4 29, 201711750055349971653216⟩, ⟨.hall 3 30, 609767626513547757134880⟩, ⟨.hall 2 31, 1483039912786564383526275⟩, ⟨.assumptionRow 18, 2839259329679948736⟩]
  caps := #[0, 0, 19054372704771600852480, 115923012443785660872, 1705783881702854060316, 65661143743916726016, 228599644367173708200, 25888616981747487968, 285894352160479180690, 36693876604271205440, 224365701241949782544, 33743067412952719008, 208201298893209144336, 351829489135668441744, 0, 7327588048790872908672, 1804649480324454920640, 347280733515344820224] }

theorem case_51_34_18_checked :
    (Witness.linear .conditional case_51_34_18).check 51 34 18 = true := by
  change case_51_34_18.check 51 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_19 : Certificate := {
  objectiveScale := 16537874074722000000
  eta := 2997461503549961123656780800
  rows := #[⟨.count 2, 369496330683213894421060800⟩, ⟨.count 3, 43110013521684113392227840⟩, ⟨.count 4, 4575559785249168976740480⟩, ⟨.count 5, 407290988296878876590400⟩, ⟨.count 6, 27106396832044839909600⟩, ⟨.count 7, 2211477597019975284000⟩, ⟨.count 8, 707672831046392090880⟩, ⟨.count 9, 353836415523196045440⟩, ⟨.path 6, 20859121634099729460480⟩, ⟨.privateRow 2 32, 30675405748264077164364000⟩, ⟨.privateRow 3 28, 1096303160762702414121600⟩, ⟨.privateRow 3 29, 5609417839235827352255520⟩, ⟨.privateRow 3 30, 9525187846780556744233440⟩, ⟨.privateRow 4 25, 236879790093369628765560⟩, ⟨.privateRow 4 26, 1045945499092503555978432⟩, ⟨.privateRow 4 27, 2166026993520649749109620⟩, ⟨.privateRow 4 28, 3519615037547511102039840⟩, ⟨.privateRow 4 29, 5918229974996456713596000⟩, ⟨.privateRow 5 22, 31554626055765018766560⟩, ⟨.privateRow 5 23, 175744770669301709304000⟩, ⟨.privateRow 5 24, 431107548932214000887040⟩, ⟨.privateRow 5 25, 781887491799414438582144⟩, ⟨.privateRow 5 26, 1276711290789311959742160⟩, ⟨.privateRow 5 27, 2270079647171864610001920⟩, ⟨.privateRow 5 28, 2649198517051849020498240⟩, ⟨.privateRow 6 19, 2189362821049775531160⟩, ⟨.privateRow 6 20, 23669830851913798952400⟩, ⟨.privateRow 6 21, 79205123221840424308500⟩, ⟨.privateRow 6 22, 167040274494908799784800⟩, ⟨.privateRow 6 23, 298575802711946901141000⟩, ⟨.privateRow 6 24, 482146345702295011417680⟩, ⟨.privateRow 6 25, 868273493395692724540200⟩, ⟨.privateRow 6 26, 1124722403025359112374400⟩, ⟨.privateRow 6 27, 1032765303231178505188200⟩, ⟨.privateRow 7 17, 1654300124524033459200⟩, ⟨.privateRow 7 18, 12125215739089521628560⟩, ⟨.privateRow 7 19, 33923364281906414515200⟩, ⟨.privateRow 7 20, 68911221549997444117500⟩, ⟨.privateRow 7 21, 122091616233845655883200⟩, ⟨.privateRow 7 22, 196958407128879036841200⟩, ⟨.privateRow 7 23, 355643508645332368100640⟩, ⟨.privateRow 7 24, 485940609408039283297800⟩, ⟨.privateRow 7 25, 510345844318009724824800⟩, ⟨.privateRow 8 15, 858790466842757068620⟩, ⟨.privateRow 8 16, 5922739091655315624240⟩, ⟨.privateRow 8 17, 15533418641468306394816⟩, ⟨.privateRow 8 18, 31280122011182539294800⟩, ⟨.privateRow 8 19, 55132136493707983830120⟩, ⟨.privateRow 8 20, 88819258803742264477680⟩, ⟨.privateRow 8 21, 161069284982954866518000⟩, ⟨.privateRow 8 22, 230736726562676141231424⟩, ⟨.privateRow 8 23, 130256030464476544227600⟩, ⟨.privateRow 9 13, 429442487216186653440⟩, ⟨.privateRow 9 14, 3040372163014128983040⟩, ⟨.privateRow 9 15, 7988125138326698601600⟩, ⟨.privateRow 9 16, 16103488422033455579136⟩, ⟨.privateRow 9 17, 28376806854798537175040⟩, ⟨.privateRow 9 18, 45689127154432689367440⟩, ⟨.privateRow 9 19, 82881967998028635596160⟩, ⟨.privateRow 9 20, 93563521801031783941440⟩, ⟨.privateRow 10 11, 236944028252140209000⟩, ⟨.privateRow 10 12, 1721550252449396144160⟩, ⟨.privateRow 10 13, 4750991037597913568460⟩, ⟨.privateRow 10 14, 9718438821813236838960⟩, ⟨.privateRow 10 15, 17209718660009447660088⟩, ⟨.privateRow 10 16, 27785987407890978346080⟩, ⟨.privateRow 10 17, 42775505420358871930770⟩, ⟨.privateRow 11 9, 151644178081369733760⟩, ⟨.privateRow 11 10, 1119278457267252796800⟩, ⟨.privateRow 11 11, 3329367371337764988000⟩, ⟨.privateRow 11 12, 7066197464763825788400⟩, ⟨.privateRow 11 13, 12711688109623909879200⟩, ⟨.privateRow 11 14, 13401554237941050221040⟩, ⟨.privateRow 12 7, 123079259119861719675⟩, ⟨.privateRow 12 8, 872656080347882310480⟩, ⟨.privateRow 12 9, 2796691736639546974800⟩, ⟨.privateRow 12 10, 6308786639410830590400⟩, ⟨.privateRow 12 11, 3118007897703163565100⟩, ⟨.privateRow 13 5, 114476487375151661760⟩, ⟨.privateRow 13 6, 834042979447533535680⟩, ⟨.privateRow 13 7, 2891348995418116257024⟩, ⟨.privateRow 13 8, 556028652965022357120⟩, ⟨.privateRow 14 3, 150591093511360221720⟩, ⟨.privateRow 14 4, 1062995954197836859200⟩, ⟨.privateRow 14 5, 169414980200280249435⟩, ⟨.privateRow 15 1, 221923716753583484640⟩, ⟨.privateRow 15 2, 234252812128782567120⟩, ⟨.hall 5 28, 274898648685724415352000⟩, ⟨.hall 4 29, 1447240645081576274817888⟩, ⟨.hall 3 30, 3916495435608095944443840⟩, ⟨.hall 2 31, 8973346784608177211740500⟩, ⟨.assumptionRow 19, 9000689589073216320⟩]
  caps := #[0, 0, 19585875741197256691200, 18524287015690802526180, 191829050558509751244, 1134928033880770093536, 1472772792801345415380, 281628007425899738760, 89508788623906903680, 0, 55467642637863730560, 395056453051400535360, 0, 3283506556937852813568, 3053830995724417552215, 0, 31143532226120625579840, 7925521435549055257920] }

theorem case_51_34_19_checked :
    (Witness.linear .conditional case_51_34_19).check 51 34 19 = true := by
  change case_51_34_19.check 51 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_20 : Certificate := {
  objectiveScale := 438902507890246400000
  eta := 99107345139774862104133920000
  rows := #[⟨.count 2, 13807616402229970346846820000⟩, ⟨.count 3, 1864668824626631255976744000⟩, ⟨.count 4, 237884660683264585480089600⟩, ⟨.count 5, 27508879577118482623080000⟩, ⟨.count 6, 2642585282211381795288000⟩, ⟨.count 7, 165407722582530604176000⟩, ⟨.path 7, 168247907978227557480000⟩, ⟨.privateRow 2 32, 1285162868558735284246128000⟩, ⟨.privateRow 3 29, 254448231201693703687312800⟩, ⟨.privateRow 4 26, 39715024316723055322102080⟩, ⟨.privateRow 4 27, 86207846671616303083249800⟩, ⟨.privateRow 4 28, 138841141920251331613852800⟩, ⟨.privateRow 4 29, 136034658589115910565141200⟩, ⟨.privateRow 5 22, 249096153651072874146000⟩, ⟨.privateRow 5 23, 4752940273391899809792000⟩, ⟨.privateRow 5 24, 16849008236525903162524800⟩, ⟨.privateRow 5 25, 31451096965335462022608000⟩, ⟨.privateRow 5 26, 53152787082118932684075600⟩, ⟨.privateRow 5 27, 98003813078208775782844800⟩, ⟨.privateRow 5 28, 120657844721559681577641600⟩, ⟨.privateRow 5 29, 168900188496487464647030400⟩, ⟨.privateRow 6 19, 16967419161739746499800⟩, ⟨.privateRow 6 20, 635776817289775371210000⟩, ⟨.privateRow 6 21, 2590690250200741613174250⟩, ⟨.privateRow 6 22, 6370260227532199050624000⟩, ⟨.privateRow 6 23, 11859142967301078138690000⟩, ⟨.privateRow 6 24, 19558741177547574167365200⟩, ⟨.privateRow 6 25, 36285908904135452554492500⟩, ⟨.privateRow 6 26, 48153776253629623825248000⟩, ⟨.privateRow 6 27, 44044893081448037695917000⟩, ⟨.privateRow 7 16, 2297329480312925058000⟩, ⟨.privateRow 7 17, 58000110515952289776000⟩, ⟨.privateRow 7 18, 383194557316195899674400⟩, ⟨.privateRow 7 19, 1163105096889858057936000⟩, ⟨.privateRow 7 20, 2557173854032604831524500⟩, ⟨.privateRow 7 21, 4749564605584093062768000⟩, ⟨.privateRow 7 22, 7928084036559904375158000⟩, ⟨.privateRow 7 23, 14883544409140468078617600⟩, ⟨.privateRow 7 24, 21672842222309255502525000⟩, ⟨.privateRow 7 25, 25445221323945957942408000⟩, ⟨.privateRow 7 26, 14639568018331235437458000⟩, ⟨.privateRow 8 13, 492284888638483941000⟩, ⟨.privateRow 8 14, 4241223655962323184000⟩, ⟨.privateRow 8 15, 41007331223585712285300⟩, ⟨.privateRow 8 16, 198990502622014090478400⟩, ⟨.privateRow 8 17, 537437258624405688068520⟩, ⟨.privateRow 8 18, 1131970812599521940245200⟩, ⟨.privateRow 8 19, 2079829811764298878133850⟩, ⟨.privateRow 8 20, 3480651076629536856446400⟩, ⟨.privateRow 8 21, 6599768131042971106622400⟩, ⟨.privateRow 8 22, 10021778231737891756016880⟩, ⟨.privateRow 8 23, 12737773036543044276586800⟩, ⟨.privateRow 8 26, 12016871045620848393386400⟩, ⟨.privateRow 9 11, 408414129833408899200⟩, ⟨.privateRow 9 12, 3325657914357758179200⟩, ⟨.privateRow 9 13, 25918589008658641680000⟩, ⟨.privateRow 9 14, 107719226743561597164000⟩, ⟨.privateRow 9 15, 276570623011732990012800⟩, ⟨.privateRow 9 16, 570350332312355527732800⟩, ⟨.privateRow 9 17, 1037508027820136406934400⟩, ⟨.privateRow 9 18, 1731420651662507852046000⟩, ⟨.privateRow 9 19, 3289075677299822839228800⟩, ⟨.privateRow 9 20, 5218919958076215618427200⟩, ⟨.privateRow 9 21, 5250653735964271489895040⟩, ⟨.privateRow 10 9, 344599422046938758700⟩, ⟨.privateRow 10 10, 2573009017950476064960⟩, ⟨.privateRow 10 11, 17525342035530028299600⟩, ⟨.privateRow 10 12, 65951027850214125511200⟩, ⟨.privateRow 10 13, 165982054952608835440500⟩, ⟨.privateRow 10 14, 338960522413443397194000⟩, ⟨.privateRow 10 15, 612146413324182010954680⟩, ⟨.privateRow 10 16, 1016491717389125573996400⟩, ⟨.privateRow 10 17, 1915283587736885620854600⟩, ⟨.privateRow 10 18, 3129750408008025503301600⟩, ⟨.privateRow 11 7, 347495215509518076000⟩, ⟨.privateRow 11 8, 2338353221032798719750⟩, ⟨.privateRow 11 9, 13652700911573954630400⟩, ⟨.privateRow 11 10, 48243919086571426218000⟩, ⟨.privateRow 11 11, 120420457374644533260000⟩, ⟨.privateRow 11 12, 245978349356362475853000⟩, ⟨.privateRow 11 13, 443593437834968438472000⟩, ⟨.privateRow 11 15, 2841030790653650655060000⟩, ⟨.privateRow 11 16, 1544789980547562606858000⟩, ⟨.privateRow 12 5, 401121020372098026000⟩, ⟨.privateRow 12 6, 2548298247069799224000⟩, ⟨.privateRow 12 7, 12860942715680392958625⟩, ⟨.privateRow 12 8, 43561742812409845623600⟩, ⟨.privateRow 12 9, 109076266039755513213000⟩, ⟨.privateRow 12 10, 224658626871480440562000⟩, ⟨.privateRow 12 11, 407338396187865545403000⟩, ⟨.privateRow 12 12, 677384006766553902816000⟩, ⟨.privateRow 12 13, 21299526181758405180600⟩, ⟨.privateRow 12 14, 3713578406604883524708000⟩, ⟨.privateRow 13 3, 456011265265121966400⟩, ⟨.privateRow 13 4, 3369416571125623418400⟩, ⟨.privateRow 13 5, 15289789482418795344000⟩, ⟨.privateRow 13 6, 50360744107716907164300⟩, ⟨.privateRow 13 7, 126497524984544833479360⟩, ⟨.privateRow 13 8, 264877400652569416483200⟩, ⟨.privateRow 13 9, 487195420251329153179200⟩, ⟨.privateRow 13 10, 818768226783526490671200⟩, ⟨.privateRow 13 11, 1498121373104634329251200⟩, ⟨.privateRow 13 12, 54584548452235099378080⟩, ⟨.privateRow 13 13, 6701288214744418461566400⟩, ⟨.privateRow 14 1, 1407934781506064071260⟩, ⟨.privateRow 14 2, 5928146448446585563200⟩, ⟨.privateRow 14 3, 25029951671218916822400⟩, ⟨.privateRow 14 4, 77850511447982366293200⟩, ⟨.privateRow 14 5, 195350950933966389887325⟩, ⟨.privateRow 14 6, 414871448950453546331280⟩, ⟨.privateRow 14 7, 778386800632638279396600⟩, ⟨.privateRow 14 9, 5092030793113598391057000⟩, ⟨.privateRow 14 11, 5935853038829566124432160⟩, ⟨.privateRow 14 12, 12233388879308245596948000⟩, ⟨.privateRow 15 1, 96826391991294230865600⟩, ⟨.privateRow 15 2, 146008051415443681464000⟩, ⟨.privateRow 15 3, 425141090886144837204000⟩, ⟨.privateRow 15 4, 928063676809413900305550⟩, ⟨.privateRow 15 5, 1778378066240104040231520⟩, ⟨.privateRow 15 6, 3116228983066755144388800⟩, ⟨.privateRow 15 10, 84126919064550340385927520⟩, ⟨.privateRow 16 1, 3504193233970648355136000⟩, ⟨.privateRow 16 2, 2087056264350165564456000⟩, ⟨.privateRow 16 7, 3120922099005108691293000⟩, ⟨.privateRow 16 10, 766213751815394579402706000⟩, ⟨.privateRow 17 2, 122208739034726361385368000⟩, ⟨.privateRow 17 7, 10034735170006856653344000⟩, ⟨.privateRow 17 17, 100006170704288333407226304000⟩, ⟨.hall 13 6, 368433471498343465500⟩, ⟨.hall 14 6, 1732432993961882071860⟩, ⟨.hall 14 8, 1109925458723734773120⟩, ⟨.hall 11 11, 1369725526972539000⟩, ⟨.hall 9 14, 2433084984668474136⟩, ⟨.hall 15 15, 89503387554977860464000⟩, ⟨.hall 13 17, 2248931747902752300960⟩, ⟨.hall 5 20, 9721101996110102400⟩, ⟨.hall 11 20, 3228899642249931936000⟩, ⟨.hall 10 21, 578872546916794357500⟩, ⟨.hall 3 26, 10874154383821729640640⟩, ⟨.hall 2 31, 756659349950896483496905500⟩]
  caps := #[0, 0, 458114860002245029584000, 34282525470541018370700, 30899297470770276130440, 0, 15731208477874570287750, 5616154861577963041500, 11747100030491112850850, 0, 3768895015120372914000, 3209492673882826202450, 0, 161887534103712591496080, 181577632502852684509125, 0, 18758454287914611206937000, 0] }

theorem case_51_34_20_checked :
    (Witness.linear .conditional case_51_34_20).check 51 34 20 = true := by
  change case_51_34_20.check 51 34 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_21 : Certificate := {
  objectiveScale := 425482414148237160000000
  eta := 106489552950876102405307221312000
  rows := #[⟨.count 2, 13601777548300477548285873600000⟩, ⟨.count 3, 1634068093643552825459980178400⟩, ⟨.count 4, 178059633359569887904833254400⟩, ⟨.count 5, 16441709124319258574851056000⟩, ⟨.count 6, 1121025622112676721012572000⟩, ⟨.count 7, 43235147960268523675416000⟩, ⟨.path 6, 582890174357565718855411200⟩, ⟨.path 7, 33412763206123802484984000⟩, ⟨.privateRow 2 32, 1502378156471370929197030584000⟩, ⟨.privateRow 3 31, 2609686501426196169605212384800⟩, ⟨.privateRow 4 25, 279690230971546616252631600⟩, ⟨.privateRow 4 26, 27459692466017003050403104560⟩, ⟨.privateRow 4 28, 267118891116299205185276474400⟩, ⟨.privateRow 4 30, 1080016466627391165327530275200⟩, ⟨.privateRow 5 23, 3101989513655510649659030400⟩, ⟨.privateRow 5 24, 12125194304628830634952142400⟩, ⟨.privateRow 5 25, 20480119001796683077698769920⟩, ⟨.privateRow 5 27, 203034725401304431095392131200⟩, ⟨.privateRow 6 19, 1698523669867692001534200⟩, ⟨.privateRow 6 20, 271763787178830720245472000⟩, ⟨.privateRow 6 21, 1597319967871408686442787250⟩, ⟨.privateRow 6 22, 4471161355727905421181456000⟩, ⟨.privateRow 6 23, 8972923098206601801438171000⟩, ⟨.privateRow 6 26, 176746485837909954466313814000⟩, ⟨.privateRow 7 16, 1029408284768298182748000⟩, ⟨.privateRow 7 17, 17687105983746214230852000⟩, ⟨.privateRow 7 18, 164602384734450879421405200⟩, ⟨.privateRow 7 19, 673233018238467011517192000⟩, ⟨.privateRow 7 20, 1703156007149149343356566000⟩, ⟨.privateRow 7 21, 3534693933241545017218704000⟩, ⟨.privateRow 7 22, 6639683436755523278724600000⟩, ⟨.privateRow 7 24, 26779541824104893075097846000⟩, ⟨.privateRow 8 14, 1164023214314921791261200⟩, ⟨.privateRow 8 15, 12069812138908296192720300⟩, ⟨.privateRow 8 16, 82539827924148999743976000⟩, ⟨.privateRow 8 17, 288594612634792395533401800⟩, ⟨.privateRow 8 18, 704492716485930999666639600⟩, ⟨.privateRow 8 19, 1457835145285304282680433250⟩, ⟨.privateRow 8 20, 2742961315593607337750320800⟩, ⟨.privateRow 8 21, 5976538619707785589398338400⟩, ⟨.privateRow 8 22, 3559117380089304868960245120⟩, ⟨.privateRow 8 23, 16001868699444883968817404300⟩, ⟨.privateRow 9 12, 823526627814638546198400⟩, ⟨.privateRow 9 13, 7390623582951884388960000⟩, ⟨.privateRow 9 14, 42434497072115402866612000⟩, ⟨.privateRow 9 15, 136605598807797921269395200⟩, ⟨.privateRow 9 16, 327818499645413783956709760⟩, ⟨.privateRow 9 17, 673827787469666472689446400⟩, ⟨.privateRow 9 18, 1264628077837854317505918000⟩, ⟨.privateRow 9 19, 2762382818566235896798166400⟩, ⟨.privateRow 9 20, 5189178536298006586020484800⟩, ⟨.privateRow 9 21, 4693991974993064428191386880⟩, ⟨.privateRow 9 22, 10956266883664935771835696800⟩, ⟨.privateRow 9 23, 9039668787603995179720681600⟩, ⟨.privateRow 10 10, 576468639470246982338880⟩, ⟨.privateRow 10 11, 4941159766887831277190400⟩, ⟨.privateRow 10 12, 24610776531229775015236800⟩, ⟨.privateRow 10 13, 75301216030801012068016200⟩, ⟨.privateRow 10 14, 178443247036017361351262400⟩, ⟨.privateRow 10 15, 364039945825460969347002720⟩, ⟨.privateRow 10 16, 676630065578202395520260400⟩, ⟨.privateRow 10 17, 1458375584634807639226375950⟩, ⟨.privateRow 10 18, 2793299380718777118886698000⟩, ⟨.privateRow 10 19, 4869358539025242478943727000⟩, ⟨.privateRow 10 20, 5100882756352480423225579680⟩, ⟨.privateRow 10 21, 7976344359320039261568309300⟩, ⟨.privateRow 11 8, 579042160182167727795750⟩, ⟨.privateRow 11 9, 3705869825165873457892800⟩, ⟨.privateRow 11 10, 16764649209083713261896000⟩, ⟨.privateRow 11 11, 50361820700972126479056000⟩, ⟨.privateRow 11 12, 118124600677162216470333000⟩, ⟨.privateRow 11 13, 239758547779670904018216000⟩, ⟨.privateRow 11 14, 441924976651030409853716400⟩, ⟨.privateRow 11 15, 930585089430541557204192000⟩, ⟨.privateRow 11 16, 1785766022001805272522093000⟩, ⟨.privateRow 11 17, 3196312724205565857432540000⟩, ⟨.privateRow 11 18, 5209320625069972953796254000⟩, ⟨.privateRow 11 19, 5821303850364726223439940000⟩, ⟨.privateRow 11 21, 2806166984278380846171048000⟩, ⟨.privateRow 12 6, 666087713673604706484000⟩, ⟨.privateRow 12 7, 3538590978891025003196250⟩, ⟨.privateRow 12 8, 14343088767771621346288800⟩, ⟨.privateRow 12 9, 42058681349104754323704000⟩, ⟨.privateRow 12 10, 98862787964093867781606000⟩, ⟨.privateRow 12 11, 200048343339972613514028000⟩, ⟨.privateRow 12 12, 367498757662282451241036000⟩, ⟨.privateRow 12 13, 756409207647745504683230400⟩, ⟨.privateRow 12 14, 1436196125299237347963918000⟩, ⟨.privateRow 12 16, 9645996803258140385855652000⟩, ⟨.privateRow 12 17, 4326517236857426570574615000⟩, ⟨.privateRow 12 19, 18242144214379012096477308000⟩, ⟨.privateRow 13 4, 754899408830085334015200⟩, ⟨.privateRow 13 5, 3996526282041628238904000⟩, ⟨.privateRow 13 6, 15286713028809228013807800⟩, ⟨.privateRow 13 7, 45293964529805120040912000⟩, ⟨.privateRow 13 8, 106764344963112068667864000⟩, ⟨.privateRow 13 9, 218456275078367771274244800⟩, ⟨.privateRow 13 10, 401983935202020440363094000⟩, ⟨.privateRow 13 11, 815291361536492160736416000⟩, ⟨.privateRow 13 12, 1525953665009134494178325280⟩, ⟨.privateRow 13 13, 2761422037500452151827601600⟩, ⟨.privateRow 13 14, 611468521152369120552312000⟩, ⟨.privateRow 13 15, 13541601281139450745945804800⟩, ⟨.privateRow 14 3, 4906846157395554671098800⟩, ⟨.privateRow 14 4, 23379678749943525197588400⟩, ⟨.privateRow 14 5, 66242423124839988059833800⟩, ⟨.privateRow 14 6, 156037707805178638540941840⟩, ⟨.privateRow 14 7, 321748912320651370576335600⟩, ⟨.privateRow 14 8, 601277379133162968543106800⟩, ⟨.privateRow 14 9, 1210764289337353115093628900⟩, ⟨.privateRow 14 10, 2244213001623366868208914800⟩, ⟨.privateRow 14 11, 4027539325990271274037895040⟩, ⟨.privateRow 14 12, 6977535235816478742302493600⟩, ⟨.privateRow 14 13, 3251398935044229413936842350⟩, ⟨.privateRow 14 14, 24118550819644121366928058800⟩, ⟨.privateRow 15 1, 21693425116906662756436800⟩, ⟨.privateRow 15 2, 45797230802358510263588800⟩, ⟨.privateRow 15 3, 133350760277455662238096800⟩, ⟨.privateRow 15 4, 322011779079083275290858750⟩, ⟨.privateRow 15 5, 673219292794670100874755360⟩, ⟨.privateRow 15 6, 1295407385552426433170083200⟩, ⟨.privateRow 15 7, 2599873564010813890348348800⟩, ⟨.privateRow 15 8, 4843057157349412460374515600⟩, ⟨.privateRow 15 10, 32211482284838858193895182480⟩, ⟨.privateRow 15 12, 1236525231663679777116897600⟩, ⟨.privateRow 15 13, 2826343386659839490552908800⟩, ⟨.privateRow 15 14, 141307355640677183418303242400⟩, ⟨.privateRow 16 1, 858698077544222067442290000⟩, ⟨.privateRow 16 2, 818288756248023381915594000⟩, ⟨.privateRow 16 3, 2221881275645674599506925375⟩, ⟨.privateRow 16 5, 17775050205165396796055403000⟩, ⟨.privateRow 16 6, 12484148973527536211276370000⟩, ⟨.privateRow 16 7, 30397911945065461187457066000⟩, ⟨.privateRow 16 8, 4777483849609671866133468000⟩, ⟨.privateRow 16 9, 160748280116278371025196688000⟩, ⟨.privateRow 16 10, 62856699276237055336775628000⟩, ⟨.privateRow 16 13, 401097872020906127702293659000⟩, ⟨.privateRow 17 11, 12283994944270327385815579872000⟩, ⟨.hall 15 9, 41093468804341909499544000⟩, ⟨.hall 13 11, 264932631979952548669200⟩, ⟨.hall 16 14, 7580788675166873404808169600⟩, ⟨.hall 10 15, 24403397002745819877000⟩, ⟨.hall 14 15, 21600377337606205256868750⟩, ⟨.hall 7 18, 15772403535741432213760⟩, ⟨.hall 9 19, 183421839831442221653280⟩, ⟨.hall 11 21, 38468540032971838611822000⟩, ⟨.hall 5 22, 322601748289687602951600⟩, ⟨.hall 8 22, 1167493594084307893496016⟩, ⟨.hall 4 24, 1943996132807957680836384⟩, ⟨.hall 4 29, 16557661673515559682155790720⟩]
  caps := #[0, 0, 384672114275271280698240000, 74301000909627566513181600, 130642117052975820498286080, 8489311614771900622538400, 0, 0, 13259633967252843119866990, 35655503580225385031174720, 694850592218601273354900, 103265416794531678162739500, 0, 135148862544279208539430560, 264736873574088464740375470, 0, 61827636862703147380257938625, 17870261394225960720000000] }

theorem case_51_34_21_checked :
    (Witness.linear .conditional case_51_34_21).check 51 34 21 = true := by
  change case_51_34_21.check 51 34 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_34_22 : Certificate := {
  objectiveScale := 622
  eta := 11140740
  rows := #[⟨.assumptionRow 22, 245⟩]
  caps := #[0, 0, 5194090, 2734424, 1067605, 623770, 306945, 137394, 78132, 35020, 18991, 10530, 4560, 14407092, 14247530, 9972948, 5798700, 2915976] }

theorem case_51_34_22_checked :
    (Witness.linear .conditional case_51_34_22).check 51 34 22 = true := by
  change case_51_34_22.check 51 34 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_35_1_checked :
    (Witness.rising).check 51 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_35_2_checked :
    (Witness.rising).check 51 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_35_3_checked :
    (Witness.rising).check 51 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_35_4_checked :
    (Witness.rising).check 51 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_35_5_checked :
    (Witness.rising).check 51 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_35_6_checked :
    (Witness.rising).check 51 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_35_7_checked :
    (Witness.rising).check 51 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_35_8_checked :
    (Witness.rising).check 51 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_35_9_checked :
    (Witness.rising).check 51 35 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_35_10_checked :
    (Witness.linear .positive case_51_35_10).check 51 35 10 = true := by
  change case_51_35_10.check 51 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_51_35_11_checked :
    (Witness.linear .positive case_51_35_11).check 51 35 11 = true := by
  change case_51_35_11.check 51 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_51_35_12_checked :
    (Witness.linear .positive case_51_35_12).check 51 35 12 = true := by
  change case_51_35_12.check 51 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_51_35_13_checked :
    (Witness.linear .positive case_51_35_13).check 51 35 13 = true := by
  change case_51_35_13.check 51 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_51_35_14_checked :
    (Witness.linear .positive case_51_35_14).check 51 35 14 = true := by
  change case_51_35_14.check 51 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_51_35_15_checked :
    (Witness.linear .positive case_51_35_15).check 51 35 15 = true := by
  change case_51_35_15.check 51 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_51_35_16_checked :
    (Witness.linear .positive case_51_35_16).check 51 35 16 = true := by
  change case_51_35_16.check 51 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_17 : Certificate := {
  objectiveScale := 442284545102400000
  eta := 140625883622856895064802000
  rows := #[⟨.count 2, 16843507721370463104972000⟩, ⟨.count 3, 2001481544360896274476800⟩, ⟨.count 4, 223524667886458599460800⟩, ⟨.count 5, 22952770004138718744000⟩, ⟨.count 6, 2728650979512994536000⟩, ⟨.count 7, 561781084017381228000⟩, ⟨.count 8, 199744385428402214400⟩, ⟨.count 9, 56178108401738122800⟩, ⟨.path 6, 889613135971271712000⟩, ⟨.privateRow 2 33, 4070291214067266123936000⟩, ⟨.privateRow 3 29, 215851674580587867521700⟩, ⟨.privateRow 3 30, 397337951849423597812800⟩, ⟨.privateRow 3 31, 563490503601605545165200⟩, ⟨.privateRow 4 25, 4741890945909977059200⟩, ⟨.privateRow 4 26, 35282527224310671505200⟩, ⟨.privateRow 4 27, 102351698241532425045360⟩, ⟨.privateRow 4 29, 544098355610929371252000⟩, ⟨.privateRow 4 31, 1117623339432292997304000⟩, ⟨.privateRow 5 22, 1092054869142782344800⟩, ⟨.privateRow 5 23, 6054528754296847925100⟩, ⟨.privateRow 5 24, 19972272946824734936400⟩, ⟨.privateRow 5 25, 38176145665003373227200⟩, ⟨.privateRow 5 26, 45158103651732407416080⟩, ⟨.privateRow 5 27, 58345647084238518704700⟩, ⟨.privateRow 5 28, 218100359419668551826000⟩, ⟨.privateRow 5 29, 79098776629647276902400⟩, ⟨.privateRow 6 19, 42559173031619790000⟩, ⟨.privateRow 6 20, 973753878963460795200⟩, ⟨.privateRow 6 21, 3865588887643408926000⟩, ⟨.privateRow 6 22, 8906570936192231552250⟩, ⟨.privateRow 6 23, 15175732548523951404000⟩, ⟨.privateRow 6 25, 73111795362833471244000⟩, ⟨.privateRow 6 26, 23430952712558275384500⟩, ⟨.privateRow 6 27, 89483701239911438460000⟩, ⟨.privateRow 6 28, 60311212091294570406000⟩, ⟨.privateRow 7 17, 19394823138695304300⟩, ⟨.privateRow 7 18, 701861562110026936800⟩, ⟨.privateRow 7 19, 2076182377647093195480⟩, ⟨.privateRow 7 20, 4146479429652099540000⟩, ⟨.privateRow 7 21, 6792535214074443383550⟩, ⟨.privateRow 7 23, 20503671992624849628600⟩, ⟨.privateRow 7 24, 35358501428053974490320⟩, ⟨.privateRow 7 26, 68531941954082249042400⟩, ⟨.privateRow 8 15, 8642785907959711200⟩, ⟨.privateRow 8 16, 460348388292020728500⟩, ⟨.privateRow 8 17, 1174065720032284606800⟩, ⟨.privateRow 8 18, 2193443032485641816880⟩, ⟨.privateRow 8 19, 3510784996661708365600⟩, ⟨.privateRow 8 20, 4005811229646160034100⟩, ⟨.privateRow 8 22, 18344233063849042950600⟩, ⟨.privateRow 8 23, 20240348255941781887920⟩, ⟨.privateRow 8 24, 5610008325118015318500⟩, ⟨.privateRow 8 27, 116731867246767181609200⟩, ⟨.privateRow 9 13, 3121006022318784600⟩, ⟨.privateRow 9 14, 312580757004542888400⟩, ⟨.privateRow 9 15, 760485134105010514200⟩, ⟨.privateRow 9 16, 1378349750584059598800⟩, ⟨.privateRow 9 17, 2172844392738337838520⟩, ⟨.privateRow 9 18, 2996859338319881834800⟩, ⟨.privateRow 9 19, 3411259582394431567800⟩, ⟨.privateRow 9 20, 462800607309556916400⟩, ⟨.privateRow 9 21, 14128794263037137884200⟩, ⟨.privateRow 9 22, 14878459909598109945120⟩, ⟨.privateRow 10 11, 1070059207652154720⟩, ⟨.privateRow 10 12, 232164631660244283000⟩, ⟨.privateRow 10 13, 588944125442397463200⟩, ⟨.privateRow 10 14, 1064708911613893946400⟩, ⟨.privateRow 10 15, 1670751535584159756000⟩, ⟨.privateRow 10 16, 2385161973856652870880⟩, ⟨.privateRow 10 17, 3117439158293277417600⟩, ⟨.privateRow 10 18, 4025763375288840835650⟩, ⟨.privateRow 10 20, 13274084470924979301600⟩, ⟨.privateRow 10 21, 13855126620680099314560⟩, ⟨.privateRow 11 10, 197069237409271827600⟩, ⟨.privateRow 11 11, 555093213969555261000⟩, ⟨.privateRow 11 12, 1037134308955165344000⟩, ⟨.privateRow 11 13, 1644101386757216887500⟩, ⟨.privateRow 11 14, 2377233807909048270000⟩, ⟨.privateRow 11 16, 11133074339614293066000⟩, ⟨.privateRow 11 17, 2151822187888004882250⟩, ⟨.privateRow 11 19, 14222870301709889820000⟩, ⟨.privateRow 11 20, 16968463885344043472400⟩, ⟨.privateRow 12 8, 198629740420431219900⟩, ⟨.privateRow 12 9, 643462270201495704960⟩, ⟨.privateRow 12 10, 1294771641259107211200⟩, ⟨.privateRow 12 11, 2118717231151266345600⟩, ⟨.privateRow 12 12, 3114318152270958633000⟩, ⟨.privateRow 12 13, 4285587126646879653600⟩, ⟨.privateRow 12 15, 20023185684522152932800⟩, ⟨.privateRow 12 19, 30568381384999103886240⟩, ⟨.privateRow 12 22, 115661362181111838491400⟩, ⟨.privateRow 13 6, 249260850723678393600⟩, ⟨.privateRow 13 7, 943491266997048294525⟩, ⟨.privateRow 13 8, 2101061254225005792720⟩, ⟨.privateRow 13 9, 3651003800108878613400⟩, ⟨.privateRow 13 10, 203722810687621764000⟩, ⟨.privateRow 13 11, 419329451998688130900⟩, ⟨.privateRow 13 12, 33530305271780268151200⟩, ⟨.privateRow 13 14, 30436942445659164214800⟩, ⟨.privateRow 13 17, 51217046400260820479400⟩, ⟨.privateRow 13 19, 32906326996318105430100⟩, ⟨.privateRow 14 4, 403798731554292274200⟩, ⟨.privateRow 14 5, 1845222686607230330400⟩, ⟨.privateRow 14 6, 4590554000827743748800⟩, ⟨.privateRow 14 7, 8645543368225584060240⟩, ⟨.privateRow 14 8, 11968230073586617630800⟩, ⟨.privateRow 14 11, 119563065567013507639200⟩, ⟨.privateRow 14 12, 5011354784236953592440⟩, ⟨.privateRow 14 13, 80717241181221160916400⟩, ⟨.privateRow 14 16, 49922274759001713268200⟩, ⟨.privateRow 15 2, 986566430002453700400⟩, ⟨.privateRow 15 3, 5355646334299034373600⟩, ⟨.privateRow 15 4, 15121824943903155878400⟩, ⟨.privateRow 15 9, 9818684946214896351600⟩, ⟨.privateRow 15 14, 3618886737319204655304000⟩, ⟨.privateRow 16 4, 419246689606846284558375⟩, ⟨.privateRow 16 9, 18257885230564889910000⟩, ⟨.privateRow 16 19, 343390653839418336449298000⟩, ⟨.hall 13 7, 13368838268977191000⟩, ⟨.hall 11 10, 3871024526268900⟩, ⟨.hall 15 12, 318864392373126600⟩, ⟨.hall 12 13, 156178477897041600⟩, ⟨.hall 14 14, 24249637039976277930⟩, ⟨.hall 10 15, 12312804227846850⟩, ⟨.hall 8 16, 2254955783141600⟩, ⟨.hall 9 18, 14060034491417712⟩, ⟨.hall 12 20, 205371611903425968000⟩, ⟨.hall 6 22, 78730515151873200⟩, ⟨.hall 5 25, 2012490130513046800⟩, ⟨.hall 4 26, 4879758676349356800⟩, ⟨.hall 2 30, 1465538852109321539550⟩, ⟨.assumptionRow 17, 647459373521458080⟩]
  caps := #[0, 0, 0, 0, 296993821194037154880, 0, 76824129295258622550, 33923730946028211000, 0, 3253453950627302400, 22701309205954110840, 106672332845250961740, 128999416324397524620, 327148693951379162940, 8258539313437007760, 9816512642299446494400, 647459373521458080] }

theorem case_51_35_17_checked :
    (Witness.linear .conditional case_51_35_17).check 51 35 17 = true := by
  change case_51_35_17.check 51 35 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_18 : Certificate := {
  objectiveScale := 35899719570000000
  eta := 7829763667661820431547000
  rows := #[⟨.count 2, 932647554501503271631200⟩, ⟨.count 3, 110091321841279640261400⟩, ⟨.count 4, 12207846903300153705600⟩, ⟨.count 5, 1103498557891284555000⟩, ⟨.count 6, 131846580942854778000⟩, ⟨.count 7, 28089054200869061400⟩, ⟨.count 8, 10700592076521547200⟩, ⟨.count 9, 4012722028695580200⟩, ⟨.path 6, 49867562937576384000⟩, ⟨.privateRow 2 32, 43227716841127920301200⟩, ⟨.privateRow 2 33, 107304199769348510128200⟩, ⟨.privateRow 3 29, 11845268805707303066100⟩, ⟨.privateRow 3 30, 24601361817928047352200⟩, ⟨.privateRow 3 31, 32598398351116061263800⟩, ⟨.privateRow 4 25, 236914384265639051400⟩, ⟨.privateRow 4 26, 1955819824986362435100⟩, ⟨.privateRow 4 27, 5668829734538656085400⟩, ⟨.privateRow 4 28, 8610441604574566056300⟩, ⟨.privateRow 4 29, 12304534395991580542800⟩, ⟨.privateRow 4 30, 18201420499161102102900⟩, ⟨.privateRow 5 8, 913870441317834000⟩, ⟨.privateRow 5 22, 46475388999019180200⟩, ⟨.privateRow 5 23, 319226368532835889125⟩, ⟨.privateRow 5 24, 1107101818488480586200⟩, ⟨.privateRow 5 25, 2137634349286545509400⟩, ⟨.privateRow 5 26, 3238190244356786638920⟩, ⟨.privateRow 5 27, 4544837632000819102950⟩, ⟨.privateRow 5 28, 7078505352619458958200⟩, ⟨.privateRow 5 29, 6597870425182366129800⟩, ⟨.privateRow 6 20, 44331024317017838400⟩, ⟨.privateRow 6 21, 202546921448443572000⟩, ⟨.privateRow 6 22, 493827547281435241875⟩, ⟨.privateRow 6 23, 858367647566887887000⟩, ⟨.privateRow 6 24, 1310026354368195964500⟩, ⟨.privateRow 6 25, 1816425504989532637200⟩, ⟨.privateRow 6 26, 2810816240100570702000⟩, ⟨.privateRow 6 27, 2904127950767856813000⟩, ⟨.privateRow 6 28, 524520093750922269000⟩, ⟨.privateRow 7 18, 30173585124866765400⟩, ⟨.privateRow 7 19, 107712924170271359940⟩, ⟨.privateRow 7 20, 228661461635192586000⟩, ⟨.privateRow 7 21, 386439462513486857475⟩, ⟨.privateRow 7 22, 583400647600557415200⟩, ⟨.privateRow 7 23, 807703619776010357400⟩, ⟨.privateRow 7 24, 1245319619305468346640⟩, ⟨.privateRow 7 25, 735761246261539598100⟩, ⟨.privateRow 8 16, 18651726466714641300⟩, ⟨.privateRow 8 17, 59663907335756505600⟩, ⟨.privateRow 8 18, 119579116455128289960⟩, ⟨.privateRow 8 19, 199397606981477905000⟩, ⟨.privateRow 8 20, 298446200884233777375⟩, ⟨.privateRow 8 21, 411781712944713111000⟩, ⟨.privateRow 8 22, 394212784485741721500⟩, ⟨.privateRow 9 14, 12003869316610710000⟩, ⟨.privateRow 9 15, 37191988432632183150⟩, ⟨.privateRow 9 16, 73607103071830036800⟩, ⟨.privateRow 9 17, 112712903206026963840⟩, ⟨.privateRow 9 18, 200636101434779010000⟩, ⟨.privateRow 9 19, 92236874409599794875⟩, ⟨.privateRow 10 12, 8557743918340574100⟩, ⟨.privateRow 10 13, 27295328964423781800⟩, ⟨.privateRow 10 14, 55031616393539385600⟩, ⟨.privateRow 10 15, 89009470454701960800⟩, ⟨.privateRow 11 10, 7070034050558879400⟩, ⟨.privateRow 11 11, 24226468030389982500⟩, ⟨.privateRow 11 12, 28956272514762978000⟩, ⟨.privateRow 12 8, 7093919300729686425⟩, ⟨.privateRow 12 9, 12191031687179905560⟩, ⟨.privateRow 13 6, 5563858275082107000⟩, ⟨.privateRow 14 4, 1518040344189068700⟩, ⟨.hall 4 30, 1806279667110526608000⟩, ⟨.hall 3 31, 8484327483672704964300⟩, ⟨.hall 2 32, 24795946989319555249200⟩, ⟨.assumptionRow 18, 33155229088536984⟩]
  caps := #[0, 0, 156711977503391807640, 35116060172768494920, 0, 15282114776317569180, 0, 3281347703459960316, 0, 0, 1230151996690273800, 11759917674517558128, 129876425872684920, 21751058179194448104, 0, 101510993372739865200, 23608381395402378432] }

theorem case_51_35_18_checked :
    (Witness.linear .conditional case_51_35_18).check 51 35 18 = true := by
  change case_51_35_18.check 51 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_19 : Certificate := {
  objectiveScale := 2513510953676923200000
  eta := 575956617784445867124120966000
  rows := #[⟨.count 2, 66683958609639822337495889280⟩, ⟨.count 3, 7508794459990616436986662320⟩, ⟨.count 4, 764217199000485206260764480⟩, ⟨.count 5, 65163658115063143494658800⟩, ⟨.count 6, 4789591892403093719143200⟩, ⟨.count 7, 882293243337412000894800⟩, ⟨.count 8, 313704264297746489207040⟩, ⟨.count 9, 176458648667482400178960⟩, ⟨.path 5, 4113136384741658398924800⟩, ⟨.path 6, 2914503337201711102848000⟩, ⟨.privateRow 2 32, 3629430895567555920614212440⟩, ⟨.privateRow 2 33, 8646709062904860918635945280⟩, ⟨.privateRow 3 29, 863649546826413116352082500⟩, ⟨.privateRow 3 30, 1906537666269554288155785600⟩, ⟨.privateRow 3 31, 2615881827396314927719629360⟩, ⟨.privateRow 4 25, 13547702781368750805576480⟩, ⟨.privateRow 4 26, 131205408077066854171160520⟩, ⟨.privateRow 4 27, 407508561557007641190427968⟩, ⟨.privateRow 4 28, 657390393516110414638137660⟩, ⟨.privateRow 4 29, 990857326231882125195379200⟩, ⟨.privateRow 4 30, 1545071927732475895966973760⟩, ⟨.privateRow 5 22, 2690760981268170779448480⟩, ⟨.privateRow 5 23, 19052282310592043195512830⟩, ⟨.privateRow 5 24, 72914634267756571099798560⟩, ⟨.privateRow 5 25, 151601787118282835728353960⟩, ⟨.privateRow 5 26, 244109533449477676552331760⟩, ⟨.privateRow 5 27, 365332423687641240656225400⟩, ⟨.privateRow 5 28, 608933588173100694103279680⟩, ⟨.privateRow 5 29, 628159178085062586084682560⟩, ⟨.privateRow 6 19, 91666830476614233859200⟩, ⟨.privateRow 6 20, 2331775000248874573793400⟩, ⟨.privateRow 6 21, 11805923875133941535782800⟩, ⟨.privateRow 6 22, 31883346906556120579954350⟩, ⟨.privateRow 6 23, 59623816866080617801965600⟩, ⟨.privateRow 6 24, 97283333568941785146281400⟩, ⟨.privateRow 6 25, 144771717042478774889681040⟩, ⟨.privateRow 6 26, 242389061624969723150586900⟩, ⟨.privateRow 6 27, 281115432912886842761290800⟩, ⟨.privateRow 6 28, 162467998665989152736199600⟩, ⟨.privateRow 7 18, 1574377813435849466531760⟩, ⟨.privateRow 7 19, 6120594270923532394778784⟩, ⟨.privateRow 7 20, 14354771022553131760590000⟩, ⟨.privateRow 7 21, 26131635239275563297930630⟩, ⟨.privateRow 7 22, 42389688846223170051153840⟩, ⟨.privateRow 7 23, 63222612979720837092690240⟩, ⟨.privateRow 7 24, 106127272984300129250488800⟩, ⟨.privateRow 7 25, 131423880689702784761858280⟩, ⟨.privateRow 7 26, 12083216037325699593206880⟩, ⟨.privateRow 8 16, 929675658257384126868780⟩, ⟨.privateRow 8 17, 3293894775126338136673920⟩, ⟨.privateRow 8 18, 7244607853626082985125080⟩, ⟨.privateRow 8 19, 13049225994052093544098400⟩, ⟨.privateRow 8 20, 21015734893384188632424750⟩, ⟨.privateRow 8 21, 31266791985319143384090960⟩, ⟨.privateRow 8 22, 52744797187811730023862840⟩, ⟨.privateRow 8 23, 28405921132160944597697472⟩, ⟨.privateRow 9 14, 579146334088147364689920⟩, ⟨.privateRow 9 15, 1990061426638829290907160⟩, ⟨.privateRow 9 16, 4290262296390203406371280⟩, ⟨.privateRow 9 17, 7672029913731762576669672⟩, ⟨.privateRow 9 18, 12310713871851148684090160⟩, ⟨.privateRow 9 19, 18273273395343732996310080⟩, ⟨.privateRow 9 20, 14248335647166396344609040⟩, ⟨.privateRow 10 12, 405134652552893265717000⟩, ⟨.privateRow 10 13, 1415547401398485188248800⟩, ⟨.privateRow 10 14, 3081724257085674774553980⟩, ⟨.privateRow 10 15, 5516051523930261522477360⟩, ⟨.privateRow 10 16, 8848140811755188923259280⟩, ⟨.privateRow 10 17, 2235142883121443735600160⟩, ⟨.privateRow 11 10, 330509849885125765414560⟩, ⟨.privateRow 11 11, 1221405952511315252939400⟩, ⟨.privateRow 11 12, 2753530561624450640155200⟩, ⟨.privateRow 11 13, 3347112462819705844664400⟩, ⟨.privateRow 12 8, 329284442602712693191095⟩, ⟨.privateRow 12 9, 1306354186325615737197888⟩, ⟨.privateRow 12 10, 1016737928036446210554960⟩, ⟨.privateRow 13 6, 407782591458467731506000⟩, ⟨.privateRow 13 7, 467930523698591721903135⟩, ⟨.privateRow 14 4, 267022082110581833075040⟩, ⟨.hall 4 30, 213568634338400496098623680⟩, ⟨.hall 3 31, 780213490606922249198416095⟩, ⟨.hall 2 32, 2080878811153026899532598080⟩, ⟨.assumptionRow 19, 1621907328362296369680⟩]
  caps := #[0, 0, 0, 1552823639472643419971232, 660039240830371790329656, 0, 152017001789280809693850, 436194317389200739262244, 40758259899242076003120, 0, 59927586022171850866020, 106225933538650524155040, 1621907328362296369680, 297803565405298675702980, 0, 20782346603660016339135600, 6012494294305703239395360] }

theorem case_51_35_19_checked :
    (Witness.linear .conditional case_51_35_19).check 51 35 19 = true := by
  change case_51_35_19.check 51 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_20 : Certificate := {
  objectiveScale := 28534486780800000
  eta := 9604586608231846858426800
  rows := #[⟨.count 2, 1136162115204866577828000⟩, ⟨.count 3, 130502892309245858001600⟩, ⟨.count 4, 13448809852974466850880⟩, ⟨.count 5, 1135027088116749828000⟩, ⟨.count 6, 61910568442731808800⟩, ⟨.path 6, 62648645402318976000⟩, ⟨.privateRow 2 32, 62584552877951573108640⟩, ⟨.privateRow 2 33, 149958097360372962460800⟩, ⟨.privateRow 3 29, 14692505275268320319820⟩, ⟨.privateRow 3 30, 32640296264615679559920⟩, ⟨.privateRow 3 31, 45195097127196953336400⟩, ⟨.privateRow 4 25, 316005954374091936240⟩, ⟨.privateRow 4 26, 2232219939962941328400⟩, ⟨.privateRow 4 27, 6885831001241615623200⟩, ⟨.privateRow 4 28, 11159838558605688031080⟩, ⟨.privateRow 4 29, 17025406321751247420000⟩, ⟨.privateRow 4 30, 27017428120805701739160⟩, ⟨.privateRow 5 22, 93698120936716055760⟩, ⟨.privateRow 5 23, 347654593286130410280⟩, ⟨.privateRow 5 24, 1229432515763285845440⟩, ⟨.privateRow 5 25, 2532231420908368659480⟩, ⟨.privateRow 5 26, 4096354799053650749616⟩, ⟨.privateRow 5 27, 6219107682073776650160⟩, ⟨.privateRow 5 28, 10610681625478584009360⟩, ⟨.privateRow 5 29, 11339340990689336985360⟩, ⟨.privateRow 6 19, 17718512853980484000⟩, ⟨.privateRow 6 20, 57936062814309519840⟩, ⟨.privateRow 6 21, 210699753506745703200⟩, ⟨.privateRow 6 22, 531160193298406621950⟩, ⟨.privateRow 6 23, 982925815029050692800⟩, ⟨.privateRow 6 24, 1610884965519681251400⟩, ⟨.privateRow 6 25, 2434843294211931482880⟩, ⟨.privateRow 6 26, 4188613010953403132100⟩, ⟨.privateRow 6 27, 5070424600259370752400⟩, ⟨.privateRow 6 28, 3596163265716705684000⟩, ⟨.privateRow 7 14, 15286560109316496⟩, ⟨.privateRow 7 15, 114649200819873720⟩, ⟨.privateRow 7 16, 2434090725098857440⟩, ⟨.privateRow 7 17, 9745182069689266200⟩, ⟨.privateRow 7 18, 37563247250438626080⟩, ⟨.privateRow 7 19, 107907827811665145264⟩, ⟨.privateRow 7 20, 237476711298231765360⟩, ⟨.privateRow 7 21, 425549171143166280210⟩, ⟨.privateRow 7 22, 692317388379437449200⟩, ⟨.privateRow 7 23, 1048428725097471878160⟩, ⟨.privateRow 7 24, 1810952916470397331632⟩, ⟨.privateRow 7 25, 2345837297975436184920⟩, ⟨.privateRow 7 26, 783436205602470420000⟩, ⟨.privateRow 8 12, 33439350239129835⟩, ⟨.privateRow 8 13, 332907309047337024⟩, ⟨.privateRow 8 14, 1477700810567261280⟩, ⟨.privateRow 8 15, 7092571927643128080⟩, ⟨.privateRow 8 16, 23080582631719392780⟩, ⟨.privateRow 8 17, 58707339256188670320⟩, ⟨.privateRow 8 18, 119846631257041328640⟩, ⟨.privateRow 8 19, 210861111641232932880⟩, ⟨.privateRow 8 20, 339030425624457687120⟩, ⟨.privateRow 8 21, 510851361253175102160⟩, ⟨.privateRow 8 22, 885355098864641124720⟩, ⟨.privateRow 8 23, 816383838158083907712⟩, ⟨.privateRow 9 9, 9907955626408840⟩, ⟨.privateRow 9 10, 62944659273656160⟩, ⟨.privateRow 9 11, 256368351833328735⟩, ⟨.privateRow 9 12, 1307850142685966880⟩, ⟨.privateRow 9 13, 5439467638898453160⟩, ⟨.privateRow 9 14, 15858826205716549440⟩, ⟨.privateRow 9 15, 36931904597438951100⟩, ⟨.privateRow 9 16, 71872310113969725360⟩, ⟨.privateRow 9 17, 124037696487012267960⟩, ⟨.privateRow 9 18, 197148501054283098320⟩, ⟨.privateRow 9 19, 294600675606733846350⟩, ⟨.privateRow 9 20, 396202160433301382160⟩, ⟨.privateRow 10 7, 12068336928407760⟩, ⟨.privateRow 10 8, 63694000455485400⟩, ⟨.privateRow 10 9, 283250966731452720⟩, ⟨.privateRow 10 10, 1304134659326063565⟩, ⟨.privateRow 10 11, 4876412674871962224⟩, ⟨.privateRow 10 12, 13004495064425676240⟩, ⟨.privateRow 10 13, 28380086787565663920⟩, ⟨.privateRow 10 14, 53350094781514571040⟩, ⟨.privateRow 10 15, 90343570246060491360⟩, ⟨.privateRow 10 16, 141889850934675715872⟩, ⟨.privateRow 10 17, 93630180669563538000⟩, ⟨.privateRow 11 5, 19108200136645620⟩, ⟨.privateRow 11 6, 80455579522718400⟩, ⟨.privateRow 11 7, 382164002732912400⟩, ⟨.privateRow 11 8, 1573616481841404000⟩, ⟨.privateRow 11 9, 5302525537919159550⟩, ⟨.privateRow 11 10, 13299307295105351520⟩, ⟨.privateRow 11 11, 17060892979147875000⟩, ⟨.privateRow 11 12, 72052613130643714800⟩, ⟨.privateRow 11 13, 45318281324077862100⟩, ⟨.privateRow 12 2, 38216400273291240⟩, ⟨.privateRow 12 3, 40036228857733680⟩, ⟨.privateRow 12 4, 168152161202481456⟩, ⟨.privateRow 12 5, 619507962324931680⟩, ⟨.privateRow 12 6, 2335446683367798000⟩, ⟨.privateRow 12 7, 6676629930098528400⟩, ⟨.privateRow 12 8, 18812023034527612890⟩, ⟨.privateRow 12 9, 26343838588388761440⟩, ⟨.privateRow 13 2, 720652119439206240⟩, ⟨.privateRow 13 3, 1135027088116749828⟩, ⟨.privateRow 13 4, 4646309717436987600⟩, ⟨.privateRow 13 5, 12331158488181973440⟩, ⟨.privateRow 14 0, 1987252814211144480⟩, ⟨.privateRow 14 1, 4163767801204302720⟩, ⟨.privateRow 15 0, 3643296826053764880⟩, ⟨.hall 4 30, 4095210279504820956480⟩, ⟨.hall 3 31, 13997090993595307948350⟩, ⟨.hall 2 32, 36441579689399230426080⟩, ⟨.assumptionRow 20, 3694234879022688⟩]
  caps := #[0, 483987330906029430480, 43351407097686848160, 18299997197958916440, 17814975823971148680, 2521441413877736064, 2318614204397320944, 0, 1016079281730303777, 0, 917868397761163629, 3174445323910119996, 0, 200909075722445376, 41064890639599775520, 0, 210460200731442645984] }

theorem case_51_35_20_checked :
    (Witness.linear .conditional case_51_35_20).check 51 35 20 = true := by
  change case_51_35_20.check 51 35 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_21 : Certificate := {
  objectiveScale := 491427272336000000
  eta := 140229948340285502166468000
  rows := #[⟨.count 2, 17223758611105694545497600⟩, ⟨.count 3, 1995907300217034014210400⟩, ⟨.count 4, 206120919202001768764800⟩, ⟨.count 5, 17277634563554969604000⟩, ⟨.count 6, 963053286886939248000⟩, ⟨.path 6, 932473630507491072000⟩, ⟨.privateRow 3 29, 267973589798319541336200⟩, ⟨.privateRow 3 32, 6055596520520483682345600⟩, ⟨.privateRow 4 25, 1199885778866278389600⟩, ⟨.privateRow 4 26, 34555269127109939208000⟩, ⟨.privateRow 4 27, 121992711430788271513440⟩, ⟨.privateRow 4 28, 170916162352247244933000⟩, ⟨.privateRow 4 30, 1094922797669958000744000⟩, ⟨.privateRow 5 22, 367132218625417845600⟩, ⟨.privateRow 5 23, 4051416133972287580500⟩, ⟨.privateRow 5 24, 18600031202725913054400⟩, ⟨.privateRow 5 25, 43681727676374620232400⟩, ⟨.privateRow 5 26, 74528400888163830928320⟩, ⟨.privateRow 6 19, 78169909649913900000⟩, ⟨.privateRow 6 20, 445985391189308770800⟩, ⟨.privateRow 6 21, 2504448097909685928000⟩, ⟨.privateRow 6 22, 7794712540741164538500⟩, ⟨.privateRow 6 23, 16031233966070342448000⟩, ⟨.privateRow 6 24, 28089054200869061400000⟩, ⟨.privateRow 6 25, 44605418070980069503200⟩, ⟨.privateRow 6 26, 35506857493914891084000⟩, ⟨.privateRow 7 15, 491353717799458800⟩, ⟨.privateRow 7 16, 12170453625494287200⟩, ⟨.privateRow 7 17, 51592140368943174000⟩, ⟨.privateRow 7 18, 300797812332868687200⟩, ⟨.privateRow 7 19, 1251969272953021022400⟩, ⟨.privateRow 7 20, 3286610423503046640000⟩, ⟨.privateRow 7 21, 6489431389406902236300⟩, ⟨.privateRow 7 22, 11451489747034186792800⟩, ⟨.privateRow 7 23, 18956098863557920864800⟩, ⟨.privateRow 7 24, 36446063747031296598240⟩, ⟨.privateRow 7 26, 113174812097330143960800⟩, ⟨.privateRow 8 13, 1783432012753591200⟩, ⟨.privateRow 8 14, 7261116051925335600⟩, ⟨.privateRow 8 15, 38686755968962516800⟩, ⟨.privateRow 8 16, 186368645332750280400⟩, ⟨.privateRow 8 17, 659545584352873545600⟩, ⟨.privateRow 8 18, 1586362775344319372400⟩, ⟨.privateRow 8 19, 3099604838165741505600⟩, ⟨.privateRow 8 20, 5476696782164684376300⟩, ⟨.privateRow 8 21, 9151299209442320330400⟩, ⟨.privateRow 8 22, 17952918356384025814800⟩, ⟨.privateRow 8 23, 29318552230461387173280⟩, ⟨.privateRow 8 24, 17539607987428381054200⟩, ⟨.privateRow 9 10, 314723296368280800⟩, ⟨.privateRow 9 11, 1337574009565193400⟩, ⟨.privateRow 9 12, 6420355245912928320⟩, ⟨.privateRow 9 13, 29808792213167167200⟩, ⟨.privateRow 9 14, 125526176282271996000⟩, ⟨.privateRow 9 15, 393246758812166859600⟩, ⟨.privateRow 9 16, 897876953329944369600⟩, ⟨.privateRow 9 17, 1724400413131447331280⟩, ⟨.privateRow 9 18, 3001516077464293989600⟩, ⟨.privateRow 9 19, 4919597207180781325200⟩, ⟨.privateRow 9 20, 1602031499456368780800⟩, ⟨.privateRow 9 21, 31870821783913051539600⟩, ⟨.privateRow 9 22, 16055168351612929418880⟩, ⟨.privateRow 10 8, 382164002732912400⟩, ⟨.privateRow 10 9, 1618576952751158400⟩, ⟨.privateRow 10 10, 6449017546117896750⟩, ⟨.privateRow 10 11, 26598614590210703040⟩, ⟨.privateRow 10 12, 98762097277691218800⟩, ⟨.privateRow 10 13, 282037034016889351200⟩, ⟨.privateRow 10 14, 623691652460113036800⟩, ⟨.privateRow 10 15, 1176300800411904367200⟩, ⟨.privateRow 10 16, 2011405579183864543680⟩, ⟨.privateRow 10 17, 1016556247269546984000⟩, ⟨.privateRow 10 18, 10443968948686396523400⟩, ⟨.privateRow 10 20, 28184213037549556587600⟩, ⟨.privateRow 11 6, 603416846420388000⟩, ⟨.privateRow 11 7, 1910820013664562000⟩, ⟨.privateRow 11 8, 8092884763755792000⟩, ⟨.privateRow 11 9, 28662300204968430000⟩, ⟨.privateRow 11 10, 95541000683228100000⟩, ⟨.privateRow 11 11, 254685010392719478000⟩, ⟨.privateRow 11 12, 550316163935393856000⟩, ⟨.privateRow 11 13, 1028021167351534356000⟩, ⟨.privateRow 11 14, 1743710117924079396000⟩, ⟨.privateRow 11 15, 2768778199799950338000⟩, ⟨.privateRow 11 16, 1703177572179679596000⟩, ⟨.privateRow 11 18, 30747277814164133508000⟩, ⟨.privateRow 11 19, 14566180964164956126000⟩, ⟨.privateRow 12 4, 1261141209018610920⟩, ⟨.privateRow 12 5, 2655034124249707200⟩, ⟨.privateRow 12 6, 11210144080165430400⟩, ⟨.privateRow 12 7, 38576084040569275200⟩, ⟨.privateRow 12 8, 118231988345494773750⟩, ⟨.privateRow 12 9, 299310846940416991680⟩, ⟨.privateRow 12 10, 635975495405099506800⟩, ⟨.privateRow 12 11, 1185472736477494264800⟩, ⟨.privateRow 12 12, 2005214522339591362800⟩, ⟨.privateRow 12 14, 11925351272479984859520⟩, ⟨.privateRow 12 16, 485539365472165204200⟩, ⟨.privateRow 12 17, 43210301081574806150400⟩, ⟨.privateRow 12 21, 90129558404530060416000⟩, ⟨.privateRow 13 3, 11350270881167498280⟩, ⟨.privateRow 13 4, 19912755931872804000⟩, ⟨.privateRow 13 5, 71464668511054618800⟩, ⟨.privateRow 13 6, 195847811282890166400⟩, ⟨.privateRow 13 7, 477657232915798885950⟩, ⟨.privateRow 13 8, 1003868402378814292320⟩, ⟨.privateRow 13 9, 1864687359048946146000⟩, ⟨.privateRow 13 10, 3172255194992967468000⟩, ⟨.privateRow 13 12, 1919227621724686072800⟩, ⟨.privateRow 13 14, 1135027088116749828000⟩, ⟨.privateRow 13 15, 111875836652040974713200⟩, ⟨.privateRow 13 20, 230864509722946915015200⟩, ⟨.privateRow 14 1, 31228258509032270400⟩, ⟨.privateRow 14 2, 65579342868967767840⟩, ⟨.privateRow 14 3, 172577218076230968000⟩, ⟨.privateRow 14 4, 473628587386989434400⟩, ⟨.privateRow 14 5, 1099418395156224343200⟩, ⟨.privateRow 14 6, 2274783455767319446950⟩, ⟨.privateRow 14 7, 4240797505526582320320⟩, ⟨.privateRow 14 9, 22549204817252763249600⟩, ⟨.privateRow 14 12, 7508834758496809417680⟩, ⟨.privateRow 14 16, 54266906224070827887600⟩, ⟨.privateRow 14 19, 1742880335647600043294400⟩, ⟨.privateRow 15 3, 11603900390981241142800⟩, ⟨.privateRow 15 9, 7842196418080728904200⟩, ⟨.privateRow 15 11, 392721894770813477709840⟩, ⟨.privateRow 15 16, 189130824834103042450560⟩, ⟨.privateRow 15 19, 12628614056277123052948800⟩, ⟨.privateRow 16 4, 256066840358672580987750⟩, ⟨.privateRow 16 9, 15649615911912762780000⟩, ⟨.privateRow 16 10, 3928366586208341713035600⟩, ⟨.privateRow 16 11, 1572264745283502233964000⟩, ⟨.privateRow 16 18, 34136507188655309452014000⟩, ⟨.privateRow 16 19, 145291034126198089649520000⟩, ⟨.hall 9 13, 7390478452942728⟩, ⟨.hall 6 15, 2384788806560160⟩, ⟨.hall 10 15, 18557768742212700⟩, ⟨.hall 8 17, 3406925005205120⟩, ⟨.hall 5 20, 40267091669737680⟩, ⟨.hall 12 20, 66368357244796464000⟩, ⟨.hall 6 25, 11994215053563270000⟩, ⟨.hall 3 28, 131981618954554604235⟩, ⟨.hall 5 28, 1160394871056779358000⟩, ⟨.hall 4 30, 1033006459783572030556800⟩]
  caps := #[0, 0, 2383149366818628408000, 275320999153876275600, 0, 47205452763232764000, 0, 8558706906700104100, 49487432254591389660, 5705629499938335660, 11341673657386645430, 874954427309562600, 273135505308825843970, 97999903204350340050, 2165514849614135203470, 20246031981000567992250, 0] }

theorem case_51_35_21_checked :
    (Witness.linear .conditional case_51_35_21).check 51 35 21 = true := by
  change case_51_35_21.check 51 35 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_35_22 : Certificate := {
  objectiveScale := 985
  eta := 14692860
  rows := #[⟨.assumptionRow 22, 383⟩]
  caps := #[0, 0, 7607710, 3871406, 1595902, 916237, 432972, 206397, 115260, 49180, 28714, 29716, 79698312, 78947660, 55681970, 32878170, 16969128] }

theorem case_51_35_22_checked :
    (Witness.linear .conditional case_51_35_22).check 51 35 22 = true := by
  change case_51_35_22.check 51 35 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_36_1_checked :
    (Witness.rising).check 51 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_36_2_checked :
    (Witness.rising).check 51 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_36_3_checked :
    (Witness.rising).check 51 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_36_4_checked :
    (Witness.rising).check 51 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_36_5_checked :
    (Witness.rising).check 51 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_36_6_checked :
    (Witness.rising).check 51 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_36_7_checked :
    (Witness.rising).check 51 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_36_8_checked :
    (Witness.rising).check 51 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_36_9_checked :
    (Witness.rising).check 51 36 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_51_36_10_checked :
    (Witness.linear .positive case_51_36_10).check 51 36 10 = true := by
  change case_51_36_10.check 51 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_51_36_11_checked :
    (Witness.linear .positive case_51_36_11).check 51 36 11 = true := by
  change case_51_36_11.check 51 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_51_36_12_checked :
    (Witness.linear .positive case_51_36_12).check 51 36 12 = true := by
  change case_51_36_12.check 51 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_51_36_13_checked :
    (Witness.linear .positive case_51_36_13).check 51 36 13 = true := by
  change case_51_36_13.check 51 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_51_36_14_checked :
    (Witness.linear .positive case_51_36_14).check 51 36 14 = true := by
  change case_51_36_14.check 51 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_51_36_15_checked :
    (Witness.linear .positive case_51_36_15).check 51 36 15 = true := by
  change case_51_36_15.check 51 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_51_36_16_checked :
    (Witness.linear .positive case_51_36_16).check 51 36 16 = true := by
  change case_51_36_16.check 51 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_17 : Certificate := {
  objectiveScale := 5
  eta := 46527390
  rows := #[⟨.assumptionRow 17, 13⟩]
  caps := #[0, 0, 13037895, 3714500, 1069776, 312018, 92378, 27846, 8580, 2717, 891, 306, 46046, 31878, 11858, 3143] }

theorem case_51_36_17_checked :
    (Witness.linear .conditional case_51_36_17).check 51 36 17 = true := by
  change case_51_36_17.check 51 36 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_18 : Certificate := {
  objectiveScale := 275917970582654400000
  eta := 112434289857610960257026648640
  rows := #[⟨.count 2, 11932599378551977997333542080⟩, ⟨.count 3, 1175088103559663280809421600⟩, ⟨.count 4, 105883128966106645698504960⟩, ⟨.count 5, 8129847125776001666040000⟩, ⟨.count 6, 780465324074496159939840⟩, ⟨.count 7, 151757146347818697766080⟩, ⟨.count 8, 75878573173909348883040⟩, ⟨.path 5, 2530133460869659048404000⟩, ⟨.path 6, 188229109902140138832000⟩, ⟨.privateRow 2 33, 968419259775311542457018760⟩, ⟨.privateRow 2 34, 1492737490457983217904936480⟩, ⟨.privateRow 3 29, 73832019657447336730308864⟩, ⟨.privateRow 3 30, 190124604883397574962011440⟩, ⟨.privateRow 3 31, 390384419183595898667686080⟩, ⟨.privateRow 3 32, 462702119316415358821000560⟩, ⟨.privateRow 3 33, 681086072809010315574167040⟩, ⟨.privateRow 4 25, 614819688886810125994275⟩, ⟨.privateRow 4 26, 22638140025089403496350240⟩, ⟨.privateRow 4 27, 39363364808486437400021340⟩, ⟨.privateRow 4 28, 91324198733266981914960528⟩, ⟨.privateRow 4 29, 128597921835524794353420720⟩, ⟨.privateRow 4 30, 168810855668654823927543240⟩, ⟨.privateRow 4 31, 230590918951947623254725540⟩, ⟨.privateRow 5 22, 292674496527936059977440⟩, ⟨.privateRow 5 23, 4393730713308274678179840⟩, ⟨.privateRow 5 24, 9316804806139297909281840⟩, ⟨.privateRow 5 25, 21049335615366322027901280⟩, ⟨.privateRow 5 26, 34849944679159793808424800⟩, ⟨.privateRow 5 27, 48824609898560355605569824⟩, ⟨.privateRow 5 28, 63120133084524876935134560⟩, ⟨.privateRow 5 29, 89894429618747175755292960⟩, ⟨.privateRow 5 30, 63494106052310573011772400⟩, ⟨.privateRow 6 20, 739077011434181969640000⟩, ⟨.privateRow 6 21, 2022705964893069214510752⟩, ⟨.privateRow 6 22, 5347632776065992206995200⟩, ⟨.privateRow 6 23, 9526148369628029952182370⟩, ⟨.privateRow 6 24, 14701086416867518441247760⟩, ⟨.privateRow 6 25, 20579353024380985550635920⟩, ⟨.privateRow 6 26, 26295177543609899788639776⟩, ⟨.privateRow 6 27, 37246894606742751632962260⟩, ⟨.privateRow 6 28, 8373742539549281716021200⟩, ⟨.privateRow 7 17, 59201963685138063414240⟩, ⟨.privateRow 7 18, 399265825510332526265520⟩, ⟨.privateRow 7 19, 1343149288779720032825760⟩, ⟨.privateRow 7 20, 2892057617542716325999296⟩, ⟨.privateRow 7 21, 4788781062531167796174080⟩, ⟨.privateRow 7 22, 7150200547119993465282180⟩, ⟨.privateRow 7 23, 9752719466311858760518080⟩, ⟨.privateRow 7 24, 12823478866390679961233760⟩, ⟨.privateRow 7 25, 6000911158439459363092992⟩, ⟨.privateRow 8 15, 33196875763585340136330⟩, ⟨.privateRow 8 16, 320295130993713501535140⟩, ⟨.privateRow 8 17, 909752476283017297545615⟩, ⟨.privateRow 8 18, 1781421956560189940822280⟩, ⟨.privateRow 8 19, 2851137387009643784280228⟩, ⟨.privateRow 8 20, 4151190274055957295142980⟩, ⟨.privateRow 8 21, 5633984058162769154565720⟩, ⟨.privateRow 9 13, 28183470036023472442272⟩, ⟨.privateRow 9 14, 280286158050563105057760⟩, ⟨.privateRow 9 15, 718761868966042403705280⟩, ⟨.privateRow 9 16, 1334198244974572717860120⟩, ⟨.privateRow 9 17, 2097007840442585641858560⟩, ⟨.privateRow 9 18, 949566144290636994593472⟩, ⟨.privateRow 10 11, 30486926721660006247650⟩, ⟨.privateRow 10 12, 286170618827315258644608⟩, ⟨.privateRow 10 13, 700328259548989857803160⟩, ⟨.privateRow 10 14, 796725018326048163271920⟩, ⟨.privateRow 11 9, 42083914533428714506560⟩, ⟨.privateRow 11 10, 355680811752700072889250⟩, ⟨.privateRow 11 11, 192948371785083772874016⟩, ⟨.privateRow 12 7, 74523598652946681938700⟩, ⟨.privateRow 12 8, 110470275650250375579720⟩, ⟨.privateRow 13 5, 56481043189601695785120⟩, ⟨.hall 3 32, 65363970891239053394961600⟩, ⟨.assumptionRow 18, 270427597136588981232⟩]
  caps := #[0, 6071971072528718279928720, 0, 1371420518520897920403900, 128059113568072458039840, 241479675144710055658176, 30474124930108639555776, 3185806464057449601048, 31261822263622520743971, 17606644979387994335520, 8698240350781055585082, 169204680360155174223060, 75958383948218751015036, 0, 3685964509047702666985200, 981519244269276573020160] }

theorem case_51_36_18_checked :
    (Witness.linear .conditional case_51_36_18).check 51 36 18 = true := by
  change case_51_36_18.check 51 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_19 : Certificate := {
  objectiveScale := 23673048439040000
  eta := 10449611432028810630388800
  rows := #[⟨.count 2, 1061033013356063797969920⟩, ⟨.count 3, 96498047822020246321920⟩, ⟨.count 4, 7506888761777659974720⟩, ⟨.count 5, 415136821193531236800⟩, ⟨.count 6, 24300691972304267520⟩, ⟨.count 7, 4725134550170274240⟩, ⟨.path 5, 327072603268475064000⟩, ⟨.privateRow 2 33, 91725493171542906115440⟩, ⟨.privateRow 2 34, 147397872215675893331520⟩, ⟨.privateRow 3 29, 6001055882560538864064⟩, ⟨.privateRow 3 30, 16923913165461653310960⟩, ⟨.privateRow 3 31, 36821623511034041359680⟩, ⟨.privateRow 3 32, 46132838651755293197760⟩, ⟨.privateRow 3 33, 71237478516809960234880⟩, ⟨.privateRow 4 25, 28540656457055272530⟩, ⟨.privateRow 4 26, 1750228409910009744000⟩, ⟨.privateRow 4 27, 3215116551780145172160⟩, ⟨.privateRow 4 28, 8069348528053285833360⟩, ⟨.privateRow 4 29, 12161104104994039295100⟩, ⟨.privateRow 4 30, 16975889645513526327600⟩, ⟨.privateRow 4 31, 24748229716127537780160⟩, ⟨.privateRow 5 22, 18023013212792331744⟩, ⟨.privateRow 5 23, 310058829054030376320⟩, ⟨.privateRow 5 24, 695607307707209657760⟩, ⟨.privateRow 5 25, 1701916319917452450240⟩, ⟨.privateRow 5 26, 3065937303839055085440⟩, ⟨.privateRow 5 27, 4602956071087300006080⟩, ⟨.privateRow 5 28, 6404244863534353836000⟩, ⟨.privateRow 5 29, 9881606382848949228480⟩, ⟨.privateRow 5 30, 8601432429363531357600⟩, ⟨.privateRow 6 19, 168754805363224080⟩, ⟨.privateRow 6 20, 46208133977639175360⟩, ⟨.privateRow 6 21, 135273851979160422528⟩, ⟨.privateRow 6 22, 390948632424802452000⟩, ⟨.privateRow 6 23, 762434210631046393440⟩, ⟨.privateRow 6 24, 1275786328545974044800⟩, ⟨.privateRow 6 25, 1924648555167570632400⟩, ⟨.privateRow 6 26, 2662140805565932506816⟩, ⟨.privateRow 6 27, 4134661486204353184080⟩, ⟨.privateRow 6 28, 3190815859807840904640⟩, ⟨.privateRow 7 17, 3427020662760858240⟩, ⟨.privateRow 7 18, 23288163140124923040⟩, ⟨.privateRow 7 19, 87138844951192070400⟩, ⟨.privateRow 7 20, 207838418285346776928⟩, ⟨.privateRow 7 21, 375835702077829273280⟩, ⟨.privateRow 7 22, 607601676710288300040⟩, ⟨.privateRow 7 23, 906454383093889344000⟩, ⟨.privateRow 7 24, 1254073210255905879840⟩, ⟨.privateRow 7 25, 1956880722991946431680⟩, ⟨.privateRow 7 26, 128759916492139973040⟩, ⟨.privateRow 8 15, 1729736754973046820⟩, ⟨.privateRow 8 16, 17991858479494505760⟩, ⟨.privateRow 8 17, 57833678088021585750⟩, ⟨.privateRow 8 18, 125269760290309656840⟩, ⟨.privateRow 8 19, 217710574399095385608⟩, ⟨.privateRow 8 20, 342506628018592517480⟩, ⟨.privateRow 8 21, 503005338911094974955⟩, ⟨.privateRow 8 22, 693244740432124520640⟩, ⟨.privateRow 8 23, 119014326482413782420⟩, ⟨.privateRow 9 13, 1350038442905792640⟩, ⟨.privateRow 9 14, 15429010776066201600⟩, ⟨.privateRow 9 15, 44810891393373040320⟩, ⟨.privateRow 9 16, 91352601303291968640⟩, ⟨.privateRow 9 17, 155070324782860818240⟩, ⟨.privateRow 9 18, 238754298627889428384⟩, ⟨.privateRow 9 19, 207305903121756158720⟩, ⟨.privateRow 10 11, 1455510196257807690⟩, ⟨.privateRow 10 12, 15660445937707194624⟩, ⟨.privateRow 10 13, 42743181415570899120⟩, ⟨.privateRow 10 14, 84351440403863851680⟩, ⟨.privateRow 10 15, 123022253109790354320⟩, ⟨.privateRow 11 9, 1905936625278766080⟩, ⟨.privateRow 11 10, 17845820667160946460⟩, ⟨.privateRow 11 11, 55081568470556339712⟩, ⟨.privateRow 11 12, 18804106883330683200⟩, ⟨.privateRow 12 7, 3403221908158352280⟩, ⟨.privateRow 12 8, 28172125742401761120⟩, ⟨.privateRow 13 5, 8206812639769423680⟩, ⟨.privateRow 13 6, 2475070478660619840⟩, ⟨.hall 4 31, 776166632917478752950⟩, ⟨.hall 3 32, 8073904907798092883520⟩, ⟨.assumptionRow 19, 17247514901801184⟩]
  caps := #[0, 1260646801316465122560, 153711432068367853680, 42575695161038047008, 0, 0, 14143566233663215440, 0, 3299341334666083511, 7571714764852675072, 114307070775369472, 11213262985080939640, 36077836572051362088, 0, 814880619671055441504, 259752485910486048480] }

theorem case_51_36_19_checked :
    (Witness.linear .conditional case_51_36_19).check 51 36 19 = true := by
  change case_51_36_19.check 51 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_20 : Certificate := {
  objectiveScale := 7861069216000000
  eta := 4673733469567655829336000
  rows := #[⟨.count 2, 469591928276952098217600⟩, ⟨.count 3, 42047056178368888046400⟩, ⟨.count 4, 3114995958869163969600⟩, ⟨.count 5, 148613102787613464000⟩, ⟨.path 5, 147659340611646864000⟩, ⟨.privateRow 2 33, 41207228836516907564400⟩, ⟨.privateRow 2 34, 67234690745441868448800⟩, ⟨.privateRow 3 29, 2685291787380407325120⟩, ⟨.privateRow 3 30, 7405750196331100614000⟩, ⟨.privateRow 3 31, 16426483879988255673600⟩, ⟨.privateRow 3 32, 21028917355549269566400⟩, ⟨.privateRow 3 33, 33194287963082129083200⟩, ⟨.privateRow 4 25, 59057377247879910900⟩, ⟨.privateRow 4 26, 759244978111255693200⟩, ⟨.privateRow 4 27, 1378454574647600049600⟩, ⟨.privateRow 4 28, 3494939237589364765200⟩, ⟨.privateRow 4 29, 5381407018043505949500⟩, ⟨.privateRow 4 30, 7707549112761331033200⟩, ⟨.privateRow 4 31, 11590964634148537037400⟩, ⟨.privateRow 5 22, 30931122712059329760⟩, ⟨.privateRow 5 23, 139431389721614390400⟩, ⟨.privateRow 5 24, 295103161249689592800⟩, ⟨.privateRow 5 25, 717915604235548118400⟩, ⟨.privateRow 5 26, 1310898215468322280800⟩, ⟨.privateRow 5 27, 2013364589458037175360⟩, ⟨.privateRow 5 28, 2889708293709259822800⟩, ⟨.privateRow 5 29, 4639559532740923190400⟩, ⟨.privateRow 5 30, 4324641291119551802400⟩, ⟨.privateRow 6 18, 339184596387621600⟩, ⟨.privateRow 6 19, 7934197703770938600⟩, ⟨.privateRow 6 20, 26322780343899967200⟩, ⟨.privateRow 6 21, 59820856649563529520⟩, ⟨.privateRow 6 22, 163311101964410400000⟩, ⟨.privateRow 6 23, 316578571158009560400⟩, ⟨.privateRow 6 24, 537363515935180677600⟩, ⟨.privateRow 6 25, 830409734972032815600⟩, ⟨.privateRow 6 26, 1187990280129907013760⟩, ⟨.privateRow 6 27, 1931235436280135185200⟩, ⟨.privateRow 6 28, 1986788429465028789600⟩, ⟨.privateRow 7 15, 94357525579437120⟩, ⟨.privateRow 7 16, 1889742751302463200⟩, ⟨.privateRow 7 17, 5946199097165712000⟩, ⟨.privateRow 7 18, 13255417776111310800⟩, ⟨.privateRow 7 19, 38165309646955545600⟩, ⟨.privateRow 7 20, 85683891497327323200⟩, ⟨.privateRow 7 21, 153972126355778931200⟩, ⟨.privateRow 7 22, 251934593297097110400⟩, ⟨.privateRow 7 23, 384900937172691825600⟩, ⟨.privateRow 7 24, 550757618535976051200⟩, ⟨.privateRow 7 25, 901215985080402351360⟩, ⟨.privateRow 7 26, 438408653223459718800⟩, ⟨.privateRow 8 12, 33622873933849200⟩, ⟨.privateRow 8 13, 500140249766006850⟩, ⟨.privateRow 8 14, 1683011634133229400⟩, ⟨.privateRow 8 15, 3776569232926990500⟩, ⟨.privateRow 8 16, 10310583610560756600⟩, ⟨.privateRow 8 17, 25189603373135551350⟩, ⟨.privateRow 8 18, 51417015807113119800⟩, ⟨.privateRow 8 19, 88348584311046619560⟩, ⟨.privateRow 8 20, 140071024870974997800⟩, ⟨.privateRow 8 21, 209927915788688922825⟩, ⟨.privateRow 8 22, 298328555513486698200⟩, ⟨.privateRow 8 23, 257564289895370257800⟩, ⟨.privateRow 9 9, 11460428208028800⟩, ⟨.privateRow 9 10, 163311101964410400⟩, ⟨.privateRow 9 11, 595605195399614400⟩, ⟨.privateRow 9 12, 1435776771437108100⟩, ⟨.privateRow 9 13, 3781559294375903040⟩, ⟨.privateRow 9 14, 8912120135772110400⟩, ⟨.privateRow 9 15, 19815080371681795200⟩, ⟨.privateRow 9 16, 37679500358788688400⟩, ⟨.privateRow 9 17, 62721360796876891200⟩, ⟨.privateRow 9 18, 96658397549335702080⟩, ⟨.privateRow 9 19, 141657259555795984000⟩, ⟨.privateRow 9 20, 28647489136256991000⟩, ⟨.privateRow 10 6, 7776719141162400⟩, ⟨.privateRow 10 7, 65324440785764160⟩, ⟨.privateRow 10 8, 257859634680648000⟩, ⟨.privateRow 10 9, 698608602847755600⟩, ⟨.privateRow 10 10, 1911700546524568800⟩, ⟨.privateRow 10 11, 4409399753039080800⟩, ⟨.privateRow 10 12, 9548255761519194720⟩, ⟨.privateRow 10 13, 19562336999594017200⟩, ⟨.privateRow 10 14, 35338009986606650400⟩, ⟨.privateRow 10 15, 57363024564999153000⟩, ⟨.privateRow 10 16, 17325823272042448800⟩, ⟨.privateRow 11 4, 44539391444839200⟩, ⟨.privateRow 11 5, 139980944540923200⟩, ⟨.privateRow 11 6, 424608865107467040⟩, ⟨.privateRow 11 7, 1254916888779153600⟩, ⟨.privateRow 11 8, 3066619581331706400⟩, ⟨.privateRow 11 9, 3266222039288208000⟩, ⟨.privateRow 11 10, 19821885000930312300⟩, ⟨.privateRow 11 11, 22014336544802521920⟩, ⟨.privateRow 11 12, 2029723695843386400⟩, ⟨.privateRow 12 2, 156210619270305600⟩, ⟨.privateRow 12 3, 285794428437718200⟩, ⟨.privateRow 12 4, 1026526926633436800⟩, ⟨.privateRow 12 5, 2829364841533410180⟩, ⟨.privateRow 12 6, 6429300224704156800⟩, ⟨.privateRow 12 7, 7235589100923183000⟩, ⟨.privateRow 13 1, 2343159289054584000⟩, ⟨.privateRow 13 2, 2776288733394976800⟩, ⟨.privateRow 13 3, 855439105527864000⟩, ⟨.privateRow 14 0, 2030738050513972800⟩, ⟨.hall 4 31, 583275807609764519250⟩, ⟨.hall 3 32, 4004061597963414187200⟩, ⟨.assumptionRow 20, 2575818581848512⟩]
  caps := #[0, 31823988359768404800, 35877026358101008080, 3618024550330590400, 2073235524585156360, 0, 1309738179132657000, 365328149640265920, 802757927724154395, 73859546472451168, 4125736091364668200, 0, 5184707093371195676, 0, 2264228038214093952, 229609104350967973632] }

theorem case_51_36_20_checked :
    (Witness.linear .conditional case_51_36_20).check 51 36 20 = true := by
  change case_51_36_20.check 51 36 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_21 : Certificate := {
  objectiveScale := 7914482373798000000
  eta := 6296362184530228763387635200
  rows := #[⟨.count 2, 632216694758158215995889600⟩, ⟨.count 3, 55475016924164589390038400⟩, ⟨.count 4, 4044586921293678699139200⟩, ⟨.count 5, 186558437329044220440000⟩, ⟨.path 4, 62989718658419888054720⟩, ⟨.path 5, 187707348096753925440000⟩, ⟨.privateRow 2 34, 242914010077401898550515200⟩, ⟨.privateRow 3 29, 2865537597374119225958400⟩, ⟨.privateRow 3 30, 10107736134487615863439200⟩, ⟨.privateRow 3 33, 205915740786305848752854400⟩, ⟨.privateRow 4 26, 857369275553621795936400⟩, ⟨.privateRow 4 27, 1665655914619483148161800⟩, ⟨.privateRow 4 28, 4703884438814520974174160⟩, ⟨.privateRow 4 30, 22286892784785386054497200⟩, ⟨.privateRow 4 31, 11024670853959868206901800⟩, ⟨.privateRow 4 32, 40462659472296400971231600⟩, ⟨.privateRow 5 22, 17706091688320196921760⟩, ⟨.privateRow 5 23, 146985435471368173680000⟩, ⟨.privateRow 5 24, 332243617025088752583600⟩, ⟨.privateRow 5 25, 865824976154639514499200⟩, ⟨.privateRow 5 26, 1737254781551978452764000⟩, ⟨.privateRow 5 28, 7456571141462507450786400⟩, ⟨.privateRow 5 29, 8964754775118338272876800⟩, ⟨.privateRow 6 17, 72685105452874371600⟩, ⟨.privateRow 6 18, 443565515327797447200⟩, ⟨.privateRow 6 19, 5314088820887926279200⟩, ⟨.privateRow 6 20, 24360523221478501512000⟩, ⟨.privateRow 6 21, 62480116647290809827360⟩, ⟨.privateRow 6 22, 181998119972112028384800⟩, ⟨.privateRow 6 23, 377865634881009566491200⟩, ⟨.privateRow 6 24, 692737511702861344262400⟩, ⟨.privateRow 6 25, 864839689169611661906400⟩, ⟨.privateRow 6 26, 940729400160674983578720⟩, ⟨.privateRow 6 27, 4511322211775069330640000⟩, ⟨.privateRow 6 28, 4806084542754959198935200⟩, ⟨.privateRow 6 29, 3013088361443454200306400⟩, ⟨.privateRow 7 14, 42399644847510050100⟩, ⟨.privateRow 7 15, 165829722070261529280⟩, ⟨.privateRow 7 16, 1356788635120321603200⟩, ⟨.privateRow 7 17, 4870523305560128832000⟩, ⟨.privateRow 7 18, 12324163435676254562400⟩, ⟨.privateRow 7 19, 39552444454113617644800⟩, ⟨.privateRow 7 20, 94522941580049071689600⟩, ⟨.privateRow 7 21, 180251882747281244099200⟩, ⟨.privateRow 7 22, 314605364768524571742000⟩, ⟨.privateRow 7 23, 483242885542021211006400⟩, ⟨.privateRow 7 24, 671836505823745913851200⟩, ⟨.privateRow 7 25, 992988375756726037328640⟩, ⟨.privateRow 7 26, 2658344666219286781136400⟩, ⟨.privateRow 8 11, 21985001032042248200⟩, ⟨.privateRow 8 12, 69834709160604788400⟩, ⟨.privateRow 8 13, 395730018576760467600⟩, ⟨.privateRow 8 14, 1292718060684084194160⟩, ⟨.privateRow 8 15, 3123440503766573690700⟩, ⟨.privateRow 8 16, 9588842757821503638000⟩, ⟨.privateRow 8 17, 25969782469099905686250⟩, ⟨.privateRow 8 18, 55977809900494480689600⟩, ⟨.privateRow 8 19, 101109019746362299471800⟩, ⟨.privateRow 8 20, 169262522945693268891800⟩, ⟨.privateRow 8 21, 265633774969650463876500⟩, ⟨.privateRow 8 22, 391490054092009462590000⟩, ⟨.privateRow 8 23, 651503520583539983158800⟩, ⟨.privateRow 8 24, 826402997793848884489080⟩, ⟨.privateRow 8 25, 952917884732839205980800⟩, ⟨.privateRow 9 8, 11306571959336013360⟩, ⟨.privateRow 9 9, 35704964082113726400⟩, ⟨.privateRow 9 10, 150754292791146844800⟩, ⟨.privateRow 9 11, 465564727737365256000⟩, ⟨.privateRow 9 12, 1116523980984431319300⟩, ⟨.privateRow 9 13, 3135689290055854371840⟩, ⟨.privateRow 9 14, 8286102021627678362400⟩, ⟨.privateRow 9 15, 20230066444165820827200⟩, ⟨.privateRow 9 16, 40439839041225141117600⟩, ⟨.privateRow 9 17, 70203533165695428408000⟩, ⟨.privateRow 9 18, 113133559025116149680160⟩, ⟨.privateRow 9 19, 173844825303657503195200⟩, ⟨.privateRow 9 20, 256178654168655722704200⟩, ⟨.privateRow 9 21, 438953427952736427244800⟩, ⟨.privateRow 9 22, 624914232192501458407200⟩, ⟨.privateRow 9 23, 749806626055327061981760⟩, ⟨.privateRow 10 5, 15418052671821836400⟩, ⟨.privateRow 10 6, 32304491312388609600⟩, ⟨.privateRow 10 7, 84799289695020100200⟩, ⟨.privateRow 10 8, 232082266533739221600⟩, ⟨.privateRow 10 9, 546484311367907312400⟩, ⟨.privateRow 10 10, 1476505279395644097600⟩, ⟨.privateRow 10 11, 3646369456885864308600⟩, ⟨.privateRow 10 12, 8819126128282090420800⟩, ⟨.privateRow 10 13, 19697663577728954703600⟩, ⟨.privateRow 10 14, 37337779554945773349600⟩, ⟨.privateRow 10 15, 62892806523806574315000⟩, ⟨.privateRow 10 16, 98367176046223316232000⟩, ⟨.privateRow 10 17, 146906289467652821586480⟩, ⟨.privateRow 10 18, 212148978530341397344800⟩, ⟨.privateRow 10 19, 357301807129967192192700⟩, ⟨.privateRow 10 20, 534283981815595214174400⟩, ⟨.privateRow 10 22, 1174843279150686476210880⟩, ⟨.privateRow 11 3, 29495405111311339200⟩, ⟨.privateRow 11 4, 61672210687287345600⟩, ⟨.privateRow 11 5, 161522456561943048000⟩, ⟨.privateRow 11 6, 373116874658088440880⟩, ⟨.privateRow 11 7, 999738994299184339200⟩, ⟨.privateRow 11 8, 2374380111460562805600⟩, ⟨.privateRow 11 9, 5427154540481286412800⟩, ⟨.privateRow 11 10, 12041499136692854228400⟩, ⟨.privateRow 11 11, 25010137174051261552320⟩, ⟨.privateRow 11 12, 45694702961373688279200⟩, ⟨.privateRow 11 14, 266156703922769754494400⟩, ⟨.privateRow 11 15, 93371726980553041238400⟩, ⟨.privateRow 11 17, 863746720546875847281600⟩, ⟨.privateRow 11 20, 2691981717798311420882400⟩, ⟨.privateRow 12 3, 1187190055730281402800⟩, ⟨.privateRow 12 4, 444186755545343382000⟩, ⟨.privateRow 12 5, 2238701247948530645280⟩, ⟨.privateRow 12 6, 5007621212516450127600⟩, ⟨.privateRow 12 7, 10675288358273085947400⟩, ⟨.privateRow 12 8, 22167531964980548546400⟩, ⟨.privateRow 12 9, 43258237655672128614525⟩, ⟨.privateRow 12 10, 76986448471118914968240⟩, ⟨.privateRow 12 11, 68626853731755552519000⟩, ⟨.privateRow 12 14, 28322962758136713466800⟩, ⟨.privateRow 12 15, 421995185238298026635280⟩, ⟨.privateRow 12 18, 8213101947384508201856400⟩, ⟨.privateRow 13 1, 4217842930917521505600⟩, ⟨.privateRow 13 2, 1356788635120321603200⟩, ⟨.privateRow 13 4, 28356882474014721506880⟩, ⟨.privateRow 13 5, 23172521689291808433600⟩, ⟨.privateRow 13 7, 226064929939900643592000⟩, ⟨.privateRow 13 9, 509926395366054202536000⟩, ⟨.privateRow 13 12, 157952810271924106639200⟩, ⟨.privateRow 13 14, 1408143084959625775881120⟩, ⟨.privateRow 13 15, 141784412370073607534400⟩, ⟨.privateRow 13 17, 19160084537799495851246400⟩, ⟨.privateRow 13 23, 66041686814481654035760000⟩, ⟨.privateRow 14 11, 14790041980717744056115800⟩, ⟨.privateRow 14 15, 212210222461787800750500⟩, ⟨.privateRow 14 22, 788548934071150691840200800⟩, ⟨.privateRow 15 18, 693842543361061393333834800⟩, ⟨.hall 14 9, 27303796062792849600⟩, ⟨.hall 14 20, 1349326297627159834382400⟩, ⟨.hall 11 22, 1877480853352004444544⟩, ⟨.hall 7 25, 59165394971414947600⟩]
  caps := #[0, 547299827997999196120000, 0, 12876330757955695201600, 3788944685011488499640, 1148910767709705000000, 1603100971787782804260, 6281428866297785200, 122540285688286363030, 664418485861160671200, 3643388966324351669940, 6475640267602776192000, 10970848897693139444847, 0, 143068724276755553476200, 0] }

theorem case_51_36_21_checked :
    (Witness.linear .conditional case_51_36_21).check 51 36 21 = true := by
  change case_51_36_21.check 51 36 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_22 : Certificate := {
  objectiveScale := 13
  eta := 161460
  rows := #[⟨.assumptionRow 22, 5⟩]
  caps := #[0, 0, 93610, 46046, 20020, 11305, 5130, 2601, 1428, 580, 364, 3714500, 3684784, 2615008, 1563320, 823650] }

theorem case_51_36_22_checked :
    (Witness.linear .conditional case_51_36_22).check 51 36 22 = true := by
  change case_51_36_22.check 51 36 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440] }

theorem case_51_36_23_checked :
    (Witness.linear .negative case_51_36_23).check 51 36 23 = true := by
  change case_51_36_23.check 51 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_37_1_checked :
    (Witness.rising).check 51 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_37_2_checked :
    (Witness.rising).check 51 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_37_3_checked :
    (Witness.rising).check 51 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_37_4_checked :
    (Witness.rising).check 51 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_37_5_checked :
    (Witness.rising).check 51 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_37_6_checked :
    (Witness.rising).check 51 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_37_7_checked :
    (Witness.rising).check 51 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_37_8_checked :
    (Witness.rising).check 51 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_37_9_checked :
    (Witness.rising).check 51 37 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_51_37_10_checked :
    (Witness.linear .positive case_51_37_10).check 51 37 10 = true := by
  change case_51_37_10.check 51 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_51_37_11_checked :
    (Witness.linear .positive case_51_37_11).check 51 37 11 = true := by
  change case_51_37_11.check 51 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_51_37_12_checked :
    (Witness.linear .positive case_51_37_12).check 51 37 12 = true := by
  change case_51_37_12.check 51 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_51_37_13_checked :
    (Witness.linear .positive case_51_37_13).check 51 37 13 = true := by
  change case_51_37_13.check 51 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_51_37_14_checked :
    (Witness.linear .positive case_51_37_14).check 51 37 14 = true := by
  change case_51_37_14.check 51 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_51_37_15_checked :
    (Witness.linear .positive case_51_37_15).check 51 37 15 = true := by
  change case_51_37_15.check 51 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_51_37_16_checked :
    (Witness.linear .positive case_51_37_16).check 51 37 16 = true := by
  change case_51_37_16.check 51 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_51_37_17_checked :
    (Witness.linear .positive case_51_37_17).check 51 37 17 = true := by
  change case_51_37_17.check 51 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_18 : Certificate := {
  objectiveScale := 182
  eta := 2593846275
  rows := #[⟨.assumptionRow 18, 337⟩]
  caps := #[0, 0, 737417835, 211503630, 61274392, 17956862, 5332730, 1608438, 494104, 155155, 50039, 20523360, 13477310, 6017858, 2125200] }

theorem case_51_37_18_checked :
    (Witness.linear .conditional case_51_37_18).check 51 37 18 = true := by
  change case_51_37_18.check 51 37 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_19 : Certificate := {
  objectiveScale := 3134047947030000000
  eta := 3526309159756544749147560000
  rows := #[⟨.count 2, 287409555151102628676432000⟩, ⟨.count 3, 20380659475202595360792000⟩, ⟨.count 4, 1081531298814578788176000⟩, ⟨.count 5, 44325053230105688040000⟩, ⟨.count 6, 3940004731564950048000⟩, ⟨.path 4, 559258635672061544419200⟩, ⟨.path 5, 20349329901304235832000⟩, ⟨.privateRow 2 34, 22867294961411524459836000⟩, ⟨.privateRow 2 35, 33805240596827271411840000⟩, ⟨.privateRow 3 29, 95709281604265244916000⟩, ⟨.privateRow 3 30, 2435710925053452119673600⟩, ⟨.privateRow 3 31, 4469442867368990210700000⟩, ⟨.privateRow 3 32, 9226013579550776156148000⟩, ⟨.privateRow 3 33, 10450370049884584383564000⟩, ⟨.privateRow 3 34, 14676025124487993310044000⟩, ⟨.privateRow 4 26, 164187384673183152781500⟩, ⟨.privateRow 4 27, 599865720380763644808000⟩, ⟨.privateRow 4 28, 981553678751118180708000⟩, ⟨.privateRow 4 29, 2184929623889343049118400⟩, ⟨.privateRow 4 30, 3056212420215787190358000⟩, ⟨.privateRow 4 31, 3949362242802416804364000⟩, ⟨.privateRow 4 32, 5224446274055123763648000⟩, ⟨.privateRow 5 23, 50944261179134804120640⟩, ⟨.privateRow 5 24, 126474151883234896540800⟩, ⟨.privateRow 5 25, 235218282474427517865600⟩, ⟨.privateRow 5 26, 527341490429028814281600⟩, ⟨.privateRow 5 27, 856852528997087511688800⟩, ⟨.privateRow 5 28, 1197485638064535268088640⟩, ⟨.privateRow 5 29, 1540886600455907401897200⟩, ⟨.privateRow 5 30, 2167199602597300773902400⟩, ⟨.privateRow 5 31, 803169964529515067284800⟩, ⟨.privateRow 6 20, 11272791315310829304000⟩, ⟨.privateRow 6 21, 30505188148934689008000⟩, ⟨.privateRow 6 22, 57195735353217858196800⟩, ⟨.privateRow 6 23, 140052575597017066984000⟩, ⟨.privateRow 6 24, 248220298088591853024000⟩, ⟨.privateRow 6 25, 379647598777222686768000⟩, ⟨.privateRow 6 26, 531353415881884235640000⟩, ⟨.privateRow 6 27, 680898484359949450795200⟩, ⟨.privateRow 6 28, 782008855783734981402000⟩, ⟨.privateRow 7 17, 2356967116204032618000⟩, ⟨.privateRow 7 18, 8239913741494006110000⟩, ⟨.privateRow 7 19, 16683457535220335359500⟩, ⟨.privateRow 7 20, 40340275717500227196000⟩, ⟨.privateRow 7 21, 81188722499810251926600⟩, ⟨.privateRow 7 22, 133604466001608688086000⟩, ⟨.privateRow 7 23, 198508519639549709840250⟩, ⟨.privateRow 7 24, 274252472207860272984000⟩, ⟨.privateRow 7 25, 303544531194316359948000⟩, ⟨.privateRow 8 14, 569453808858996686625⟩, ⟨.privateRow 8 15, 2446086270846573154800⟩, ⟨.privateRow 8 16, 5892417790510081545000⟩, ⟨.privateRow 8 17, 14699248421607698256000⟩, ⟨.privateRow 8 18, 30227223799974851149500⟩, ⟨.privateRow 8 19, 55764498785956196418000⟩, ⟨.privateRow 8 20, 87985230661759790759400⟩, ⟨.privateRow 8 21, 127530292040446056762000⟩, ⟨.privateRow 8 22, 58207413651479066724750⟩, ⟨.privateRow 9 11, 182407626461340280000⟩, ⟨.privateRow 9 12, 849804942102244128000⟩, ⟨.privateRow 9 13, 2421461241274292217000⟩, ⟨.privateRow 9 14, 6851230449887940916800⟩, ⟨.privateRow 9 15, 14798470152485020716000⟩, ⟨.privateRow 9 16, 28085161932693746496000⟩, ⟨.privateRow 9 17, 48429224825485844340000⟩, ⟨.privateRow 9 18, 33579585780383097000000⟩, ⟨.privateRow 10 8, 59100070973474250720⟩, ⟨.privateRow 10 9, 373263606148258425600⟩, ⟨.privateRow 10 10, 1182001419469485014400⟩, ⟨.privateRow 10 11, 3858886987091554017600⟩, ⟨.privateRow 10 12, 9603761533189565742000⟩, ⟨.privateRow 10 13, 19148422995405657233280⟩, ⟨.privateRow 10 14, 12242157558791094792000⟩, ⟨.privateRow 11 5, 67159171560766194000⟩, ⟨.privateRow 11 6, 211071682048122324000⟩, ⟨.privateRow 11 7, 738750887168428134000⟩, ⟨.privateRow 11 8, 2643950543550163848000⟩, ⟨.privateRow 11 9, 7715842599314693844000⟩, ⟨.privateRow 11 10, 4171769715774652992000⟩, ⟨.privateRow 12 3, 235543761126165492000⟩, ⟨.privateRow 12 4, 738750887168428134000⟩, ⟨.privateRow 12 5, 2579765002810383960000⟩, ⟨.privateRow 12 6, 1625251951770541894800⟩, ⟨.privateRow 13 1, 1354376626475451579000⟩, ⟨.hall 3 33, 985667507220840407964000⟩, ⟨.assumptionRow 19, 2518072134567293304⟩]
  caps := #[0, 0, 24523903140974216179200, 0, 1276333649823350135160, 2412309284260902411840, 320932446916302853632, 580624138675721149644, 78229780840451488248, 23448898460583156560, 6364178037997800134400, 11268590517787691064600, 0, 24668926221214591348032, 148482078234763469820624] }

theorem case_51_37_19_checked :
    (Witness.linear .conditional case_51_37_19).check 51 37 19 = true := by
  change case_51_37_19.check 51 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_20 : Certificate := {
  objectiveScale := 1114328158944000000
  eta := 1550308333770498666946982400
  rows := #[⟨.count 2, 123844198724915292383760000⟩, ⟨.count 3, 8366797047714749674430400⟩, ⟨.count 4, 400698481200155419881600⟩, ⟨.count 5, 7092008516816910086400⟩, ⟨.path 4, 266498177291446856595840⟩, ⟨.path 5, 6216324289151397220800⟩, ⟨.privateRow 2 34, 10183828729794215512816800⟩, ⟨.privateRow 2 35, 15433392534013065833020800⟩, ⟨.privateRow 3 29, 46951723051148988072000⟩, ⟨.privateRow 3 30, 1017624422068595298397440⟩, ⟨.privateRow 3 31, 1917255552438649255232400⟩, ⟨.privateRow 3 32, 4093829082959798306124000⟩, ⟨.privateRow 3 33, 4805328270734902202292000⟩, ⟨.privateRow 3 34, 6970163870493264006165600⟩, ⟨.privateRow 4 26, 74909339958878612787600⟩, ⟨.privateRow 4 27, 243492292410713912966400⟩, ⟨.privateRow 4 28, 403407234453106323039600⟩, ⟨.privateRow 4 29, 930412417335405129084960⟩, ⟨.privateRow 4 30, 1353687125647427712741600⟩, ⟨.privateRow 4 31, 1820676186456163417180800⟩, ⟨.privateRow 4 32, 2526380283938590532653200⟩, ⟨.privateRow 5 22, 2159838957394240799040⟩, ⟨.privateRow 5 23, 22197986657636928570432⟩, ⟨.privateRow 5 24, 50944261179134804120640⟩, ⟨.privateRow 5 25, 93215586942912261948120⟩, ⟨.privateRow 5 26, 214111114269615285465600⟩, ⟨.privateRow 5 27, 361968234688871960909760⟩, ⟨.privateRow 5 28, 526439792203319235713472⟩, ⟨.privateRow 5 29, 710441953172133967905120⟩, ⟨.privateRow 5 30, 1059821872743655913411520⟩, ⟨.privateRow 5 31, 611331134149617649447680⟩, ⟨.privateRow 6 19, 767795793843426163200⟩, ⟨.privateRow 6 20, 5723951318356857986400⟩, ⟨.privateRow 6 21, 12542348395481757652800⟩, ⟨.privateRow 6 22, 22458026969920215273600⟩, ⟨.privateRow 6 23, 54642028582759094276800⟩, ⟨.privateRow 6 24, 99600036276685633088400⟩, ⟨.privateRow 6 25, 158209951899625910856000⟩, ⟨.privateRow 6 26, 230906166184881433646400⟩, ⟨.privateRow 6 27, 311194707048104971291200⟩, ⟨.privateRow 6 28, 473194568260950500764800⟩, ⟨.privateRow 6 29, 69781861579050337516800⟩, ⟨.privateRow 7 16, 265950319380634128240⟩, ⟨.privateRow 7 17, 1628769813138010600200⟩, ⟨.privateRow 7 18, 3833927681099739854400⟩, ⟨.privateRow 7 19, 6784195647163398363900⟩, ⟨.privateRow 7 20, 15607791470722063485600⟩, ⟨.privateRow 7 21, 31288562574540159568680⟩, ⟨.privateRow 7 22, 52883619063671773977600⟩, ⟨.privateRow 7 23, 81342628934637007787850⟩, ⟨.privateRow 7 24, 117165890704912702052400⟩, ⟨.privateRow 7 25, 158207606658714265052400⟩, ⟨.privateRow 7 26, 89999558080772371471440⟩, ⟨.privateRow 8 13, 110088367499608898400⟩, ⟨.privateRow 8 14, 575610066252066921075⟩, ⟨.privateRow 8 15, 1474218437060552142960⟩, ⟨.privateRow 8 16, 2761521173462933739000⟩, ⟨.privateRow 8 17, 5944103292139814062800⟩, ⟨.privateRow 8 18, 11598388928544321703800⟩, ⟨.privateRow 8 19, 21316321053387189975600⟩, ⟨.privateRow 8 20, 34342066241502995855880⟩, ⟨.privateRow 8 21, 51318561628633474375200⟩, ⟨.privateRow 8 22, 72576118406904993931050⟩, ⟨.privateRow 8 23, 4770220014287564522400⟩, ⟨.privateRow 9 10, 55298312021964211200⟩, ⟨.privateRow 9 11, 266315134633556808800⟩, ⟨.privateRow 9 12, 722334200786907508800⟩, ⟨.privateRow 9 13, 1469293431146095955400⟩, ⟨.privateRow 9 14, 3222048313813114705920⟩, ⟨.privateRow 9 15, 5975673842873507572800⟩, ⟨.privateRow 9 16, 8122471292764666252800⟩, ⟨.privateRow 9 17, 23771361880441865289600⟩, ⟨.privateRow 9 18, 26051788861438548499200⟩, ⟨.privateRow 9 19, 5903440422794816821920⟩, ⟨.privateRow 10 7, 33771469127699571840⟩, ⟨.privateRow 10 8, 159570191628380476944⟩, ⟨.privateRow 10 9, 460358447582852058240⟩, ⟨.privateRow 10 10, 1011267881101670512320⟩, ⟨.privateRow 10 11, 2350096939886387852160⟩, ⟨.privateRow 10 12, 4506380411727411617400⟩, ⟨.privateRow 10 13, 7816969387424860895232⟩, ⟨.privateRow 10 14, 10545141235124191307040⟩, ⟨.privateRow 11 4, 25695683031945326400⟩, ⟨.privateRow 11 5, 134318343121532388000⟩, ⟨.privateRow 11 6, 394000473156495004800⟩, ⟨.privateRow 11 7, 930826117832219448840⟩, ⟨.privateRow 11 8, 1337527922031259358400⟩, ⟨.privateRow 11 9, 6566674552608250080000⟩, ⟨.privateRow 12 1, 43340052047214450528⟩, ⟨.privateRow 12 2, 135437662647545157900⟩, ⟨.privateRow 12 3, 471087522252330984000⟩, ⟨.privateRow 12 4, 1182001419469485014400⟩, ⟨.privateRow 12 5, 1341477801461399659200⟩, ⟨.privateRow 13 0, 1040161249133146812672⟩, ⟨.hall 3 33, 547423098578713111154400⟩, ⟨.assumptionRow 20, 529792001157739320⟩]
  caps := #[0, 59163292300566784730400, 463656616906018175640, 4493040227966584934640, 0, 1098872169559939827936, 118667057017415380320, 104207275459212868860, 228426350816980920555, 2962409572605225600, 1515625387637031654984, 63672734567568157668, 7762175499902604517308, 0, 125043321707400699242640] }

theorem case_51_37_20_checked :
    (Witness.linear .conditional case_51_37_20).check 51 37 20 = true := by
  change case_51_37_20.check 51 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_21 : Certificate := {
  objectiveScale := 911723039136000000
  eta := 1972620301926363355059393600
  rows := #[⟨.count 2, 158091507852624151190985600⟩, ⟨.count 3, 10723412377782035421890400⟩, ⟨.count 4, 517716621727634436307200⟩, ⟨.count 5, 9456011355755880115200⟩, ⟨.path 4, 328872245521450790839680⟩, ⟨.path 5, 9221581429460505705600⟩, ⟨.privateRow 2 35, 51357961675949123875680000⟩, ⟨.privateRow 3 30, 1264662718737717666407040⟩, ⟨.privateRow 3 31, 2477154849823600937991000⟩, ⟨.privateRow 3 34, 41578278931495183114036800⟩, ⟨.privateRow 4 26, 77790468418835482510200⟩, ⟨.privateRow 4 27, 295415926194552004670400⟩, ⟨.privateRow 4 28, 495504845053437030411600⟩, ⟨.privateRow 4 29, 1191161930470373523261600⟩, ⟨.privateRow 4 30, 1322659588386353731113600⟩, ⟨.privateRow 4 32, 7182136125051458318748000⟩, ⟨.privateRow 4 33, 4583506004347795514589600⟩, ⟨.privateRow 5 21, 384150461327582629680⟩, ⟨.privateRow 5 22, 3094694625520106219520⟩, ⟨.privateRow 5 23, 24301949184292611896064⟩, ⟨.privateRow 5 24, 59677938334103776727040⟩, ⟨.privateRow 5 25, 111241108589821908417720⟩, ⟨.privateRow 5 26, 260411798443691398458240⟩, ⟨.privateRow 5 27, 458340750422950639083840⟩, ⟨.privateRow 5 28, 647263977301489993885440⟩, ⟨.privateRow 5 29, 901364732451942534856080⟩, ⟨.privateRow 5 30, 412557895442165919526080⟩, ⟨.privateRow 5 31, 3074976692749865264961600⟩, ⟨.privateRow 6 17, 8755566070144333440⟩, ⟨.privateRow 6 18, 225143127517997145600⟩, ⟨.privateRow 6 19, 1257770741230349438400⟩, ⟨.privateRow 6 20, 6528368951051368621200⟩, ⟨.privateRow 6 21, 14386986974350802448000⟩, ⟨.privateRow 6 22, 26174764766696484818880⟩, ⟨.privateRow 6 23, 64557707157197551897600⟩, ⟨.privateRow 6 24, 119915685673817406773400⟩, ⟨.privateRow 6 25, 197009617541894085614400⟩, ⟨.privateRow 6 26, 294187019956849603584000⟩, ⟨.privateRow 6 28, 1494755711723834445085200⟩, ⟨.privateRow 7 14, 5794124605242573600⟩, ⟨.privateRow 7 15, 113890761771799337325⟩, ⟨.privateRow 7 16, 508917277827139381200⟩, ⟨.privateRow 7 17, 1994627395354755961800⟩, ⟨.privateRow 7 18, 4428716856922525582800⟩, ⟨.privateRow 7 19, 7789717688031536657400⟩, ⟨.privateRow 7 20, 18038953481221799708400⟩, ⟨.privateRow 7 21, 36474593802462525069360⟩, ⟨.privateRow 7 22, 62470963910479819094400⟩, ⟨.privateRow 7 24, 342280875331970098009200⟩, ⟨.privateRow 7 26, 285010092269579574097200⟩, ⟨.privateRow 8 11, 5184216752059144800⟩, ⟨.privateRow 8 12, 65666745526082500800⟩, ⟨.privateRow 8 13, 252044420328051951600⟩, ⟨.privateRow 8 14, 791079075009525126825⟩, ⟨.privateRow 8 15, 1782852141033139896720⟩, ⟨.privateRow 8 16, 3211807428498928030200⟩, ⟨.privateRow 8 17, 6841969755006057487200⟩, ⟨.privateRow 8 18, 13391911915725450006900⟩, ⟨.privateRow 8 19, 24754870637298419108400⟩, ⟨.privateRow 8 20, 40311173409823895178600⟩, ⟨.privateRow 8 21, 33298512210517668114000⟩, ⟨.privateRow 8 22, 61187042229725060198550⟩, ⟨.privateRow 8 23, 265042711147827202246800⟩, ⟨.privateRow 8 24, 29435118682066480983600⟩, ⟨.privateRow 9 8, 3126987882194404800⟩, ⟨.privateRow 9 9, 45966721868257750560⟩, ⟨.privateRow 9 10, 158982647063147107200⟩, ⟨.privateRow 9 11, 430481998448763060800⟩, ⟨.privateRow 9 12, 954099184996610452800⟩, ⟨.privateRow 9 13, 1785314643990367990500⟩, ⟨.privateRow 9 14, 3756137844091919045760⟩, ⟨.privateRow 9 15, 6885627316592079369600⟩, ⟨.privateRow 9 16, 12436271345016547459200⟩, ⟨.privateRow 9 17, 21352636753564493176800⟩, ⟨.privateRow 9 18, 19682114545408545921600⟩, ⟨.privateRow 9 20, 163123492191847385598400⟩, ⟨.privateRow 9 26, 256428641279352165624000⟩, ⟨.privateRow 10 5, 5139136606389065280⟩, ⟨.privateRow 10 6, 37609136074029068640⟩, ⟨.privateRow 10 7, 129457298322848358720⟩, ⟨.privateRow 10 8, 330960397451455804032⟩, ⟨.privateRow 10 9, 709200851681691008640⟩, ⟨.privateRow 10 10, 1339601608732083016320⟩, ⟨.privateRow 10 11, 2857662255305637299520⟩, ⟨.privateRow 10 12, 5259906316639208314080⟩, ⟨.privateRow 10 13, 9022610835283735609920⟩, ⟨.privateRow 10 14, 15230932576592506899840⟩, ⟨.privateRow 10 15, 24658368073855718146560⟩, ⟨.privateRow 10 16, 29195435060896279855680⟩, ⟨.privateRow 10 17, 20351915349774587429760⟩, ⟨.privateRow 10 18, 33911620724579525063136⟩, ⟨.privateRow 10 20, 60045672109049838731520⟩, ⟨.privateRow 11 3, 61562573930702344500⟩, ⟨.privateRow 11 4, 141326256675699295200⟩, ⟨.privateRow 11 5, 362659526428137447600⟩, ⟨.privateRow 11 6, 759858055373240366400⟩, ⟨.privateRow 11 7, 1418401703363382017280⟩, ⟨.privateRow 11 9, 11721514076405726392800⟩, ⟨.privateRow 11 10, 6900802404843905157600⟩, ⟨.privateRow 11 11, 16141706884630154727900⟩, ⟨.privateRow 11 13, 91394038326836966292000⟩, ⟨.privateRow 11 14, 26890532292930784077600⟩, ⟨.privateRow 11 15, 53928814763295253782000⟩, ⟨.privateRow 11 16, 44083280212486929741600⟩, ⟨.privateRow 11 17, 67905981548521914077280⟩, ⟨.privateRow 11 19, 82112161108770787094100⟩, ⟨.privateRow 12 3, 3486047664667249281600⟩, ⟨.privateRow 12 4, 935751123746675636400⟩, ⟨.privateRow 12 5, 4695172305114898807200⟩, ⟨.privateRow 12 9, 23837028625967947790400⟩, ⟨.privateRow 12 11, 56992168442087002444320⟩, ⟨.privateRow 12 14, 1145802625998232035834000⟩, ⟨.privateRow 12 15, 98500118289123751200⟩, ⟨.privateRow 12 16, 8668010409442890105600⟩, ⟨.privateRow 12 24, 289294847415156457274400⟩, ⟨.privateRow 13 5, 121568845992436533731040⟩, ⟨.privateRow 13 8, 59656306935577537785600⟩, ⟨.privateRow 13 9, 114173949611880568109700⟩, ⟨.privateRow 13 10, 199364239417186472428800⟩, ⟨.privateRow 13 12, 573088842070474157366400⟩, ⟨.privateRow 13 13, 5729013129991160179170000⟩, ⟨.privateRow 14 6, 4141141973111340747950400⟩, ⟨.privateRow 14 9, 1797311958397983263396160⟩, ⟨.privateRow 14 10, 573481760124748354308000⟩, ⟨.privateRow 14 11, 6299476565062620384244800⟩, ⟨.privateRow 14 12, 68744365305339790885618800⟩, ⟨.hall 10 8, 89578838023823904⟩, ⟨.hall 12 9, 286391513668740480⟩, ⟨.hall 6 14, 1732223123078448⟩, ⟨.hall 9 20, 399995847308248704⟩, ⟨.hall 13 23, 232411029103187490956400⟩, ⟨.hall 12 24, 97255076793949226984832⟩, ⟨.hall 6 25, 2544328749985510400⟩, ⟨.hall 10 25, 626359726556479238400⟩, ⟨.hall 4 27, 1649542234902658200⟩]
  caps := #[0, 7960856406681708129600, 1157912201180262528000, 0, 2111764122068948713080, 0, 378337288808358637400, 309579890508610023835, 0, 593765247865935257760, 1661434868589429668832, 227725583386442158368, 8958735160320124334232, 4511093311338268184640, 0] }

theorem case_51_37_21_checked :
    (Witness.linear .conditional case_51_37_21).check 51 37 21 = true := by
  change case_51_37_21.check 51 37 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_22 : Certificate := {
  objectiveScale := 81
  eta := 30565275
  rows := #[⟨.assumptionRow 22, 44⟩]
  caps := #[0, 0, 11297715, 5163730, 1846900, 894102, 328776, 159885, 60588, 29852, 25407180, 50220040, 42345300, 27784460, 15690048] }

theorem case_51_37_22_checked :
    (Witness.linear .conditional case_51_37_22).check 51 37 22 = true := by
  change case_51_37_22.check 51 37 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876] }

theorem case_51_37_23_checked :
    (Witness.linear .negative case_51_37_23).check 51 37 23 = true := by
  change case_51_37_23.check 51 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012] }

theorem case_51_37_24_checked :
    (Witness.linear .negative case_51_37_24).check 51 37 24 = true := by
  change case_51_37_24.check 51 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_38_1_checked :
    (Witness.rising).check 51 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_38_2_checked :
    (Witness.rising).check 51 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_38_3_checked :
    (Witness.rising).check 51 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_38_4_checked :
    (Witness.rising).check 51 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_38_5_checked :
    (Witness.rising).check 51 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_38_6_checked :
    (Witness.rising).check 51 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_38_7_checked :
    (Witness.rising).check 51 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_38_8_checked :
    (Witness.rising).check 51 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_38_9_checked :
    (Witness.rising).check 51 38 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_51_38_10_checked :
    (Witness.linear .positive case_51_38_10).check 51 38 10 = true := by
  change case_51_38_10.check 51 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_51_38_11_checked :
    (Witness.linear .positive case_51_38_11).check 51 38 11 = true := by
  change case_51_38_11.check 51 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_51_38_12_checked :
    (Witness.linear .positive case_51_38_12).check 51 38 12 = true := by
  change case_51_38_12.check 51 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_51_38_13_checked :
    (Witness.linear .positive case_51_38_13).check 51 38 13 = true := by
  change case_51_38_13.check 51 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_51_38_14_checked :
    (Witness.linear .positive case_51_38_14).check 51 38 14 = true := by
  change case_51_38_14.check 51 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_51_38_15_checked :
    (Witness.linear .positive case_51_38_15).check 51 38 15 = true := by
  change case_51_38_15.check 51 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_51_38_16_checked :
    (Witness.linear .positive case_51_38_16).check 51 38 16 = true := by
  change case_51_38_16.check 51 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_51_38_17_checked :
    (Witness.linear .positive case_51_38_17).check 51 38 17 = true := by
  change case_51_38_17.check 51 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_51_38_18_checked :
    (Witness.linear .positive case_51_38_18).check 51 38 18 = true := by
  change case_51_38_18.check 51 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_19 : Certificate := {
  objectiveScale := 669
  eta := 13764678900
  rows := #[⟨.assumptionRow 19, 973⟩]
  caps := #[0, 0, 3964051035, 1150146855, 336496555, 99370304, 29654630, 8955498, 2741284, 910455, 462416955, 354175965, 189068165, 82485590] }

theorem case_51_38_19_checked :
    (Witness.linear .conditional case_51_38_19).check 51 38 19 = true := by
  change case_51_38_19.check 51 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_20 : Certificate := {
  objectiveScale := 9499599039840000000
  eta := 42687434393898715098581904000
  rows := #[⟨.count 2, 2159305541446820269046544000⟩, ⟨.count 3, 72822942391589801178768000⟩, ⟨.count 4, 554208085171916295120000⟩, ⟨.path 2, 240154076484417660869304000⟩, ⟨.path 3, 60529044537478856226888000⟩, ⟨.path 4, 506491992045733072579200⟩, ⟨.privateRow 2 35, 156420613639063608328494000⟩, ⟨.privateRow 2 36, 215605418734714502678184000⟩, ⟨.privateRow 3 30, 8824224289459511676744000⟩, ⟨.privateRow 3 31, 17198924243168469025224000⟩, ⟨.privateRow 3 32, 30490681485874928169852000⟩, ⟨.privateRow 3 33, 62650145094878626517232000⟩, ⟨.privateRow 3 34, 65729078901389272601232000⟩, ⟨.privateRow 3 35, 84147260931935957475720000⟩, ⟨.privateRow 4 25, 178455003425357047028640⟩, ⟨.privateRow 4 26, 501250423699933182475200⟩, ⟨.privateRow 4 27, 2980946738118444772376700⟩, ⟨.privateRow 4 28, 4356075549451262079643200⟩, ⟨.privateRow 4 29, 6896195939822545098943200⟩, ⟨.privateRow 4 30, 15307227312448328071214400⟩, ⟨.privateRow 4 31, 20885331689703665581597200⟩, ⟨.privateRow 4 32, 25997901275414593404079200⟩, ⟨.privateRow 4 33, 31961180271864412739570400⟩, ⟨.privateRow 5 21, 17242029316459618070400⟩, ⟨.privateRow 5 22, 51110301188076724994400⟩, ⟨.privateRow 5 23, 214293792933140967446400⟩, ⟨.privateRow 5 24, 804710139669622460514240⟩, ⟨.privateRow 5 25, 1173552725539346702950400⟩, ⟨.privateRow 5 26, 1761765924085391689264800⟩, ⟨.privateRow 5 27, 3876993449158205548972800⟩, ⟨.privateRow 5 28, 6224372583241922123414400⟩, ⟨.privateRow 5 29, 8502783600059800225574400⟩, ⟨.privateRow 5 30, 10652495183765533321423200⟩, ⟨.privateRow 5 31, 12533313215036003325936000⟩, ⟨.privateRow 6 17, 1635683584708780732125⟩, ⟨.privateRow 6 18, 5849974232370227559600⟩, ⟨.privateRow 6 19, 25071318138729546684000⟩, ⟨.privateRow 6 20, 82539110120689243098000⟩, ⟨.privateRow 6 21, 240156836907830394552000⟩, ⟨.privateRow 6 22, 388365514230320131050000⟩, ⟨.privateRow 6 23, 546972590726616276822600⟩, ⟨.privateRow 6 24, 1123981891254525300998000⟩, ⟨.privateRow 6 25, 1943961832085659171285500⟩, ⟨.privateRow 6 26, 2923007801595214078746000⟩, ⟨.privateRow 6 27, 4019291506582439242155000⟩, ⟨.privateRow 6 28, 5054069843387225546886000⟩, ⟨.privateRow 6 29, 1307777134315396924179000⟩, ⟨.privateRow 7 13, 208348904199968532000⟩, ⟨.privateRow 7 14, 879695373288756024000⟩, ⟨.privateRow 7 15, 4036249359795468816000⟩, ⟨.privateRow 7 16, 14102616453035370009750⟩, ⟨.privateRow 7 17, 38618626887376389453600⟩, ⟨.privateRow 7 18, 92462267271028892094000⟩, ⟨.privateRow 7 19, 161390266561052547480000⟩, ⟨.privateRow 7 20, 233339197764842535366000⟩, ⟨.privateRow 7 21, 422973529938566419176000⟩, ⟨.privateRow 7 22, 718095333215611542391200⟩, ⟨.privateRow 7 23, 1143457369379834705196000⟩, ⟨.privateRow 7 24, 1684561658887137238708500⟩, ⟨.privateRow 7 25, 2019843412454790170820000⟩, ⟨.privateRow 8 9, 69975768329787411000⟩, ⟨.privateRow 8 10, 219923843322189006000⟩, ⟨.privateRow 8 11, 846706796790427673100⟩, ⟨.privateRow 8 12, 3322007528077276038000⟩, ⟨.privateRow 8 13, 10006534871159599773000⟩, ⟨.privateRow 8 14, 23907015438788546064000⟩, ⟨.privateRow 8 15, 50032674355797998865000⟩, ⟨.privateRow 8 16, 88468031373739230813600⟩, ⟨.privateRow 8 17, 135143201721485144187000⟩, ⟨.privateRow 8 18, 236604220977241187532000⟩, ⟨.privateRow 8 19, 362287877899419355884000⟩, ⟨.privateRow 8 20, 573521397230937620556000⟩, ⟨.privateRow 8 21, 861947519132655371215800⟩, ⟨.privateRow 9 7, 214186699583349292800⟩, ⟨.privateRow 9 8, 1007651063948938718400⟩, ⟨.privateRow 9 9, 3518781493155024096000⟩, ⟨.privateRow 9 10, 9359958771792364095360⟩, ⟨.privateRow 9 11, 20353372952512481481600⟩, ⟨.privateRow 9 12, 39136669718313101334400⟩, ⟨.privateRow 9 13, 67664098241904551587200⟩, ⟨.privateRow 9 14, 106069269634291757593800⟩, ⟨.privateRow 9 15, 189333902875027996525440⟩, ⟨.privateRow 9 16, 284845361870899200571200⟩, ⟨.privateRow 9 17, 99473246056497796560000⟩, ⟨.privateRow 10 4, 443366468137533036096⟩, ⟨.privateRow 10 5, 1616440248418089194100⟩, ⟨.privateRow 10 6, 5060160777656627042400⟩, ⟨.privateRow 10 7, 12091812767387264620800⟩, ⟨.privateRow 10 8, 24543500914756293069600⟩, ⟨.privateRow 10 9, 44890854898925219904720⟩, ⟨.privateRow 10 10, 75547312662908589703200⟩, ⟨.privateRow 10 11, 116691591266753486583600⟩, ⟨.privateRow 11 2, 6394708675060572636000⟩, ⟨.privateRow 11 3, 8128385249188105661760⟩, ⟨.privateRow 11 4, 22322270097202184109000⟩, ⟨.privateRow 11 5, 44979206912503351488000⟩, ⟨.privateRow 11 6, 12595638299361733980000⟩, ⟨.privateRow 12 0, 33868271871617106924000⟩, ⟨.hall 3 34, 2155077725482794507595200⟩, ⟨.assumptionRow 20, 5580711636186605100⟩]
  caps := #[0, 0, 220862900218509729180000, 68279709644911787022000, 7032801161928340819020, 7287064676550506786400, 5580711636186605100, 4015798271420468901300, 0, 5614595440217309932568, 5798385571503525007644, 240079213191344536938600, 0, 4013767520317606691640000] }

theorem case_51_38_20_checked :
    (Witness.linear .conditional case_51_38_20).check 51 38 20 = true := by
  change case_51_38_20.check 51 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_21 : Certificate := {
  objectiveScale := 5801540842188000000
  eta := 43656744334864396698746784000
  rows := #[⟨.count 2, 2198931419536612284147624000⟩, ⟨.count 3, 77838525562395643649604000⟩, ⟨.count 4, 1230341949081654175166400⟩, ⟨.path 2, 339947523489859390853748000⟩, ⟨.path 3, 48926930211709155690084000⟩, ⟨.path 4, 1227051991094987949091200⟩, ⟨.privateRow 2 35, 160688015894887363800918000⟩, ⟨.privateRow 2 36, 223276582313635777396470000⟩, ⟨.privateRow 3 30, 9012039251656661087868000⟩, ⟨.privateRow 3 31, 17433538999224580256824800⟩, ⟨.privateRow 3 32, 30968685959335705974393000⟩, ⟨.privateRow 3 33, 64223480270005566666156000⟩, ⟨.privateRow 3 34, 68264580891050789651406000⟩, ⟨.privateRow 3 35, 88562452010472223960176000⟩, ⟨.privateRow 4 25, 225839794707555890261400⟩, ⟨.privateRow 4 26, 557594912359078005812400⟩, ⟨.privateRow 4 27, 3071351932012113618018150⟩, ⟨.privateRow 4 28, 4413079809640373469998400⟩, ⟨.privateRow 4 29, 6934066825642626045776400⟩, ⟨.privateRow 4 30, 15457417703529917387191920⟩, ⟨.privateRow 4 31, 21310686395073111338101800⟩, ⟨.privateRow 4 32, 26935436619497085136657200⟩, ⟨.privateRow 4 33, 33898137529540260191014800⟩, ⟨.privateRow 5 18, 76973345162766152100⟩, ⟨.privateRow 5 19, 410524507534752811200⟩, ⟨.privateRow 5 20, 1847360283906387650400⟩, ⟨.privateRow 5 21, 31926175162895007086400⟩, ⟨.privateRow 5 22, 72047051072349118365600⟩, ⟨.privateRow 5 23, 247770200502111264868800⟩, ⟨.privateRow 5 24, 840548929177406380932000⟩, ⟨.privateRow 5 25, 1200236818529105635678400⟩, ⟨.privateRow 5 26, 1770848778814598095212600⟩, ⟨.privateRow 5 27, 3867668678201344735118400⟩, ⟨.privateRow 5 28, 6236483056214197331344800⟩, ⟨.privateRow 5 29, 8610669440639933264357760⟩, ⟨.privateRow 5 30, 10985020034868683098495200⟩, ⟨.privateRow 5 31, 14306368563078600717508800⟩, ⟨.privateRow 6 14, 40512286927771659000⟩, ⟨.privateRow 6 15, 171051878139480338000⟩, ⟨.privateRow 6 16, 543341259972466956000⟩, ⟨.privateRow 6 17, 4522184028312511435875⟩, ⟨.privateRow 6 18, 12367050789484428437400⟩, ⟨.privateRow 6 19, 37661958168924867277500⟩, ⟨.privateRow 6 20, 98525881808340674688000⟩, ⟨.privateRow 6 21, 257988995203871219788500⟩, ⟨.privateRow 6 22, 405159698629469109690000⟩, ⟨.privateRow 6 23, 558364645810705667333400⟩, ⟨.privateRow 6 24, 1122442424351269977956000⟩, ⟨.privateRow 6 25, 1924526062432060717880250⟩, ⟨.privateRow 6 26, 2904534198756150202242000⟩, ⟨.privateRow 6 27, 4036225642518247795617000⟩, ⟨.privateRow 6 28, 5168452234299096048906600⟩, ⟨.privateRow 6 29, 2424852805990040706530250⟩, ⟨.privateRow 7 10, 29989614998480319000⟩, ⟨.privateRow 7 11, 62835383806339716000⟩, ⟨.privateRow 7 12, 197931458989970105400⟩, ⟨.privateRow 7 13, 868120434166535550000⟩, ⟨.privateRow 7 14, 2602432145979236571000⟩, ⟨.privateRow 7 15, 8848700519551604712000⟩, ⟨.privateRow 7 16, 21607517606405069839500⟩, ⟨.privateRow 7 17, 47987382612901641109200⟩, ⟨.privateRow 7 18, 103254244439767738317000⟩, ⟨.privateRow 7 19, 173012395819694381874000⟩, ⟨.privateRow 7 20, 244335389930951985666000⟩, ⟨.privateRow 7 21, 430950767528162184030000⟩, ⟨.privateRow 7 22, 713674863964835543370600⟩, ⟨.privateRow 7 23, 1132387869265951191894000⟩, ⟨.privateRow 7 24, 1650665896535104858158750⟩, ⟨.privateRow 7 25, 2264712903148096044072000⟩, ⟨.privateRow 7 26, 277543890272602525572000⟩, ⟨.privateRow 8 7, 32072227151152563375⟩, ⟨.privateRow 8 8, 100400015429694981000⟩, ⟨.privateRow 8 9, 279903073319149644000⟩, ⟨.privateRow 8 10, 733079477740630020000⟩, ⟨.privateRow 8 11, 2578607062952666095350⟩, ⟨.privateRow 8 12, 7373236220854441938000⟩, ⟨.privateRow 8 13, 15865061697436801349500⟩, ⟨.privateRow 8 14, 31196844010085811057000⟩, ⟨.privateRow 8 15, 58499742323702275596000⟩, ⟨.privateRow 8 16, 98012726173922233674000⟩, ⟨.privateRow 8 17, 145369660435966932966000⟩, ⟨.privateRow 8 18, 248031802220636470113000⟩, ⟨.privateRow 8 19, 368766467783952173685750⟩, ⟨.privateRow 8 20, 570092584582778037417000⟩, ⟨.privateRow 8 21, 850940330774379811465500⟩, ⟨.privateRow 8 22, 184051820878080843688000⟩, ⟨.privateRow 9 5, 492629409041703373440⟩, ⟨.privateRow 9 6, 153946690325532304200⟩, ⟨.privateRow 9 7, 1017386823020909140800⟩, ⟨.privateRow 9 8, 3134914421174476012800⟩, ⟨.privateRow 9 9, 7917258359598804216000⟩, ⟨.privateRow 9 10, 15640983737074082106720⟩, ⟨.privateRow 9 11, 28261371360813509318400⟩, ⟨.privateRow 9 12, 48373471137845039586400⟩, ⟨.privateRow 9 13, 78096250433375917142400⟩, ⟨.privateRow 9 15, 326613298194649336590720⟩, ⟨.privateRow 9 16, 406155353847418656280800⟩, ⟨.privateRow 10 4, 5431239234684779692176⟩, ⟨.privateRow 10 5, 2540120390371283019300⟩, ⟨.privateRow 10 6, 11445601758985227834000⟩, ⟨.privateRow 10 7, 21538541491908565105800⟩, ⟨.privateRow 10 8, 36815251372134439604400⟩, ⟨.privateRow 10 9, 59438817134688022651620⟩, ⟨.privateRow 10 10, 92027710985126100584400⟩, ⟨.privateRow 10 11, 91906174124342785607400⟩, ⟨.privateRow 11 3, 76850187810505726256640⟩, ⟨.privateRow 11 4, 10006534871159599773000⟩, ⟨.privateRow 11 5, 24899203826564355288000⟩, ⟨.privateRow 12 0, 41394554509754241796000⟩, ⟨.privateRow 13 0, 23447265141888766332000⟩, ⟨.hall 3 34, 2683950583903994629224000⟩, ⟨.assumptionRow 21, 142493985597600⟩]
  caps := #[0, 613161373878545968476000, 9368162318146942510200, 3442248073529925660000, 0, 14170593768103577777840, 1574594487925813956875, 0, 12866453141123549194325, 0, 15353712978234614847864, 0, 341953824265641531944000, 0] }

theorem case_51_38_21_checked :
    (Witness.linear .conditional case_51_38_21).check 51 38 21 = true := by
  change case_51_38_21.check 51 38 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_22 : Certificate := {
  objectiveScale := 929
  eta := 1022180835
  rows := #[⟨.assumptionRow 22, 564⟩]
  caps := #[0, 0, 355063995, 153777195, 56849100, 23112056, 9253893, 3469989, 1542648, 570285, 1475523945, 1442093445, 1009428485, 596524665] }

theorem case_51_38_22_checked :
    (Witness.linear .conditional case_51_38_22).check 51 38 22 = true := by
  change case_51_38_22.check 51 38 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640] }

theorem case_51_38_23_checked :
    (Witness.linear .negative case_51_38_23).check 51 38 23 = true := by
  change case_51_38_23.check 51 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900] }

theorem case_51_38_24_checked :
    (Witness.linear .negative case_51_38_24).check 51 38 24 = true := by
  change case_51_38_24.check 51 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_39_1_checked :
    (Witness.rising).check 51 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_39_2_checked :
    (Witness.rising).check 51 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_39_3_checked :
    (Witness.rising).check 51 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_39_4_checked :
    (Witness.rising).check 51 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_39_5_checked :
    (Witness.rising).check 51 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_39_6_checked :
    (Witness.rising).check 51 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_39_7_checked :
    (Witness.rising).check 51 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_39_8_checked :
    (Witness.rising).check 51 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_39_9_checked :
    (Witness.rising).check 51 39 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_51_39_10_checked :
    (Witness.linear .positive case_51_39_10).check 51 39 10 = true := by
  change case_51_39_10.check 51 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_51_39_11_checked :
    (Witness.linear .positive case_51_39_11).check 51 39 11 = true := by
  change case_51_39_11.check 51 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_51_39_12_checked :
    (Witness.linear .positive case_51_39_12).check 51 39 12 = true := by
  change case_51_39_12.check 51 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_51_39_13_checked :
    (Witness.linear .positive case_51_39_13).check 51 39 13 = true := by
  change case_51_39_13.check 51 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_51_39_14_checked :
    (Witness.linear .positive case_51_39_14).check 51 39 14 = true := by
  change case_51_39_14.check 51 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_51_39_15_checked :
    (Witness.linear .positive case_51_39_15).check 51 39 15 = true := by
  change case_51_39_15.check 51 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_51_39_16_checked :
    (Witness.linear .positive case_51_39_16).check 51 39 16 = true := by
  change case_51_39_16.check 51 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_51_39_17_checked :
    (Witness.linear .positive case_51_39_17).check 51 39 17 = true := by
  change case_51_39_17.check 51 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_51_39_18_checked :
    (Witness.linear .positive case_51_39_18).check 51 39 18 = true := by
  change case_51_39_18.check 51 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_19 : Certificate := {
  objectiveScale := 8
  eta := 987533520
  rows := #[⟨.assumptionRow 19, 21⟩]
  caps := #[0, 0, 272786325, 75847905, 21395520, 6091780, 1753244, 510986, 151164, 45526, 14014, 4433, 1452] }

theorem case_51_39_19_checked :
    (Witness.linear .conditional case_51_39_19).check 51 39 19 = true := by
  change case_51_39_19.check 51 39 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_20 : Certificate := {
  objectiveScale := 748
  eta := 16123097520
  rows := #[⟨.assumptionRow 20, 863⟩]
  caps := #[0, 0, 4873385475, 1475156865, 447634395, 136307292, 41690902, 12819870, 4346934, 2621199945, 2253376125, 1371364995, 695574165] }

theorem case_51_39_20_checked :
    (Witness.linear .conditional case_51_39_20).check 51 39 20 = true := by
  change case_51_39_20.check 51 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_21 : Certificate := {
  objectiveScale := 556
  eta := 7351914120
  rows := #[⟨.assumptionRow 21, 503⟩]
  caps := #[0, 0, 2360809815, 744375450, 231529155, 82031455, 28111336, 9385734, 3101550, 2467683225, 2290704780, 1516441290, 843924510] }

theorem case_51_39_21_checked :
    (Witness.linear .conditional case_51_39_21).check 51 39 21 = true := by
  change case_51_39_21.check 51 39 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_22 : Certificate := {
  objectiveScale := 5
  eta := 4942470
  rows := #[⟨.assumptionRow 22, 3⟩]
  caps := #[0, 0, 1776060, 740025, 284625, 110561, 46398, 16473, 7752, 28514250, 27943965, 19684665, 11759670] }

theorem case_51_39_22_checked :
    (Witness.linear .conditional case_51_39_22).check 51 39 22 = true := by
  change case_51_39_22.check 51 39 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405, 4345965] }

theorem case_51_39_23_checked :
    (Witness.linear .negative case_51_39_23).check 51 39 23 = true := by
  change case_51_39_23.check 51 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440] }

theorem case_51_39_24_checked :
    (Witness.linear .negative case_51_39_24).check 51 39 24 = true := by
  change case_51_39_24.check 51 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_39_25_checked :
    (Witness.linear .negative case_51_39_25).check 51 39 25 = true := by
  change case_51_39_25.check 51 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_40_1_checked :
    (Witness.rising).check 51 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_40_2_checked :
    (Witness.rising).check 51 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_40_3_checked :
    (Witness.rising).check 51 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_40_4_checked :
    (Witness.rising).check 51 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_40_5_checked :
    (Witness.rising).check 51 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_40_6_checked :
    (Witness.rising).check 51 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_40_7_checked :
    (Witness.rising).check 51 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_40_8_checked :
    (Witness.rising).check 51 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_40_9_checked :
    (Witness.rising).check 51 40 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_51_40_10_checked :
    (Witness.linear .positive case_51_40_10).check 51 40 10 = true := by
  change case_51_40_10.check 51 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_51_40_11_checked :
    (Witness.linear .positive case_51_40_11).check 51 40 11 = true := by
  change case_51_40_11.check 51 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_51_40_12_checked :
    (Witness.linear .positive case_51_40_12).check 51 40 12 = true := by
  change case_51_40_12.check 51 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_51_40_13_checked :
    (Witness.linear .positive case_51_40_13).check 51 40 13 = true := by
  change case_51_40_13.check 51 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_51_40_14_checked :
    (Witness.linear .positive case_51_40_14).check 51 40 14 = true := by
  change case_51_40_14.check 51 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_51_40_15_checked :
    (Witness.linear .positive case_51_40_15).check 51 40 15 = true := by
  change case_51_40_15.check 51 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_51_40_16_checked :
    (Witness.linear .positive case_51_40_16).check 51 40 16 = true := by
  change case_51_40_16.check 51 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_51_40_17_checked :
    (Witness.linear .positive case_51_40_17).check 51 40 17 = true := by
  change case_51_40_17.check 51 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_51_40_18_checked :
    (Witness.linear .positive case_51_40_18).check 51 40 18 = true := by
  change case_51_40_18.check 51 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_51_40_19_checked :
    (Witness.linear .positive case_51_40_19).check 51 40 19 = true := by
  change case_51_40_19.check 51 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_20 : Certificate := {
  objectiveScale := 27
  eta := 1059489480
  rows := #[⟨.assumptionRow 20, 35⟩]
  caps := #[0, 0, 303951900, 91815885, 27865305, 8506205, 2615008, 810730, 253878, 112896420, 112896420, 70105035] }

theorem case_51_40_20_checked :
    (Witness.linear .conditional case_51_40_20).check 51 40 20 = true := by
  change case_51_40_20.check 51 40 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_21 : Certificate := {
  objectiveScale := 935
  eta := 30186765840
  rows := #[⟨.assumptionRow 21, 954⟩]
  caps := #[0, 0, 9357376350, 2882500530, 884190840, 270489890, 88828553, 29951790, 9980700, 7047341910, 6343139985, 4066092030] }

theorem case_51_40_21_checked :
    (Witness.linear .conditional case_51_40_21).check 51 40 21 = true := by
  change case_51_40_21.check 51 40 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_22 : Certificate := {
  objectiveScale := 133
  eta := 999939720
  rows := #[⟨.assumptionRow 22, 99⟩]
  caps := #[0, 0, 340510170, 110165055, 43118790, 15262225, 5090613, 2014551, 258048960, 1389494400, 1269734550, 858559065] }

theorem case_51_40_22_checked :
    (Witness.linear .conditional case_51_40_22).check 51 40 22 = true := by
  change case_51_40_22.check 51 40 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825, 15967980] }

theorem case_51_40_23_checked :
    (Witness.linear .negative case_51_40_23).check 51 40 23 = true := by
  change case_51_40_23.check 51 40 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845] }

theorem case_51_40_24_checked :
    (Witness.linear .negative case_51_40_24).check 51 40 24 = true := by
  change case_51_40_24.check 51 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_40_25_checked :
    (Witness.linear .negative case_51_40_25).check 51 40 25 = true := by
  change case_51_40_25.check 51 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_40_26_checked :
    (Witness.linear .negative case_51_40_26).check 51 40 26 = true := by
  change case_51_40_26.check 51 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_41_1_checked :
    (Witness.rising).check 51 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_41_2_checked :
    (Witness.rising).check 51 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_41_3_checked :
    (Witness.rising).check 51 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_41_4_checked :
    (Witness.rising).check 51 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_41_5_checked :
    (Witness.rising).check 51 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_41_6_checked :
    (Witness.rising).check 51 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_41_7_checked :
    (Witness.rising).check 51 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_41_8_checked :
    (Witness.rising).check 51 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_41_9_checked :
    (Witness.rising).check 51 41 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_51_41_10_checked :
    (Witness.linear .positive case_51_41_10).check 51 41 10 = true := by
  change case_51_41_10.check 51 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_51_41_11_checked :
    (Witness.linear .positive case_51_41_11).check 51 41 11 = true := by
  change case_51_41_11.check 51 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_51_41_12_checked :
    (Witness.linear .positive case_51_41_12).check 51 41 12 = true := by
  change case_51_41_12.check 51 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_51_41_13_checked :
    (Witness.linear .positive case_51_41_13).check 51 41 13 = true := by
  change case_51_41_13.check 51 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_51_41_14_checked :
    (Witness.linear .positive case_51_41_14).check 51 41 14 = true := by
  change case_51_41_14.check 51 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_51_41_15_checked :
    (Witness.linear .positive case_51_41_15).check 51 41 15 = true := by
  change case_51_41_15.check 51 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_51_41_16_checked :
    (Witness.linear .positive case_51_41_16).check 51 41 16 = true := by
  change case_51_41_16.check 51 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_51_41_17_checked :
    (Witness.linear .positive case_51_41_17).check 51 41 17 = true := by
  change case_51_41_17.check 51 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_51_41_18_checked :
    (Witness.linear .positive case_51_41_18).check 51 41 18 = true := by
  change case_51_41_18.check 51 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_51_41_19_checked :
    (Witness.linear .positive case_51_41_19).check 51 41 19 = true := by
  change case_51_41_19.check 51 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_51_41_20_checked :
    (Witness.linear .positive case_51_41_20).check 51 41 20 = true := by
  change case_51_41_20.check 51 41 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_21 : Certificate := {
  objectiveScale := 12
  eta := 573166440
  rows := #[⟨.assumptionRow 21, 13⟩]
  caps := #[0, 0, 169344630, 50075025, 16105635, 5141305, 1634380, 518738, 109174560, 200980440, 153216570] }

theorem case_51_41_21_checked :
    (Witness.linear .conditional case_51_41_21).check 51 41 21 = true := by
  change case_51_41_21.check 51 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_22 : Certificate := {
  objectiveScale := 4
  eta := 32256120
  rows := #[⟨.assumptionRow 22, 3⟩]
  caps := #[0, 0, 10795395, 3641820, 1381380, 480700, 158631, 63954, 136468200, 131505720, 91185570] }

theorem case_51_41_22_checked :
    (Witness.linear .conditional case_51_41_22).check 51 41 22 = true := by
  change case_51_41_22.check 51 41 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 129644790, 129644790, 94287120, 58929450] }

theorem case_51_41_23_checked :
    (Witness.linear .negative case_51_41_23).check 51 41 23 = true := by
  change case_51_41_23.check 51 41 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670] }

theorem case_51_41_24_checked :
    (Witness.linear .negative case_51_41_24).check 51 41 24 = true := by
  change case_51_41_24.check 51 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_41_25_checked :
    (Witness.linear .negative case_51_41_25).check 51 41 25 = true := by
  change case_51_41_25.check 51 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_41_26_checked :
    (Witness.linear .negative case_51_41_26).check 51 41 26 = true := by
  change case_51_41_26.check 51 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_42_1_checked :
    (Witness.rising).check 51 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_42_2_checked :
    (Witness.rising).check 51 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_42_3_checked :
    (Witness.rising).check 51 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_42_4_checked :
    (Witness.rising).check 51 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_42_5_checked :
    (Witness.rising).check 51 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_42_6_checked :
    (Witness.rising).check 51 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_42_7_checked :
    (Witness.rising).check 51 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_42_8_checked :
    (Witness.rising).check 51 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_42_9_checked :
    (Witness.rising).check 51 42 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_51_42_10_checked :
    (Witness.linear .positive case_51_42_10).check 51 42 10 = true := by
  change case_51_42_10.check 51 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_51_42_11_checked :
    (Witness.linear .positive case_51_42_11).check 51 42 11 = true := by
  change case_51_42_11.check 51 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_51_42_12_checked :
    (Witness.linear .positive case_51_42_12).check 51 42 12 = true := by
  change case_51_42_12.check 51 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_51_42_13_checked :
    (Witness.linear .positive case_51_42_13).check 51 42 13 = true := by
  change case_51_42_13.check 51 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_51_42_14_checked :
    (Witness.linear .positive case_51_42_14).check 51 42 14 = true := by
  change case_51_42_14.check 51 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_51_42_15_checked :
    (Witness.linear .positive case_51_42_15).check 51 42 15 = true := by
  change case_51_42_15.check 51 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_51_42_16_checked :
    (Witness.linear .positive case_51_42_16).check 51 42 16 = true := by
  change case_51_42_16.check 51 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_51_42_17_checked :
    (Witness.linear .positive case_51_42_17).check 51 42 17 = true := by
  change case_51_42_17.check 51 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_51_42_18_checked :
    (Witness.linear .positive case_51_42_18).check 51 42 18 = true := by
  change case_51_42_18.check 51 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_51_42_19_checked :
    (Witness.linear .positive case_51_42_19).check 51 42 19 = true := by
  change case_51_42_19.check 51 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_51_42_20_checked :
    (Witness.linear .positive case_51_42_20).check 51 42 20 = true := by
  change case_51_42_20.check 51 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_21 : Certificate := {
  objectiveScale := 3
  eta := 1275977670
  rows := #[⟨.assumptionRow 21, 5⟩]
  caps := #[0, 0, 354817320, 99249600, 28514250, 8259300, 2414425, 713184, 213180, 64600] }

theorem case_51_42_21_checked :
    (Witness.linear .conditional case_51_42_21).check 51 42 21 = true := by
  change case_51_42_21.check 51 42 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_22 : Certificate := {
  objectiveScale := 8
  eta := 238199040
  rows := #[⟨.assumptionRow 22, 7⟩]
  caps := #[0, 0, 76918440, 26403195, 8727810, 2812095, 889295, 326876, 463991880, 436698240] }

theorem case_51_42_22_checked :
    (Witness.linear .conditional case_51_42_22).check 51 42 22 = true := by
  change case_51_42_22.check 51 42 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 477638700, 477638700, 347993910, 218349120] }

theorem case_51_42_23_checked :
    (Witness.linear .negative case_51_42_23).check 51 42 23 = true := by
  change case_51_42_23.check 51 42 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 129644790, 129644790] }

theorem case_51_42_24_checked :
    (Witness.linear .negative case_51_42_24).check 51 42 24 = true := by
  change case_51_42_24.check 51 42 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_42_25_checked :
    (Witness.linear .negative case_51_42_25).check 51 42 25 = true := by
  change case_51_42_25.check 51 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_42_26_checked :
    (Witness.linear .negative case_51_42_26).check 51 42 26 = true := by
  change case_51_42_26.check 51 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_42_27_checked :
    (Witness.linear .negative case_51_42_27).check 51 42 27 = true := by
  change case_51_42_27.check 51 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_43_1_checked :
    (Witness.rising).check 51 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_43_2_checked :
    (Witness.rising).check 51 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_43_3_checked :
    (Witness.rising).check 51 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_43_4_checked :
    (Witness.rising).check 51 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_43_5_checked :
    (Witness.rising).check 51 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_43_6_checked :
    (Witness.rising).check 51 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_43_7_checked :
    (Witness.rising).check 51 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_43_8_checked :
    (Witness.rising).check 51 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_43_9_checked :
    (Witness.rising).check 51 43 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_51_43_10_checked :
    (Witness.linear .positive case_51_43_10).check 51 43 10 = true := by
  change case_51_43_10.check 51 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_51_43_11_checked :
    (Witness.linear .positive case_51_43_11).check 51 43 11 = true := by
  change case_51_43_11.check 51 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_51_43_12_checked :
    (Witness.linear .positive case_51_43_12).check 51 43 12 = true := by
  change case_51_43_12.check 51 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_51_43_13_checked :
    (Witness.linear .positive case_51_43_13).check 51 43 13 = true := by
  change case_51_43_13.check 51 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_51_43_14_checked :
    (Witness.linear .positive case_51_43_14).check 51 43 14 = true := by
  change case_51_43_14.check 51 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_51_43_15_checked :
    (Witness.linear .positive case_51_43_15).check 51 43 15 = true := by
  change case_51_43_15.check 51 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_51_43_16_checked :
    (Witness.linear .positive case_51_43_16).check 51 43 16 = true := by
  change case_51_43_16.check 51 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_51_43_17_checked :
    (Witness.linear .positive case_51_43_17).check 51 43 17 = true := by
  change case_51_43_17.check 51 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_51_43_18_checked :
    (Witness.linear .positive case_51_43_18).check 51 43 18 = true := by
  change case_51_43_18.check 51 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_51_43_19_checked :
    (Witness.linear .positive case_51_43_19).check 51 43 19 = true := by
  change case_51_43_19.check 51 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_51_43_20_checked :
    (Witness.linear .positive case_51_43_20).check 51 43 20 = true := by
  change case_51_43_20.check 51 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_51_43_21_checked :
    (Witness.linear .positive case_51_43_21).check 51 43 21 = true := by
  change case_51_43_21.check 51 43 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_22 : Certificate := {
  objectiveScale := 50
  eta := 3754116120
  rows := #[⟨.assumptionRow 22, 49⟩]
  caps := #[0, 0, 1119039240, 369084450, 119269605, 38005890, 11993465, 189814860, 5061729600] }

theorem case_51_43_22_checked :
    (Witness.linear .conditional case_51_43_22).check 51 43 22 = true := by
  change case_51_43_22.check 51 43 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 1767263190, 1767263190, 1289624490, 811985790] }

theorem case_51_43_23_checked :
    (Witness.linear .negative case_51_43_23).check 51 43 23 = true := by
  change case_51_43_23.check 51 43 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 477638700, 477638700] }

theorem case_51_43_24_checked :
    (Witness.linear .negative case_51_43_24).check 51 43 24 = true := by
  change case_51_43_24.check 51 43 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_43_25_checked :
    (Witness.linear .negative case_51_43_25).check 51 43 25 = true := by
  change case_51_43_25.check 51 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_43_26_checked :
    (Witness.linear .negative case_51_43_26).check 51 43 26 = true := by
  change case_51_43_26.check 51 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_43_27_checked :
    (Witness.linear .negative case_51_43_27).check 51 43 27 = true := by
  change case_51_43_27.check 51 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_43_28_checked :
    (Witness.linear .negative case_51_43_28).check 51 43 28 = true := by
  change case_51_43_28.check 51 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_44_1_checked :
    (Witness.rising).check 51 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_44_2_checked :
    (Witness.rising).check 51 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_44_3_checked :
    (Witness.rising).check 51 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_44_4_checked :
    (Witness.rising).check 51 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_44_5_checked :
    (Witness.rising).check 51 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_44_6_checked :
    (Witness.rising).check 51 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_44_7_checked :
    (Witness.rising).check 51 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_44_8_checked :
    (Witness.rising).check 51 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_44_9_checked :
    (Witness.rising).check 51 44 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_51_44_10_checked :
    (Witness.linear .positive case_51_44_10).check 51 44 10 = true := by
  change case_51_44_10.check 51 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_51_44_11_checked :
    (Witness.linear .positive case_51_44_11).check 51 44 11 = true := by
  change case_51_44_11.check 51 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_51_44_12_checked :
    (Witness.linear .positive case_51_44_12).check 51 44 12 = true := by
  change case_51_44_12.check 51 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_51_44_13_checked :
    (Witness.linear .positive case_51_44_13).check 51 44 13 = true := by
  change case_51_44_13.check 51 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_51_44_14_checked :
    (Witness.linear .positive case_51_44_14).check 51 44 14 = true := by
  change case_51_44_14.check 51 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_51_44_15_checked :
    (Witness.linear .positive case_51_44_15).check 51 44 15 = true := by
  change case_51_44_15.check 51 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_51_44_16_checked :
    (Witness.linear .positive case_51_44_16).check 51 44 16 = true := by
  change case_51_44_16.check 51 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_51_44_17_checked :
    (Witness.linear .positive case_51_44_17).check 51 44 17 = true := by
  change case_51_44_17.check 51 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_51_44_18_checked :
    (Witness.linear .positive case_51_44_18).check 51 44 18 = true := by
  change case_51_44_18.check 51 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_51_44_19_checked :
    (Witness.linear .positive case_51_44_19).check 51 44 19 = true := by
  change case_51_44_19.check 51 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_51_44_20_checked :
    (Witness.linear .positive case_51_44_20).check 51 44 20 = true := by
  change case_51_44_20.check 51 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_51_44_21_checked :
    (Witness.linear .positive case_51_44_21).check 51 44 21 = true := by
  change case_51_44_21.check 51 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_22 : Certificate := {
  objectiveScale := 10
  eta := 64103455710
  rows := #[⟨.assumptionRow 22, 27⟩]
  caps := #[0, 0, 17420165730, 4776387000, 1316918130, 365362590, 102081015, 28750230] }

theorem case_51_44_22_checked :
    (Witness.linear .conditional case_51_44_22).check 51 44 22 = true := by
  change case_51_44_22.check 51 44 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_23 : Certificate := {
  objectiveScale := 19
  eta := 32957340
  rows := #[⟨.assumptionRow 23, 11⟩]
  caps := #[0, 0, 12486240, 5229510, 1825395, 841225, 19187428920, 18934962750] }

theorem case_51_44_23_checked :
    (Witness.linear .conditional case_51_44_23).check 51 44 23 = true := by
  change case_51_44_23.check 51 44 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 1767263190, 1767263190] }

theorem case_51_44_24_checked :
    (Witness.linear .negative case_51_44_24).check 51 44 24 = true := by
  change case_51_44_24.check 51 44 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_44_25_checked :
    (Witness.linear .negative case_51_44_25).check 51 44 25 = true := by
  change case_51_44_25.check 51 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_44_26_checked :
    (Witness.linear .negative case_51_44_26).check 51 44 26 = true := by
  change case_51_44_26.check 51 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_44_27_checked :
    (Witness.linear .negative case_51_44_27).check 51 44 27 = true := by
  change case_51_44_27.check 51 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_51_44_28_checked :
    (Witness.linear .negative case_51_44_28).check 51 44 28 = true := by
  change case_51_44_28.check 51 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_45_1_checked :
    (Witness.rising).check 51 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_45_2_checked :
    (Witness.rising).check 51 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_45_3_checked :
    (Witness.rising).check 51 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_45_4_checked :
    (Witness.rising).check 51 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_45_5_checked :
    (Witness.rising).check 51 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_45_6_checked :
    (Witness.rising).check 51 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_45_7_checked :
    (Witness.rising).check 51 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_45_8_checked :
    (Witness.rising).check 51 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_45_9_checked :
    (Witness.rising).check 51 45 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_51_45_10_checked :
    (Witness.linear .positive case_51_45_10).check 51 45 10 = true := by
  change case_51_45_10.check 51 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_51_45_11_checked :
    (Witness.linear .positive case_51_45_11).check 51 45 11 = true := by
  change case_51_45_11.check 51 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_51_45_12_checked :
    (Witness.linear .positive case_51_45_12).check 51 45 12 = true := by
  change case_51_45_12.check 51 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_51_45_13_checked :
    (Witness.linear .positive case_51_45_13).check 51 45 13 = true := by
  change case_51_45_13.check 51 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_51_45_14_checked :
    (Witness.linear .positive case_51_45_14).check 51 45 14 = true := by
  change case_51_45_14.check 51 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_51_45_15_checked :
    (Witness.linear .positive case_51_45_15).check 51 45 15 = true := by
  change case_51_45_15.check 51 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_51_45_16_checked :
    (Witness.linear .positive case_51_45_16).check 51 45 16 = true := by
  change case_51_45_16.check 51 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_51_45_17_checked :
    (Witness.linear .positive case_51_45_17).check 51 45 17 = true := by
  change case_51_45_17.check 51 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_51_45_18_checked :
    (Witness.linear .positive case_51_45_18).check 51 45 18 = true := by
  change case_51_45_18.check 51 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_51_45_19_checked :
    (Witness.linear .positive case_51_45_19).check 51 45 19 = true := by
  change case_51_45_19.check 51 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_51_45_20_checked :
    (Witness.linear .positive case_51_45_20).check 51 45 20 = true := by
  change case_51_45_20.check 51 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_51_45_21_checked :
    (Witness.linear .positive case_51_45_21).check 51 45 21 = true := by
  change case_51_45_21.check 51 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_51_45_22_checked :
    (Witness.linear .positive case_51_45_22).check 51 45 22 = true := by
  change case_51_45_22.check 51 45 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_23 : Certificate := {
  objectiveScale := 992
  eta := 76109340000
  rows := #[⟨.assumptionRow 23, 845⟩]
  caps := #[0, 0, 24514651200, 7701148650, 2541079905, 890173830, 492957660] }

theorem case_51_45_23_checked :
    (Witness.linear .conditional case_51_45_23).check 51 45 23 = true := by
  change case_51_45_23.check 51 45 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 6564120420, 6564120420] }

theorem case_51_45_24_checked :
    (Witness.linear .negative case_51_45_24).check 51 45 24 = true := by
  change case_51_45_24.check 51 45 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_51_45_25_checked :
    (Witness.linear .negative case_51_45_25).check 51 45 25 = true := by
  change case_51_45_25.check 51 45 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_51_45_26_checked :
    (Witness.linear .negative case_51_45_26).check 51 45 26 = true := by
  change case_51_45_26.check 51 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_51_45_27_checked :
    (Witness.linear .negative case_51_45_27).check 51 45 27 = true := by
  change case_51_45_27.check 51 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_51_45_28_checked :
    (Witness.linear .negative case_51_45_28).check 51 45 28 = true := by
  change case_51_45_28.check 51 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_51_45_29_checked :
    (Witness.linear .negative case_51_45_29).check 51 45 29 = true := by
  change case_51_45_29.check 51 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_46_1_checked :
    (Witness.rising).check 51 46 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_46_2_checked :
    (Witness.rising).check 51 46 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_46_3_checked :
    (Witness.rising).check 51 46 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_46_4_checked :
    (Witness.rising).check 51 46 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_46_5_checked :
    (Witness.rising).check 51 46 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_46_6_checked :
    (Witness.rising).check 51 46 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_46_7_checked :
    (Witness.rising).check 51 46 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_46_8_checked :
    (Witness.rising).check 51 46 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_51_46_9_checked :
    (Witness.linear .positive case_51_46_9).check 51 46 9 = true := by
  change case_51_46_9.check 51 46 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_51_46_10_checked :
    (Witness.linear .positive case_51_46_10).check 51 46 10 = true := by
  change case_51_46_10.check 51 46 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_51_46_11_checked :
    (Witness.linear .positive case_51_46_11).check 51 46 11 = true := by
  change case_51_46_11.check 51 46 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_51_46_12_checked :
    (Witness.linear .positive case_51_46_12).check 51 46 12 = true := by
  change case_51_46_12.check 51 46 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_51_46_13_checked :
    (Witness.linear .positive case_51_46_13).check 51 46 13 = true := by
  change case_51_46_13.check 51 46 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_51_46_14_checked :
    (Witness.linear .positive case_51_46_14).check 51 46 14 = true := by
  change case_51_46_14.check 51 46 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_51_46_15_checked :
    (Witness.linear .positive case_51_46_15).check 51 46 15 = true := by
  change case_51_46_15.check 51 46 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_51_46_16_checked :
    (Witness.linear .positive case_51_46_16).check 51 46 16 = true := by
  change case_51_46_16.check 51 46 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_51_46_17_checked :
    (Witness.linear .positive case_51_46_17).check 51 46 17 = true := by
  change case_51_46_17.check 51 46 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_51_46_18_checked :
    (Witness.linear .positive case_51_46_18).check 51 46 18 = true := by
  change case_51_46_18.check 51 46 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_51_46_19_checked :
    (Witness.linear .positive case_51_46_19).check 51 46 19 = true := by
  change case_51_46_19.check 51 46 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_51_46_20_checked :
    (Witness.linear .positive case_51_46_20).check 51 46 20 = true := by
  change case_51_46_20.check 51 46 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845] }

theorem case_51_46_21_checked :
    (Witness.linear .positive case_51_46_21).check 51 46 21 = true := by
  change case_51_46_21.check 51 46 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670] }

theorem case_51_46_22_checked :
    (Witness.linear .positive case_51_46_22).check 51 46 22 = true := by
  change case_51_46_22.check 51 46 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790] }

theorem case_51_46_23_checked :
    (Witness.linear .positive case_51_46_23).check 51 46 23 = true := by
  change case_51_46_23.check 51 46 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 24466267020, 24466267020] }

theorem case_51_46_24_checked :
    (Witness.linear .negative case_51_46_24).check 51 46 24 = true := by
  change case_51_46_24.check 51 46 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_51_46_25_checked :
    (Witness.linear .negative case_51_46_25).check 51 46 25 = true := by
  change case_51_46_25.check 51 46 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_51_46_26_checked :
    (Witness.linear .negative case_51_46_26).check 51 46 26 = true := by
  change case_51_46_26.check 51 46 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_51_46_27_checked :
    (Witness.linear .negative case_51_46_27).check 51 46 27 = true := by
  change case_51_46_27.check 51 46 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_51_46_28_checked :
    (Witness.linear .negative case_51_46_28).check 51 46 28 = true := by
  change case_51_46_28.check 51 46 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_51_46_29_checked :
    (Witness.linear .negative case_51_46_29).check 51 46 29 = true := by
  change case_51_46_29.check 51 46 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_46_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_51_46_30_checked :
    (Witness.linear .negative case_51_46_30).check 51 46 30 = true := by
  change case_51_46_30.check 51 46 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_47_1_checked :
    (Witness.rising).check 51 47 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_47_2_checked :
    (Witness.rising).check 51 47 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_47_3_checked :
    (Witness.rising).check 51 47 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_47_4_checked :
    (Witness.rising).check 51 47 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_47_5_checked :
    (Witness.rising).check 51 47 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_47_6_checked :
    (Witness.rising).check 51 47 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_47_7_checked :
    (Witness.rising).check 51 47 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_47_8_checked :
    (Witness.rising).check 51 47 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_51_47_9_checked :
    (Witness.linear .positive case_51_47_9).check 51 47 9 = true := by
  change case_51_47_9.check 51 47 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_51_47_10_checked :
    (Witness.linear .positive case_51_47_10).check 51 47 10 = true := by
  change case_51_47_10.check 51 47 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_51_47_11_checked :
    (Witness.linear .positive case_51_47_11).check 51 47 11 = true := by
  change case_51_47_11.check 51 47 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_51_47_12_checked :
    (Witness.linear .positive case_51_47_12).check 51 47 12 = true := by
  change case_51_47_12.check 51 47 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_51_47_13_checked :
    (Witness.linear .positive case_51_47_13).check 51 47 13 = true := by
  change case_51_47_13.check 51 47 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_51_47_14_checked :
    (Witness.linear .positive case_51_47_14).check 51 47 14 = true := by
  change case_51_47_14.check 51 47 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_51_47_15_checked :
    (Witness.linear .positive case_51_47_15).check 51 47 15 = true := by
  change case_51_47_15.check 51 47 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_51_47_16_checked :
    (Witness.linear .positive case_51_47_16).check 51 47 16 = true := by
  change case_51_47_16.check 51 47 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_51_47_17_checked :
    (Witness.linear .positive case_51_47_17).check 51 47 17 = true := by
  change case_51_47_17.check 51 47 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_51_47_18_checked :
    (Witness.linear .positive case_51_47_18).check 51 47 18 = true := by
  change case_51_47_18.check 51 47 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_51_47_19_checked :
    (Witness.linear .positive case_51_47_19).check 51 47 19 = true := by
  change case_51_47_19.check 51 47 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_51_47_20_checked :
    (Witness.linear .positive case_51_47_20).check 51 47 20 = true := by
  change case_51_47_20.check 51 47 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_51_47_21_checked :
    (Witness.linear .positive case_51_47_21).check 51 47 21 = true := by
  change case_51_47_21.check 51 47 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790] }

theorem case_51_47_22_checked :
    (Witness.linear .positive case_51_47_22).check 51 47 22 = true := by
  change case_51_47_22.check 51 47 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700] }

theorem case_51_47_23_checked :
    (Witness.linear .positive case_51_47_23).check 51 47 23 = true := by
  change case_51_47_23.check 51 47 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 91482563640, 91482563640] }

theorem case_51_47_24_checked :
    (Witness.linear .negative case_51_47_24).check 51 47 24 = true := by
  change case_51_47_24.check 51 47 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_51_47_25_checked :
    (Witness.linear .negative case_51_47_25).check 51 47 25 = true := by
  change case_51_47_25.check 51 47 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_51_47_26_checked :
    (Witness.linear .negative case_51_47_26).check 51 47 26 = true := by
  change case_51_47_26.check 51 47 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_51_47_27_checked :
    (Witness.linear .negative case_51_47_27).check 51 47 27 = true := by
  change case_51_47_27.check 51 47 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_51_47_28_checked :
    (Witness.linear .negative case_51_47_28).check 51 47 28 = true := by
  change case_51_47_28.check 51 47 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_51_47_29_checked :
    (Witness.linear .negative case_51_47_29).check 51 47 29 = true := by
  change case_51_47_29.check 51 47 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_47_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_51_47_30_checked :
    (Witness.linear .negative case_51_47_30).check 51 47 30 = true := by
  change case_51_47_30.check 51 47 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_48_1_checked :
    (Witness.rising).check 51 48 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_48_2_checked :
    (Witness.rising).check 51 48 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_48_3_checked :
    (Witness.rising).check 51 48 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_48_4_checked :
    (Witness.rising).check 51 48 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_48_5_checked :
    (Witness.rising).check 51 48 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_48_6_checked :
    (Witness.rising).check 51 48 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_48_7_checked :
    (Witness.rising).check 51 48 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_48_8_checked :
    (Witness.rising).check 51 48 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_51_48_9_checked :
    (Witness.linear .positive case_51_48_9).check 51 48 9 = true := by
  change case_51_48_9.check 51 48 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_51_48_10_checked :
    (Witness.linear .positive case_51_48_10).check 51 48 10 = true := by
  change case_51_48_10.check 51 48 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_51_48_11_checked :
    (Witness.linear .positive case_51_48_11).check 51 48 11 = true := by
  change case_51_48_11.check 51 48 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_51_48_12_checked :
    (Witness.linear .positive case_51_48_12).check 51 48 12 = true := by
  change case_51_48_12.check 51 48 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_51_48_13_checked :
    (Witness.linear .positive case_51_48_13).check 51 48 13 = true := by
  change case_51_48_13.check 51 48 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_51_48_14_checked :
    (Witness.linear .positive case_51_48_14).check 51 48 14 = true := by
  change case_51_48_14.check 51 48 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_51_48_15_checked :
    (Witness.linear .positive case_51_48_15).check 51 48 15 = true := by
  change case_51_48_15.check 51 48 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_51_48_16_checked :
    (Witness.linear .positive case_51_48_16).check 51 48 16 = true := by
  change case_51_48_16.check 51 48 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_51_48_17_checked :
    (Witness.linear .positive case_51_48_17).check 51 48 17 = true := by
  change case_51_48_17.check 51 48 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_51_48_18_checked :
    (Witness.linear .positive case_51_48_18).check 51 48 18 = true := by
  change case_51_48_18.check 51 48 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_51_48_19_checked :
    (Witness.linear .positive case_51_48_19).check 51 48 19 = true := by
  change case_51_48_19.check 51 48 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_51_48_20_checked :
    (Witness.linear .positive case_51_48_20).check 51 48 20 = true := by
  change case_51_48_20.check 51 48 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_51_48_21_checked :
    (Witness.linear .positive case_51_48_21).check 51 48 21 = true := by
  change case_51_48_21.check 51 48 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700] }

theorem case_51_48_22_checked :
    (Witness.linear .positive case_51_48_22).check 51 48 22 = true := by
  change case_51_48_22.check 51 48 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190] }

theorem case_51_48_23_checked :
    (Witness.linear .positive case_51_48_23).check 51 48 23 = true := by
  change case_51_48_23.check 51 48 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420] }

theorem case_51_48_24_checked :
    (Witness.linear .positive case_51_48_24).check 51 48 24 = true := by
  change case_51_48_24.check 51 48 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_51_48_25_checked :
    (Witness.linear .negative case_51_48_25).check 51 48 25 = true := by
  change case_51_48_25.check 51 48 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_51_48_26_checked :
    (Witness.linear .negative case_51_48_26).check 51 48 26 = true := by
  change case_51_48_26.check 51 48 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_51_48_27_checked :
    (Witness.linear .negative case_51_48_27).check 51 48 27 = true := by
  change case_51_48_27.check 51 48 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_51_48_28_checked :
    (Witness.linear .negative case_51_48_28).check 51 48 28 = true := by
  change case_51_48_28.check 51 48 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_51_48_29_checked :
    (Witness.linear .negative case_51_48_29).check 51 48 29 = true := by
  change case_51_48_29.check 51 48 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_51_48_30_checked :
    (Witness.linear .negative case_51_48_30).check 51 48 30 = true := by
  change case_51_48_30.check 51 48 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_48_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_51_48_31_checked :
    (Witness.linear .negative case_51_48_31).check 51 48 31 = true := by
  change case_51_48_31.check 51 48 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_49_1_checked :
    (Witness.rising).check 51 49 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_49_2_checked :
    (Witness.rising).check 51 49 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_49_3_checked :
    (Witness.rising).check 51 49 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_49_4_checked :
    (Witness.rising).check 51 49 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_49_5_checked :
    (Witness.rising).check 51 49 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_49_6_checked :
    (Witness.rising).check 51 49 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_49_7_checked :
    (Witness.rising).check 51 49 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_49_8_checked :
    (Witness.rising).check 51 49 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_51_49_9_checked :
    (Witness.linear .positive case_51_49_9).check 51 49 9 = true := by
  change case_51_49_9.check 51 49 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_51_49_10_checked :
    (Witness.linear .positive case_51_49_10).check 51 49 10 = true := by
  change case_51_49_10.check 51 49 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_51_49_11_checked :
    (Witness.linear .positive case_51_49_11).check 51 49 11 = true := by
  change case_51_49_11.check 51 49 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_51_49_12_checked :
    (Witness.linear .positive case_51_49_12).check 51 49 12 = true := by
  change case_51_49_12.check 51 49 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_51_49_13_checked :
    (Witness.linear .positive case_51_49_13).check 51 49 13 = true := by
  change case_51_49_13.check 51 49 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_51_49_14_checked :
    (Witness.linear .positive case_51_49_14).check 51 49 14 = true := by
  change case_51_49_14.check 51 49 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_51_49_15_checked :
    (Witness.linear .positive case_51_49_15).check 51 49 15 = true := by
  change case_51_49_15.check 51 49 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_51_49_16_checked :
    (Witness.linear .positive case_51_49_16).check 51 49 16 = true := by
  change case_51_49_16.check 51 49 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_51_49_17_checked :
    (Witness.linear .positive case_51_49_17).check 51 49 17 = true := by
  change case_51_49_17.check 51 49 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_51_49_18_checked :
    (Witness.linear .positive case_51_49_18).check 51 49 18 = true := by
  change case_51_49_18.check 51 49 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_51_49_19_checked :
    (Witness.linear .positive case_51_49_19).check 51 49 19 = true := by
  change case_51_49_19.check 51 49 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_51_49_20_checked :
    (Witness.linear .positive case_51_49_20).check 51 49 20 = true := by
  change case_51_49_20.check 51 49 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_51_49_21_checked :
    (Witness.linear .positive case_51_49_21).check 51 49 21 = true := by
  change case_51_49_21.check 51 49 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_51_49_22_checked :
    (Witness.linear .positive case_51_49_22).check 51 49 22 = true := by
  change case_51_49_22.check 51 49 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420] }

theorem case_51_49_23_checked :
    (Witness.linear .positive case_51_49_23).check 51 49 23 = true := by
  change case_51_49_23.check 51 49 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020] }

theorem case_51_49_24_checked :
    (Witness.linear .positive case_51_49_24).check 51 49 24 = true := by
  change case_51_49_24.check 51 49 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_51_49_25_checked :
    (Witness.linear .negative case_51_49_25).check 51 49 25 = true := by
  change case_51_49_25.check 51 49 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_51_49_26_checked :
    (Witness.linear .negative case_51_49_26).check 51 49 26 = true := by
  change case_51_49_26.check 51 49 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_51_49_27_checked :
    (Witness.linear .negative case_51_49_27).check 51 49 27 = true := by
  change case_51_49_27.check 51 49 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_51_49_28_checked :
    (Witness.linear .negative case_51_49_28).check 51 49 28 = true := by
  change case_51_49_28.check 51 49 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_51_49_29_checked :
    (Witness.linear .negative case_51_49_29).check 51 49 29 = true := by
  change case_51_49_29.check 51 49 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_51_49_30_checked :
    (Witness.linear .negative case_51_49_30).check 51 49 30 = true := by
  change case_51_49_30.check 51 49 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_51_49_31_checked :
    (Witness.linear .negative case_51_49_31).check 51 49 31 = true := by
  change case_51_49_31.check 51 49 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_49_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_51_49_32_checked :
    (Witness.linear .negative case_51_49_32).check 51 49 32 = true := by
  change case_51_49_32.check 51 49 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_50_1_checked :
    (Witness.rising).check 51 50 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_50_2_checked :
    (Witness.rising).check 51 50 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_50_3_checked :
    (Witness.rising).check 51 50 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_50_4_checked :
    (Witness.rising).check 51 50 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_50_5_checked :
    (Witness.rising).check 51 50 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_50_6_checked :
    (Witness.rising).check 51 50 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_50_7_checked :
    (Witness.rising).check 51 50 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_51_50_8_checked :
    (Witness.rising).check 51 50 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_9_checked :
    (Witness.linear .positive case_51_50_9).check 51 50 9 = true := by
  change case_51_50_9.check 51 50 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_10_checked :
    (Witness.linear .positive case_51_50_10).check 51 50 10 = true := by
  change case_51_50_10.check 51 50 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_11_checked :
    (Witness.linear .positive case_51_50_11).check 51 50 11 = true := by
  change case_51_50_11.check 51 50 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_12_checked :
    (Witness.linear .positive case_51_50_12).check 51 50 12 = true := by
  change case_51_50_12.check 51 50 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_13_checked :
    (Witness.linear .positive case_51_50_13).check 51 50 13 = true := by
  change case_51_50_13.check 51 50 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_14_checked :
    (Witness.linear .positive case_51_50_14).check 51 50 14 = true := by
  change case_51_50_14.check 51 50 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_15_checked :
    (Witness.linear .positive case_51_50_15).check 51 50 15 = true := by
  change case_51_50_15.check 51 50 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_16_checked :
    (Witness.linear .positive case_51_50_16).check 51 50 16 = true := by
  change case_51_50_16.check 51 50 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_17_checked :
    (Witness.linear .positive case_51_50_17).check 51 50 17 = true := by
  change case_51_50_17.check 51 50 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_18_checked :
    (Witness.linear .positive case_51_50_18).check 51 50 18 = true := by
  change case_51_50_18.check 51 50 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_19_checked :
    (Witness.linear .positive case_51_50_19).check 51 50 19 = true := by
  change case_51_50_19.check 51 50 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_20_checked :
    (Witness.linear .positive case_51_50_20).check 51 50 20 = true := by
  change case_51_50_20.check 51 50 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_21_checked :
    (Witness.linear .positive case_51_50_21).check 51 50 21 = true := by
  change case_51_50_21.check 51 50 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_22_checked :
    (Witness.linear .positive case_51_50_22).check 51 50 22 = true := by
  change case_51_50_22.check 51 50 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_23_checked :
    (Witness.linear .positive case_51_50_23).check 51 50 23 = true := by
  change case_51_50_23.check 51 50 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_24_checked :
    (Witness.linear .positive case_51_50_24).check 51 50 24 = true := by
  change case_51_50_24.check 51 50 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_25_checked :
    (Witness.linear .positive case_51_50_25).check 51 50 25 = true := by
  change case_51_50_25.check 51 50 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_26_checked :
    (Witness.linear .negative case_51_50_26).check 51 50 26 = true := by
  change case_51_50_26.check 51 50 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_27_checked :
    (Witness.linear .negative case_51_50_27).check 51 50 27 = true := by
  change case_51_50_27.check 51 50 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_28_checked :
    (Witness.linear .negative case_51_50_28).check 51 50 28 = true := by
  change case_51_50_28.check 51 50 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_29_checked :
    (Witness.linear .negative case_51_50_29).check 51 50 29 = true := by
  change case_51_50_29.check 51 50 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_30_checked :
    (Witness.linear .negative case_51_50_30).check 51 50 30 = true := by
  change case_51_50_30.check 51 50 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_31_checked :
    (Witness.linear .negative case_51_50_31).check 51 50 31 = true := by
  change case_51_50_31.check 51 50 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_51_50_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_51_50_32_checked :
    (Witness.linear .negative case_51_50_32).check 51 50 32 = true := by
  change case_51_50_32.check 51 50 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_51 (a k : ℕ) (h : Domain 51 a k) :
    ∃ w : Witness, w.check 51 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 26 ≤ a := by omega
  have haHi : a ≤ 50 := by omega
  interval_cases a

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_26_1_checked⟩

    · exact ⟨Witness.rising, case_51_26_2_checked⟩

    · exact ⟨Witness.rising, case_51_26_3_checked⟩

    · exact ⟨Witness.rising, case_51_26_4_checked⟩

    · exact ⟨Witness.rising, case_51_26_5_checked⟩

    · exact ⟨Witness.rising, case_51_26_6_checked⟩

    · exact ⟨Witness.rising, case_51_26_7_checked⟩

    · exact ⟨Witness.rising, case_51_26_8_checked⟩

    · exact ⟨Witness.rising, case_51_26_9_checked⟩

    · exact ⟨Witness.rising, case_51_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_26_11, case_51_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_26_12, case_51_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_26_13, case_51_26_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_26_14, case_51_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_51_26_15, case_51_26_15_checked⟩

    · exact ⟨Witness.linear .conditional case_51_26_16, case_51_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_27_1_checked⟩

    · exact ⟨Witness.rising, case_51_27_2_checked⟩

    · exact ⟨Witness.rising, case_51_27_3_checked⟩

    · exact ⟨Witness.rising, case_51_27_4_checked⟩

    · exact ⟨Witness.rising, case_51_27_5_checked⟩

    · exact ⟨Witness.rising, case_51_27_6_checked⟩

    · exact ⟨Witness.rising, case_51_27_7_checked⟩

    · exact ⟨Witness.rising, case_51_27_8_checked⟩

    · exact ⟨Witness.rising, case_51_27_9_checked⟩

    · exact ⟨Witness.rising, case_51_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_27_11, case_51_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_27_12, case_51_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_27_13, case_51_27_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_27_14, case_51_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_51_27_15, case_51_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_51_27_16, case_51_27_16_checked⟩

    · exact ⟨Witness.linear .conditional case_51_27_17, case_51_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_28_1_checked⟩

    · exact ⟨Witness.rising, case_51_28_2_checked⟩

    · exact ⟨Witness.rising, case_51_28_3_checked⟩

    · exact ⟨Witness.rising, case_51_28_4_checked⟩

    · exact ⟨Witness.rising, case_51_28_5_checked⟩

    · exact ⟨Witness.rising, case_51_28_6_checked⟩

    · exact ⟨Witness.rising, case_51_28_7_checked⟩

    · exact ⟨Witness.rising, case_51_28_8_checked⟩

    · exact ⟨Witness.rising, case_51_28_9_checked⟩

    · exact ⟨Witness.rising, case_51_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_28_11, case_51_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_28_12, case_51_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_28_13, case_51_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_28_14, case_51_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_51_28_15, case_51_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_51_28_16, case_51_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_51_28_17, case_51_28_17_checked⟩

    · exact ⟨Witness.linear .conditional case_51_28_18, case_51_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_29_1_checked⟩

    · exact ⟨Witness.rising, case_51_29_2_checked⟩

    · exact ⟨Witness.rising, case_51_29_3_checked⟩

    · exact ⟨Witness.rising, case_51_29_4_checked⟩

    · exact ⟨Witness.rising, case_51_29_5_checked⟩

    · exact ⟨Witness.rising, case_51_29_6_checked⟩

    · exact ⟨Witness.rising, case_51_29_7_checked⟩

    · exact ⟨Witness.rising, case_51_29_8_checked⟩

    · exact ⟨Witness.rising, case_51_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_29_10, case_51_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_29_11, case_51_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_29_12, case_51_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_29_13, case_51_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_29_14, case_51_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_51_29_15, case_51_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_51_29_16, case_51_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_51_29_17, case_51_29_17_checked⟩

    · exact ⟨Witness.linear .conditional case_51_29_18, case_51_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_30_1_checked⟩

    · exact ⟨Witness.rising, case_51_30_2_checked⟩

    · exact ⟨Witness.rising, case_51_30_3_checked⟩

    · exact ⟨Witness.rising, case_51_30_4_checked⟩

    · exact ⟨Witness.rising, case_51_30_5_checked⟩

    · exact ⟨Witness.rising, case_51_30_6_checked⟩

    · exact ⟨Witness.rising, case_51_30_7_checked⟩

    · exact ⟨Witness.rising, case_51_30_8_checked⟩

    · exact ⟨Witness.rising, case_51_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_30_10, case_51_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_30_11, case_51_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_30_12, case_51_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_30_13, case_51_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_30_14, case_51_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_51_30_15, case_51_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_51_30_16, case_51_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_51_30_17, case_51_30_17_checked⟩

    · exact ⟨Witness.linear .conditional case_51_30_18, case_51_30_18_checked⟩

    · exact ⟨Witness.linear .conditional case_51_30_19, case_51_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_31_1_checked⟩

    · exact ⟨Witness.rising, case_51_31_2_checked⟩

    · exact ⟨Witness.rising, case_51_31_3_checked⟩

    · exact ⟨Witness.rising, case_51_31_4_checked⟩

    · exact ⟨Witness.rising, case_51_31_5_checked⟩

    · exact ⟨Witness.rising, case_51_31_6_checked⟩

    · exact ⟨Witness.rising, case_51_31_7_checked⟩

    · exact ⟨Witness.rising, case_51_31_8_checked⟩

    · exact ⟨Witness.rising, case_51_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_31_10, case_51_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_31_11, case_51_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_31_12, case_51_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_31_13, case_51_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_31_14, case_51_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_31_15, case_51_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_51_31_16, case_51_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_51_31_17, case_51_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_51_31_18, case_51_31_18_checked⟩

    · exact ⟨Witness.linear .conditional case_51_31_19, case_51_31_19_checked⟩

    · exact ⟨Witness.linear .conditional case_51_31_20, case_51_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_32_1_checked⟩

    · exact ⟨Witness.rising, case_51_32_2_checked⟩

    · exact ⟨Witness.rising, case_51_32_3_checked⟩

    · exact ⟨Witness.rising, case_51_32_4_checked⟩

    · exact ⟨Witness.rising, case_51_32_5_checked⟩

    · exact ⟨Witness.rising, case_51_32_6_checked⟩

    · exact ⟨Witness.rising, case_51_32_7_checked⟩

    · exact ⟨Witness.rising, case_51_32_8_checked⟩

    · exact ⟨Witness.rising, case_51_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_32_10, case_51_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_32_11, case_51_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_32_12, case_51_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_32_13, case_51_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_32_14, case_51_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_32_15, case_51_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_51_32_16, case_51_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_51_32_17, case_51_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_51_32_18, case_51_32_18_checked⟩

    · exact ⟨Witness.linear .conditional case_51_32_19, case_51_32_19_checked⟩

    · exact ⟨Witness.linear .conditional case_51_32_20, case_51_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_33_1_checked⟩

    · exact ⟨Witness.rising, case_51_33_2_checked⟩

    · exact ⟨Witness.rising, case_51_33_3_checked⟩

    · exact ⟨Witness.rising, case_51_33_4_checked⟩

    · exact ⟨Witness.rising, case_51_33_5_checked⟩

    · exact ⟨Witness.rising, case_51_33_6_checked⟩

    · exact ⟨Witness.rising, case_51_33_7_checked⟩

    · exact ⟨Witness.rising, case_51_33_8_checked⟩

    · exact ⟨Witness.rising, case_51_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_33_10, case_51_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_33_11, case_51_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_33_12, case_51_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_33_13, case_51_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_33_14, case_51_33_14_checked⟩

    · exact ⟨Witness.linear .conditional case_51_33_15, case_51_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_33_16, case_51_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_51_33_17, case_51_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_51_33_18, case_51_33_18_checked⟩

    · exact ⟨Witness.linear .conditional case_51_33_19, case_51_33_19_checked⟩

    · exact ⟨Witness.linear .conditional case_51_33_20, case_51_33_20_checked⟩

    · exact ⟨Witness.linear .conditional case_51_33_21, case_51_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_34_1_checked⟩

    · exact ⟨Witness.rising, case_51_34_2_checked⟩

    · exact ⟨Witness.rising, case_51_34_3_checked⟩

    · exact ⟨Witness.rising, case_51_34_4_checked⟩

    · exact ⟨Witness.rising, case_51_34_5_checked⟩

    · exact ⟨Witness.rising, case_51_34_6_checked⟩

    · exact ⟨Witness.rising, case_51_34_7_checked⟩

    · exact ⟨Witness.rising, case_51_34_8_checked⟩

    · exact ⟨Witness.rising, case_51_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_34_10, case_51_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_34_11, case_51_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_34_12, case_51_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_34_13, case_51_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_34_14, case_51_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_34_15, case_51_34_15_checked⟩

    · exact ⟨Witness.linear .conditional case_51_34_16, case_51_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_51_34_17, case_51_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_51_34_18, case_51_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_51_34_19, case_51_34_19_checked⟩

    · exact ⟨Witness.linear .conditional case_51_34_20, case_51_34_20_checked⟩

    · exact ⟨Witness.linear .conditional case_51_34_21, case_51_34_21_checked⟩

    · exact ⟨Witness.linear .conditional case_51_34_22, case_51_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_35_1_checked⟩

    · exact ⟨Witness.rising, case_51_35_2_checked⟩

    · exact ⟨Witness.rising, case_51_35_3_checked⟩

    · exact ⟨Witness.rising, case_51_35_4_checked⟩

    · exact ⟨Witness.rising, case_51_35_5_checked⟩

    · exact ⟨Witness.rising, case_51_35_6_checked⟩

    · exact ⟨Witness.rising, case_51_35_7_checked⟩

    · exact ⟨Witness.rising, case_51_35_8_checked⟩

    · exact ⟨Witness.rising, case_51_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_35_10, case_51_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_35_11, case_51_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_35_12, case_51_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_35_13, case_51_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_35_14, case_51_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_35_15, case_51_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_35_16, case_51_35_16_checked⟩

    · exact ⟨Witness.linear .conditional case_51_35_17, case_51_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_51_35_18, case_51_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_51_35_19, case_51_35_19_checked⟩

    · exact ⟨Witness.linear .conditional case_51_35_20, case_51_35_20_checked⟩

    · exact ⟨Witness.linear .conditional case_51_35_21, case_51_35_21_checked⟩

    · exact ⟨Witness.linear .conditional case_51_35_22, case_51_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_36_1_checked⟩

    · exact ⟨Witness.rising, case_51_36_2_checked⟩

    · exact ⟨Witness.rising, case_51_36_3_checked⟩

    · exact ⟨Witness.rising, case_51_36_4_checked⟩

    · exact ⟨Witness.rising, case_51_36_5_checked⟩

    · exact ⟨Witness.rising, case_51_36_6_checked⟩

    · exact ⟨Witness.rising, case_51_36_7_checked⟩

    · exact ⟨Witness.rising, case_51_36_8_checked⟩

    · exact ⟨Witness.rising, case_51_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_36_10, case_51_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_36_11, case_51_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_36_12, case_51_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_36_13, case_51_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_36_14, case_51_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_36_15, case_51_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_36_16, case_51_36_16_checked⟩

    · exact ⟨Witness.linear .conditional case_51_36_17, case_51_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_51_36_18, case_51_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_51_36_19, case_51_36_19_checked⟩

    · exact ⟨Witness.linear .conditional case_51_36_20, case_51_36_20_checked⟩

    · exact ⟨Witness.linear .conditional case_51_36_21, case_51_36_21_checked⟩

    · exact ⟨Witness.linear .conditional case_51_36_22, case_51_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_51_36_23, case_51_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_37_1_checked⟩

    · exact ⟨Witness.rising, case_51_37_2_checked⟩

    · exact ⟨Witness.rising, case_51_37_3_checked⟩

    · exact ⟨Witness.rising, case_51_37_4_checked⟩

    · exact ⟨Witness.rising, case_51_37_5_checked⟩

    · exact ⟨Witness.rising, case_51_37_6_checked⟩

    · exact ⟨Witness.rising, case_51_37_7_checked⟩

    · exact ⟨Witness.rising, case_51_37_8_checked⟩

    · exact ⟨Witness.rising, case_51_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_37_10, case_51_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_37_11, case_51_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_37_12, case_51_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_37_13, case_51_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_37_14, case_51_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_37_15, case_51_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_37_16, case_51_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_37_17, case_51_37_17_checked⟩

    · exact ⟨Witness.linear .conditional case_51_37_18, case_51_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_51_37_19, case_51_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_51_37_20, case_51_37_20_checked⟩

    · exact ⟨Witness.linear .conditional case_51_37_21, case_51_37_21_checked⟩

    · exact ⟨Witness.linear .conditional case_51_37_22, case_51_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_51_37_23, case_51_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_51_37_24, case_51_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_38_1_checked⟩

    · exact ⟨Witness.rising, case_51_38_2_checked⟩

    · exact ⟨Witness.rising, case_51_38_3_checked⟩

    · exact ⟨Witness.rising, case_51_38_4_checked⟩

    · exact ⟨Witness.rising, case_51_38_5_checked⟩

    · exact ⟨Witness.rising, case_51_38_6_checked⟩

    · exact ⟨Witness.rising, case_51_38_7_checked⟩

    · exact ⟨Witness.rising, case_51_38_8_checked⟩

    · exact ⟨Witness.rising, case_51_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_38_10, case_51_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_38_11, case_51_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_38_12, case_51_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_38_13, case_51_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_38_14, case_51_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_38_15, case_51_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_38_16, case_51_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_38_17, case_51_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_38_18, case_51_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_51_38_19, case_51_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_51_38_20, case_51_38_20_checked⟩

    · exact ⟨Witness.linear .conditional case_51_38_21, case_51_38_21_checked⟩

    · exact ⟨Witness.linear .conditional case_51_38_22, case_51_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_51_38_23, case_51_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_51_38_24, case_51_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_39_1_checked⟩

    · exact ⟨Witness.rising, case_51_39_2_checked⟩

    · exact ⟨Witness.rising, case_51_39_3_checked⟩

    · exact ⟨Witness.rising, case_51_39_4_checked⟩

    · exact ⟨Witness.rising, case_51_39_5_checked⟩

    · exact ⟨Witness.rising, case_51_39_6_checked⟩

    · exact ⟨Witness.rising, case_51_39_7_checked⟩

    · exact ⟨Witness.rising, case_51_39_8_checked⟩

    · exact ⟨Witness.rising, case_51_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_39_10, case_51_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_39_11, case_51_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_39_12, case_51_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_39_13, case_51_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_39_14, case_51_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_39_15, case_51_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_39_16, case_51_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_39_17, case_51_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_39_18, case_51_39_18_checked⟩

    · exact ⟨Witness.linear .conditional case_51_39_19, case_51_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_51_39_20, case_51_39_20_checked⟩

    · exact ⟨Witness.linear .conditional case_51_39_21, case_51_39_21_checked⟩

    · exact ⟨Witness.linear .conditional case_51_39_22, case_51_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_51_39_23, case_51_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_51_39_24, case_51_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_51_39_25, case_51_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_40_1_checked⟩

    · exact ⟨Witness.rising, case_51_40_2_checked⟩

    · exact ⟨Witness.rising, case_51_40_3_checked⟩

    · exact ⟨Witness.rising, case_51_40_4_checked⟩

    · exact ⟨Witness.rising, case_51_40_5_checked⟩

    · exact ⟨Witness.rising, case_51_40_6_checked⟩

    · exact ⟨Witness.rising, case_51_40_7_checked⟩

    · exact ⟨Witness.rising, case_51_40_8_checked⟩

    · exact ⟨Witness.rising, case_51_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_40_10, case_51_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_40_11, case_51_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_40_12, case_51_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_40_13, case_51_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_40_14, case_51_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_40_15, case_51_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_40_16, case_51_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_40_17, case_51_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_40_18, case_51_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_51_40_19, case_51_40_19_checked⟩

    · exact ⟨Witness.linear .conditional case_51_40_20, case_51_40_20_checked⟩

    · exact ⟨Witness.linear .conditional case_51_40_21, case_51_40_21_checked⟩

    · exact ⟨Witness.linear .conditional case_51_40_22, case_51_40_22_checked⟩

    · exact ⟨Witness.linear .negative case_51_40_23, case_51_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_51_40_24, case_51_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_51_40_25, case_51_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_51_40_26, case_51_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_41_1_checked⟩

    · exact ⟨Witness.rising, case_51_41_2_checked⟩

    · exact ⟨Witness.rising, case_51_41_3_checked⟩

    · exact ⟨Witness.rising, case_51_41_4_checked⟩

    · exact ⟨Witness.rising, case_51_41_5_checked⟩

    · exact ⟨Witness.rising, case_51_41_6_checked⟩

    · exact ⟨Witness.rising, case_51_41_7_checked⟩

    · exact ⟨Witness.rising, case_51_41_8_checked⟩

    · exact ⟨Witness.rising, case_51_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_41_10, case_51_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_41_11, case_51_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_41_12, case_51_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_41_13, case_51_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_41_14, case_51_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_41_15, case_51_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_41_16, case_51_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_41_17, case_51_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_41_18, case_51_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_51_41_19, case_51_41_19_checked⟩

    · exact ⟨Witness.linear .positive case_51_41_20, case_51_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_51_41_21, case_51_41_21_checked⟩

    · exact ⟨Witness.linear .conditional case_51_41_22, case_51_41_22_checked⟩

    · exact ⟨Witness.linear .negative case_51_41_23, case_51_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_51_41_24, case_51_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_51_41_25, case_51_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_51_41_26, case_51_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_42_1_checked⟩

    · exact ⟨Witness.rising, case_51_42_2_checked⟩

    · exact ⟨Witness.rising, case_51_42_3_checked⟩

    · exact ⟨Witness.rising, case_51_42_4_checked⟩

    · exact ⟨Witness.rising, case_51_42_5_checked⟩

    · exact ⟨Witness.rising, case_51_42_6_checked⟩

    · exact ⟨Witness.rising, case_51_42_7_checked⟩

    · exact ⟨Witness.rising, case_51_42_8_checked⟩

    · exact ⟨Witness.rising, case_51_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_42_10, case_51_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_42_11, case_51_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_42_12, case_51_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_42_13, case_51_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_42_14, case_51_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_42_15, case_51_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_42_16, case_51_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_42_17, case_51_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_42_18, case_51_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_51_42_19, case_51_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_51_42_20, case_51_42_20_checked⟩

    · exact ⟨Witness.linear .conditional case_51_42_21, case_51_42_21_checked⟩

    · exact ⟨Witness.linear .conditional case_51_42_22, case_51_42_22_checked⟩

    · exact ⟨Witness.linear .negative case_51_42_23, case_51_42_23_checked⟩

    · exact ⟨Witness.linear .negative case_51_42_24, case_51_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_51_42_25, case_51_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_51_42_26, case_51_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_51_42_27, case_51_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_43_1_checked⟩

    · exact ⟨Witness.rising, case_51_43_2_checked⟩

    · exact ⟨Witness.rising, case_51_43_3_checked⟩

    · exact ⟨Witness.rising, case_51_43_4_checked⟩

    · exact ⟨Witness.rising, case_51_43_5_checked⟩

    · exact ⟨Witness.rising, case_51_43_6_checked⟩

    · exact ⟨Witness.rising, case_51_43_7_checked⟩

    · exact ⟨Witness.rising, case_51_43_8_checked⟩

    · exact ⟨Witness.rising, case_51_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_10, case_51_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_11, case_51_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_12, case_51_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_13, case_51_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_14, case_51_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_15, case_51_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_16, case_51_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_17, case_51_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_18, case_51_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_19, case_51_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_20, case_51_43_20_checked⟩

    · exact ⟨Witness.linear .positive case_51_43_21, case_51_43_21_checked⟩

    · exact ⟨Witness.linear .conditional case_51_43_22, case_51_43_22_checked⟩

    · exact ⟨Witness.linear .negative case_51_43_23, case_51_43_23_checked⟩

    · exact ⟨Witness.linear .negative case_51_43_24, case_51_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_51_43_25, case_51_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_51_43_26, case_51_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_51_43_27, case_51_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_51_43_28, case_51_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_44_1_checked⟩

    · exact ⟨Witness.rising, case_51_44_2_checked⟩

    · exact ⟨Witness.rising, case_51_44_3_checked⟩

    · exact ⟨Witness.rising, case_51_44_4_checked⟩

    · exact ⟨Witness.rising, case_51_44_5_checked⟩

    · exact ⟨Witness.rising, case_51_44_6_checked⟩

    · exact ⟨Witness.rising, case_51_44_7_checked⟩

    · exact ⟨Witness.rising, case_51_44_8_checked⟩

    · exact ⟨Witness.rising, case_51_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_10, case_51_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_11, case_51_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_12, case_51_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_13, case_51_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_14, case_51_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_15, case_51_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_16, case_51_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_17, case_51_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_18, case_51_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_19, case_51_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_20, case_51_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_51_44_21, case_51_44_21_checked⟩

    · exact ⟨Witness.linear .conditional case_51_44_22, case_51_44_22_checked⟩

    · exact ⟨Witness.linear .conditional case_51_44_23, case_51_44_23_checked⟩

    · exact ⟨Witness.linear .negative case_51_44_24, case_51_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_51_44_25, case_51_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_51_44_26, case_51_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_51_44_27, case_51_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_51_44_28, case_51_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_45_1_checked⟩

    · exact ⟨Witness.rising, case_51_45_2_checked⟩

    · exact ⟨Witness.rising, case_51_45_3_checked⟩

    · exact ⟨Witness.rising, case_51_45_4_checked⟩

    · exact ⟨Witness.rising, case_51_45_5_checked⟩

    · exact ⟨Witness.rising, case_51_45_6_checked⟩

    · exact ⟨Witness.rising, case_51_45_7_checked⟩

    · exact ⟨Witness.rising, case_51_45_8_checked⟩

    · exact ⟨Witness.rising, case_51_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_10, case_51_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_11, case_51_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_12, case_51_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_13, case_51_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_14, case_51_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_15, case_51_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_16, case_51_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_17, case_51_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_18, case_51_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_19, case_51_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_20, case_51_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_21, case_51_45_21_checked⟩

    · exact ⟨Witness.linear .positive case_51_45_22, case_51_45_22_checked⟩

    · exact ⟨Witness.linear .conditional case_51_45_23, case_51_45_23_checked⟩

    · exact ⟨Witness.linear .negative case_51_45_24, case_51_45_24_checked⟩

    · exact ⟨Witness.linear .negative case_51_45_25, case_51_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_51_45_26, case_51_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_51_45_27, case_51_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_51_45_28, case_51_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_51_45_29, case_51_45_29_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_46_1_checked⟩

    · exact ⟨Witness.rising, case_51_46_2_checked⟩

    · exact ⟨Witness.rising, case_51_46_3_checked⟩

    · exact ⟨Witness.rising, case_51_46_4_checked⟩

    · exact ⟨Witness.rising, case_51_46_5_checked⟩

    · exact ⟨Witness.rising, case_51_46_6_checked⟩

    · exact ⟨Witness.rising, case_51_46_7_checked⟩

    · exact ⟨Witness.rising, case_51_46_8_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_9, case_51_46_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_10, case_51_46_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_11, case_51_46_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_12, case_51_46_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_13, case_51_46_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_14, case_51_46_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_15, case_51_46_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_16, case_51_46_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_17, case_51_46_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_18, case_51_46_18_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_19, case_51_46_19_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_20, case_51_46_20_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_21, case_51_46_21_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_22, case_51_46_22_checked⟩

    · exact ⟨Witness.linear .positive case_51_46_23, case_51_46_23_checked⟩

    · exact ⟨Witness.linear .negative case_51_46_24, case_51_46_24_checked⟩

    · exact ⟨Witness.linear .negative case_51_46_25, case_51_46_25_checked⟩

    · exact ⟨Witness.linear .negative case_51_46_26, case_51_46_26_checked⟩

    · exact ⟨Witness.linear .negative case_51_46_27, case_51_46_27_checked⟩

    · exact ⟨Witness.linear .negative case_51_46_28, case_51_46_28_checked⟩

    · exact ⟨Witness.linear .negative case_51_46_29, case_51_46_29_checked⟩

    · exact ⟨Witness.linear .negative case_51_46_30, case_51_46_30_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_47_1_checked⟩

    · exact ⟨Witness.rising, case_51_47_2_checked⟩

    · exact ⟨Witness.rising, case_51_47_3_checked⟩

    · exact ⟨Witness.rising, case_51_47_4_checked⟩

    · exact ⟨Witness.rising, case_51_47_5_checked⟩

    · exact ⟨Witness.rising, case_51_47_6_checked⟩

    · exact ⟨Witness.rising, case_51_47_7_checked⟩

    · exact ⟨Witness.rising, case_51_47_8_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_9, case_51_47_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_10, case_51_47_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_11, case_51_47_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_12, case_51_47_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_13, case_51_47_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_14, case_51_47_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_15, case_51_47_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_16, case_51_47_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_17, case_51_47_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_18, case_51_47_18_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_19, case_51_47_19_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_20, case_51_47_20_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_21, case_51_47_21_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_22, case_51_47_22_checked⟩

    · exact ⟨Witness.linear .positive case_51_47_23, case_51_47_23_checked⟩

    · exact ⟨Witness.linear .negative case_51_47_24, case_51_47_24_checked⟩

    · exact ⟨Witness.linear .negative case_51_47_25, case_51_47_25_checked⟩

    · exact ⟨Witness.linear .negative case_51_47_26, case_51_47_26_checked⟩

    · exact ⟨Witness.linear .negative case_51_47_27, case_51_47_27_checked⟩

    · exact ⟨Witness.linear .negative case_51_47_28, case_51_47_28_checked⟩

    · exact ⟨Witness.linear .negative case_51_47_29, case_51_47_29_checked⟩

    · exact ⟨Witness.linear .negative case_51_47_30, case_51_47_30_checked⟩

  · have hkHi : k ≤ 31 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_48_1_checked⟩

    · exact ⟨Witness.rising, case_51_48_2_checked⟩

    · exact ⟨Witness.rising, case_51_48_3_checked⟩

    · exact ⟨Witness.rising, case_51_48_4_checked⟩

    · exact ⟨Witness.rising, case_51_48_5_checked⟩

    · exact ⟨Witness.rising, case_51_48_6_checked⟩

    · exact ⟨Witness.rising, case_51_48_7_checked⟩

    · exact ⟨Witness.rising, case_51_48_8_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_9, case_51_48_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_10, case_51_48_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_11, case_51_48_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_12, case_51_48_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_13, case_51_48_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_14, case_51_48_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_15, case_51_48_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_16, case_51_48_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_17, case_51_48_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_18, case_51_48_18_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_19, case_51_48_19_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_20, case_51_48_20_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_21, case_51_48_21_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_22, case_51_48_22_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_23, case_51_48_23_checked⟩

    · exact ⟨Witness.linear .positive case_51_48_24, case_51_48_24_checked⟩

    · exact ⟨Witness.linear .negative case_51_48_25, case_51_48_25_checked⟩

    · exact ⟨Witness.linear .negative case_51_48_26, case_51_48_26_checked⟩

    · exact ⟨Witness.linear .negative case_51_48_27, case_51_48_27_checked⟩

    · exact ⟨Witness.linear .negative case_51_48_28, case_51_48_28_checked⟩

    · exact ⟨Witness.linear .negative case_51_48_29, case_51_48_29_checked⟩

    · exact ⟨Witness.linear .negative case_51_48_30, case_51_48_30_checked⟩

    · exact ⟨Witness.linear .negative case_51_48_31, case_51_48_31_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_49_1_checked⟩

    · exact ⟨Witness.rising, case_51_49_2_checked⟩

    · exact ⟨Witness.rising, case_51_49_3_checked⟩

    · exact ⟨Witness.rising, case_51_49_4_checked⟩

    · exact ⟨Witness.rising, case_51_49_5_checked⟩

    · exact ⟨Witness.rising, case_51_49_6_checked⟩

    · exact ⟨Witness.rising, case_51_49_7_checked⟩

    · exact ⟨Witness.rising, case_51_49_8_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_9, case_51_49_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_10, case_51_49_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_11, case_51_49_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_12, case_51_49_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_13, case_51_49_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_14, case_51_49_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_15, case_51_49_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_16, case_51_49_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_17, case_51_49_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_18, case_51_49_18_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_19, case_51_49_19_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_20, case_51_49_20_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_21, case_51_49_21_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_22, case_51_49_22_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_23, case_51_49_23_checked⟩

    · exact ⟨Witness.linear .positive case_51_49_24, case_51_49_24_checked⟩

    · exact ⟨Witness.linear .negative case_51_49_25, case_51_49_25_checked⟩

    · exact ⟨Witness.linear .negative case_51_49_26, case_51_49_26_checked⟩

    · exact ⟨Witness.linear .negative case_51_49_27, case_51_49_27_checked⟩

    · exact ⟨Witness.linear .negative case_51_49_28, case_51_49_28_checked⟩

    · exact ⟨Witness.linear .negative case_51_49_29, case_51_49_29_checked⟩

    · exact ⟨Witness.linear .negative case_51_49_30, case_51_49_30_checked⟩

    · exact ⟨Witness.linear .negative case_51_49_31, case_51_49_31_checked⟩

    · exact ⟨Witness.linear .negative case_51_49_32, case_51_49_32_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_51_50_1_checked⟩

    · exact ⟨Witness.rising, case_51_50_2_checked⟩

    · exact ⟨Witness.rising, case_51_50_3_checked⟩

    · exact ⟨Witness.rising, case_51_50_4_checked⟩

    · exact ⟨Witness.rising, case_51_50_5_checked⟩

    · exact ⟨Witness.rising, case_51_50_6_checked⟩

    · exact ⟨Witness.rising, case_51_50_7_checked⟩

    · exact ⟨Witness.rising, case_51_50_8_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_9, case_51_50_9_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_10, case_51_50_10_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_11, case_51_50_11_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_12, case_51_50_12_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_13, case_51_50_13_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_14, case_51_50_14_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_15, case_51_50_15_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_16, case_51_50_16_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_17, case_51_50_17_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_18, case_51_50_18_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_19, case_51_50_19_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_20, case_51_50_20_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_21, case_51_50_21_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_22, case_51_50_22_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_23, case_51_50_23_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_24, case_51_50_24_checked⟩

    · exact ⟨Witness.linear .positive case_51_50_25, case_51_50_25_checked⟩

    · exact ⟨Witness.linear .negative case_51_50_26, case_51_50_26_checked⟩

    · exact ⟨Witness.linear .negative case_51_50_27, case_51_50_27_checked⟩

    · exact ⟨Witness.linear .negative case_51_50_28, case_51_50_28_checked⟩

    · exact ⟨Witness.linear .negative case_51_50_29, case_51_50_29_checked⟩

    · exact ⟨Witness.linear .negative case_51_50_30, case_51_50_30_checked⟩

    · exact ⟨Witness.linear .negative case_51_50_31, case_51_50_31_checked⟩

    · exact ⟨Witness.linear .negative case_51_50_32, case_51_50_32_checked⟩


#print axioms coverage_51
end ForestUnimodality.FiniteRows.FiniteData
