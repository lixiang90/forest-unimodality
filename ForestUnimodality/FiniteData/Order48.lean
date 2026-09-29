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

theorem case_48_24_1_checked :
    (Witness.rising).check 48 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_24_2_checked :
    (Witness.rising).check 48 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_24_3_checked :
    (Witness.rising).check 48 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_24_4_checked :
    (Witness.rising).check 48 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_24_5_checked :
    (Witness.rising).check 48 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_24_6_checked :
    (Witness.rising).check 48 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_24_7_checked :
    (Witness.rising).check 48 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_24_8_checked :
    (Witness.rising).check 48 24 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_24_9_checked :
    (Witness.rising).check 48 24 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_24_10 : Certificate := {
  objectiveScale := 100800456900000
  eta := 0
  rows := #[⟨.count 2, 709984711920163680⟩, ⟨.count 3, 342958716774994320⟩, ⟨.count 4, 48447118797105600⟩, ⟨.count 5, 8048472961454640⟩, ⟨.count 6, 1554584966494560⟩, ⟨.count 7, 383848139875200⟩, ⟨.count 8, 130959953604480⟩, ⟨.count 9, 101606860555200⟩, ⟨.count 11, 14636226341880⟩, ⟨.path 10, 30357655552224⟩, ⟨.path 11, 15062725786680⟩, ⟨.hall 9 1, 749955399336⟩, ⟨.hall 0 2, 1093967198644320⟩, ⟨.hall 1 3, 58605385641660⟩, ⟨.hall 8 3, 126543342816⟩, ⟨.hall 9 3, 9769890438⟩, ⟨.hall 0 4, 937686170266560⟩, ⟨.hall 8 4, 17575464280⟩, ⟨.hall 1 5, 22162660457080⟩, ⟨.hall 7 5, 66037222405⟩, ⟨.hall 0 6, 169989890516160⟩, ⟨.hall 7 6, 7260452490⟩, ⟨.hall 6 8, 40714925808⟩, ⟨.hall 6 9, 1353404736⟩, ⟨.hall 1 13, 84672383796⟩, ⟨.hall 5 14, 686787113012⟩, ⟨.hall 4 18, 127492417887120⟩]
  caps := #[0, 0, 15931820440055520, 902406058725600, 109806521235840, 45103006449072, 3164318873280, 6497592747360, 198158847744, 862451870280, 0, 426499444800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_24_10_checked :
    (Witness.linear .positive case_48_24_10).check 48 24 10 = true := by
  change case_48_24_10.check 48 24 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_24_11 : Certificate := {
  objectiveScale := 12341529200000
  eta := 0
  rows := #[⟨.count 3, 89505503969001120⟩, ⟨.count 4, 15240475423293120⟩, ⟨.count 5, 2647709713368720⟩, ⟨.count 6, 537019428385440⟩, ⟨.count 7, 126890666622720⟩, ⟨.count 8, 36076758157440⟩, ⟨.count 9, 14695058818440⟩, ⟨.count 10, 12129254897760⟩, ⟨.path 11, 2034352405800⟩, ⟨.path 12, 2587774555080⟩, ⟨.privateRow 10 2, 333733936536⟩, ⟨.privateRow 12 0, 199538428320⟩, ⟨.hall 10 1, 325531566360⟩, ⟨.hall 1 2, 14350730153760⟩, ⟨.hall 10 2, 11961789840⟩, ⟨.hall 2 3, 679771428336⟩, ⟨.hall 9 3, 33962939010⟩, ⟨.hall 0 4, 202345295168016⟩, ⟨.hall 8 4, 32296832568⟩, ⟨.hall 1 5, 9818920631520⟩, ⟨.hall 8 5, 4401524400⟩, ⟨.hall 0 6, 63445333311360⟩, ⟨.hall 7 6, 11515164570⟩, ⟨.hall 7 7, 6157603179⟩, ⟨.hall 6 9, 1335992112⟩, ⟨.hall 6 10, 16796993850⟩, ⟨.hall 1 11, 21146735610⟩, ⟨.hall 1 12, 2563240680⟩, ⟨.hall 5 15, 698376283605⟩, ⟨.hall 2 16, 81454092720⟩, ⟨.hall 2 17, 75530158704⟩, ⟨.hall 4 19, 490794971258592⟩]
  caps := #[0, 8528496559623040, 2206213760550800, 0, 0, 0, 991990359360, 0, 0, 400914914400, 212274302240, 241657135720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_24_11_checked :
    (Witness.linear .positive case_48_24_11).check 48 24 11 = true := by
  change case_48_24_11.check 48 24 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_24_12 : Certificate := {
  objectiveScale := 1544400000
  eta := 0
  rows := #[⟨.count 3, 17657781261120⟩, ⟨.count 4, 3930469583040⟩, ⟨.count 5, 747962495280⟩, ⟨.count 6, 160553352960⟩, ⟨.count 7, 39023384400⟩, ⟨.count 8, 10453322880⟩, ⟨.count 9, 3655131480⟩, ⟨.count 10, 1589187600⟩, ⟨.count 11, 1581620040⟩, ⟨.path 13, 459729270⟩, ⟨.privateRow 9 6, 35315280⟩, ⟨.privateRow 10 4, 73198944⟩, ⟨.privateRow 11 2, 51711660⟩, ⟨.privateRow 12 12, 19209960⟩, ⟨.privateRow 13 0, 38419920⟩, ⟨.hall 11 1, 56562660⟩, ⟨.hall 11 2, 1649340⟩, ⟨.hall 10 3, 6350400⟩, ⟨.hall 9 4, 4836888⟩, ⟨.hall 1 5, 385945560⟩, ⟨.hall 9 5, 1259496⟩, ⟨.hall 0 6, 13122149040⟩, ⟨.hall 8 6, 4508784⟩, ⟨.hall 1 7, 317837520⟩, ⟨.hall 2 8, 5213208⟩, ⟨.hall 7 8, 1915312⟩, ⟨.hall 0 9, 561512952⟩, ⟨.hall 7 9, 2417121⟩, ⟨.hall 6 13, 35063028⟩, ⟨.hall 6 14, 15765750⟩, ⟨.hall 2 15, 10090080⟩, ⟨.hall 5 16, 792071280⟩, ⟨.hall 4 19, 76262842656⟩]
  caps := #[0, 62296153920, 489562753680, 0, 0, 3965787540, 0, 0, 81651150, 0, 0, 0, 34309440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_24_12_checked :
    (Witness.linear .positive case_48_24_12).check 48 24 12 = true := by
  change case_48_24_12.check 48 24 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_24_13 : Certificate := {
  objectiveScale := 231000000
  eta := 0
  rows := #[⟨.count 3, 4082017539600⟩, ⟨.count 4, 1052222371200⟩, ⟨.count 5, 228136708800⟩, ⟨.count 6, 56972916000⟩, ⟨.count 7, 14294280000⟩, ⟨.count 8, 4237833600⟩, ⟨.count 9, 1362160800⟩, ⟨.count 10, 479278800⟩, ⟨.count 11, 237837600⟩, ⟨.count 12, 237837600⟩, ⟨.path 14, 26445300⟩, ⟨.path 15, 32004840⟩, ⟨.privateRow 10 6, 33073040⟩, ⟨.privateRow 11 4, 22162140⟩, ⟨.privateRow 11 5, 9409400⟩, ⟨.privateRow 14 0, 2457000⟩, ⟨.privateRow 15 0, 3279276⟩, ⟨.privateRow 16 4, 9249240⟩, ⟨.hall 12 1, 2633400⟩, ⟨.hall 13 1, 2342340⟩, ⟨.hall 12 2, 2772000⟩, ⟨.hall 11 3, 2945250⟩, ⟨.hall 2 5, 6006000⟩, ⟨.hall 10 5, 1484000⟩, ⟨.hall 9 6, 1187760⟩, ⟨.hall 11 6, 37950⟩, ⟨.hall 0 7, 1261260000⟩, ⟨.hall 1 7, 78303225⟩, ⟨.hall 9 7, 573300⟩, ⟨.hall 8 8, 1595440⟩, ⟨.hall 0 9, 75675600⟩, ⟨.hall 8 9, 513240⟩, ⟨.hall 2 10, 277200⟩, ⟨.hall 7 11, 3744125⟩, ⟨.hall 7 12, 4093320⟩, ⟨.hall 6 14, 53153100⟩, ⟨.hall 2 17, 23143120⟩, ⟨.hall 5 17, 2256454200⟩, ⟨.hall 4 19, 24676011360⟩, ⟨.hall 1 22, 268875406800⟩]
  caps := #[0, 0, 81999687000, 0, 3068629200, 362281920, 132732600, 285885600, 23123100, 0, 9166500, 10610600, 0, 16562700, 56700, 2239104, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_24_13_checked :
    (Witness.linear .positive case_48_24_13).check 48 24 13 = true := by
  change case_48_24_13.check 48 24 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_24_14 : Certificate := {
  objectiveScale := 5400000
  eta := 0
  rows := #[⟨.count 2, 128035908000⟩, ⟨.count 3, 85900454640⟩, ⟨.count 4, 20751793920⟩, ⟨.count 5, 5753301840⟩, ⟨.count 6, 1648801440⟩, ⟨.count 7, 498257760⟩, ⟨.count 8, 161441280⟩, ⟨.count 9, 57297240⟩, ⟨.count 10, 23783760⟩, ⟨.count 11, 11325600⟩, ⟨.count 12, 7840800⟩, ⟨.count 13, 7927920⟩, ⟨.path 14, 1080030⟩, ⟨.privateRow 4 20, 1064194560⟩, ⟨.privateRow 9 9, 377520⟩, ⟨.privateRow 10 7, 1288287⟩, ⟨.privateRow 12 3, 509652⟩, ⟨.privateRow 12 4, 237160⟩, ⟨.privateRow 15 0, 540540⟩, ⟨.hall 13 1, 597168⟩, ⟨.hall 12 2, 239184⟩, ⟨.hall 13 2, 19448⟩, ⟨.hall 12 3, 31416⟩, ⟨.hall 11 4, 103576⟩, ⟨.hall 0 5, 12252240⟩, ⟨.hall 10 5, 102720⟩, ⟨.hall 0 6, 7001280⟩, ⟨.hall 1 6, 1475760⟩, ⟨.hall 10 6, 15690⟩, ⟨.hall 0 7, 10570560⟩, ⟨.hall 9 7, 105588⟩, ⟨.hall 8 9, 150384⟩, ⟨.hall 7 12, 733392⟩, ⟨.hall 6 14, 2987556⟩, ⟨.hall 5 16, 16588000⟩, ⟨.hall 4 19, 2208203712⟩, ⟨.hall 1 22, 2560718160⟩, ⟨.assumptionRow 14, 7809648⟩]
  caps := #[0, 0, 0, 0, 35067396, 27159132, 5513508, 1516944, 0, 83226, 477477, 0, 0, 367290, 74022, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_24_14_checked :
    (Witness.linear .conditional case_48_24_14).check 48 24 14 = true := by
  change case_48_24_14.check 48 24 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_24_15 : Certificate := {
  objectiveScale := 7200000
  eta := 0
  rows := #[⟨.count 2, 189493143840⟩, ⟨.count 3, 55171836720⟩, ⟨.count 4, 16361991360⟩, ⟨.count 5, 5021668080⟩, ⟨.count 6, 1596291840⟩, ⟨.count 7, 526846320⟩, ⟨.count 8, 180660480⟩, ⟨.count 9, 73513440⟩, ⟨.count 10, 31711680⟩, ⟨.count 11, 14723280⟩, ⟨.count 12, 7318080⟩, ⟨.count 13, 6229080⟩, ⟨.count 14, 5045040⟩, ⟨.path 13, 958980⟩, ⟨.privateRow 13 3, 474320⟩, ⟨.privateRow 16 0, 800800⟩, ⟨.hall 14 1, 824824⟩, ⟨.hall 13 2, 351208⟩, ⟨.hall 12 3, 102960⟩, ⟨.hall 13 3, 33033⟩, ⟨.hall 14 3, 5148⟩, ⟨.hall 11 4, 29656⟩, ⟨.hall 12 4, 116556⟩, ⟨.hall 0 5, 15752880⟩, ⟨.hall 11 5, 179520⟩, ⟨.hall 10 6, 122310⟩, ⟨.hall 10 7, 86280⟩, ⟨.hall 9 8, 200328⟩, ⟨.hall 9 9, 59940⟩, ⟨.hall 8 10, 256720⟩, ⟨.hall 8 11, 388872⟩, ⟨.hall 0 12, 87120⟩, ⟨.hall 7 12, 1160280⟩, ⟨.hall 6 14, 4495920⟩, ⟨.hall 5 16, 25179440⟩, ⟨.hall 4 18, 207587952⟩, ⟨.hall 3 20, 2660486400⟩, ⟨.assumptionRow 15, 5314680⟩]
  caps := #[0, 32488205640, 1502105040, 206745840, 0, 4534920, 514800, 1124640, 875640, 0, 278520, 308880, 63360, 44580, 924840, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_24_15_checked :
    (Witness.linear .conditional case_48_24_15).check 48 24 15 = true := by
  change case_48_24_15.check 48 24 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_25_1_checked :
    (Witness.rising).check 48 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_25_2_checked :
    (Witness.rising).check 48 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_25_3_checked :
    (Witness.rising).check 48 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_25_4_checked :
    (Witness.rising).check 48 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_25_5_checked :
    (Witness.rising).check 48 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_25_6_checked :
    (Witness.rising).check 48 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_25_7_checked :
    (Witness.rising).check 48 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_25_8_checked :
    (Witness.rising).check 48 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_25_9_checked :
    (Witness.rising).check 48 25 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_25_10 : Certificate := {
  objectiveScale := 583167312000000
  eta := 77298823998179784000
  rows := #[⟨.count 2, 17526578275523116800⟩, ⟨.count 3, 2645521249135564800⟩, ⟨.count 4, 351948809036784960⟩, ⟨.count 5, 55322225369611200⟩, ⟨.count 6, 10359967297680000⟩, ⟨.count 7, 2388886576876800⟩, ⟨.count 8, 767856399710400⟩, ⟨.count 9, 588689906444640⟩, ⟨.count 11, 77348172132000⟩, ⟨.path 10, 198719055334800⟩, ⟨.path 11, 77170530396960⟩, ⟨.privateRow 4 21, 1181036271935520⟩, ⟨.privateRow 6 12, 47483183447700⟩, ⟨.privateRow 7 9, 92630295838080⟩, ⟨.privateRow 7 10, 131361676846400⟩, ⟨.privateRow 7 11, 82270328540400⟩, ⟨.privateRow 8 5, 9844312816800⟩, ⟨.privateRow 8 6, 35548907394000⟩, ⟨.privateRow 8 7, 30539743170300⟩, ⟨.privateRow 8 8, 122643730509300⟩, ⟨.privateRow 9 2, 7204578565184⟩, ⟨.privateRow 9 3, 19297978299600⟩, ⟨.privateRow 9 4, 9844312816800⟩, ⟨.privateRow 10 0, 5141895533775⟩, ⟨.hall 6 9, 84334965120⟩, ⟨.hall 5 12, 280032457320⟩, ⟨.hall 7 17, 170634755491200⟩, ⟨.hall 4 18, 94127702876064⟩]
  caps := #[0, 287354507216736960, 3593649011752800, 1439146885176000, 1000395932870880, 389157992308800, 184418616984420, 0, 19691617915200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_25_10_checked :
    (Witness.linear .positive case_48_25_10).check 48 25 10 = true := by
  change case_48_25_10.check 48 25 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_25_11 : Certificate := {
  objectiveScale := 7963956000000
  eta := 1707059843727638400
  rows := #[⟨.count 2, 436002297748617600⟩, ⟨.count 3, 75658187260656000⟩, ⟨.count 4, 11612651998147200⟩, ⟨.count 5, 2037307368096000⟩, ⟨.count 6, 388940497545600⟩, ⟨.count 7, 88973316432000⟩, ⟨.count 8, 24149900174400⟩, ⟨.count 9, 9914169545280⟩, ⟨.count 10, 8171018856000⟩, ⟨.path 11, 1603144342800⟩, ⟨.path 12, 1511103765600⟩, ⟨.privateRow 7 11, 5084189510400⟩, ⟨.privateRow 7 12, 1400746089600⟩, ⟨.privateRow 8 7, 158880922200⟩, ⟨.privateRow 8 8, 1557033037560⟩, ⟨.privateRow 8 9, 2489134447800⟩, ⟨.privateRow 8 10, 3237198789825⟩, ⟨.privateRow 9 4, 19554575040⟩, ⟨.privateRow 9 5, 600216817200⟩, ⟨.privateRow 9 6, 924398092800⟩, ⟨.privateRow 9 7, 1254100079232⟩, ⟨.privateRow 9 8, 743798095040⟩, ⟨.privateRow 10 2, 237348642960⟩, ⟨.privateRow 10 3, 414836341920⟩, ⟨.privateRow 10 4, 208814926320⟩, ⟨.privateRow 11 0, 212306814720⟩, ⟨.privateRow 12 0, 107001437400⟩, ⟨.hall 12 1, 106368292800⟩, ⟨.hall 13 1, 140723102520⟩, ⟨.hall 7 10, 2512582800⟩, ⟨.hall 6 11, 8015007000⟩, ⟨.hall 7 11, 1232431200⟩, ⟨.hall 5 15, 138333915720⟩, ⟨.hall 8 16, 6130934409600⟩, ⟨.hall 4 18, 2910439097280⟩]
  caps := #[0, 2597052422764800, 0, 203216265252000, 15434146728000, 0, 2469463476480, 0, 1369578104895, 0, 0, 0, 13083642000, 293318625600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_25_11_checked :
    (Witness.linear .positive case_48_25_11).check 48 25 11 = true := by
  change case_48_25_11.check 48 25 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_25_12 : Certificate := {
  objectiveScale := 3981978000000
  eta := 1002558955840041600
  rows := #[⟨.count 2, 268498590138979200⟩, ⟨.count 3, 49265796355776000⟩, ⟨.count 4, 9008602762199040⟩, ⟨.count 5, 1796534679139200⟩, ⟨.count 6, 401287814928000⟩, ⟨.count 7, 99141695452800⟩, ⟨.count 8, 26691994929600⟩, ⟨.count 9, 9151541118720⟩, ⟨.count 10, 3813142132800⟩, ⟨.count 11, 4148363419200⟩, ⟨.path 12, 23664326400⟩, ⟨.path 13, 1140683544000⟩, ⟨.privateRow 4 21, 351898545398400⟩, ⟨.privateRow 7 12, 985710211200⟩, ⟨.privateRow 8 9, 1253393941800⟩, ⟨.privateRow 8 10, 2760556023225⟩, ⟨.privateRow 9 6, 154066348800⟩, ⟨.privateRow 9 7, 1008364252896⟩, ⟨.privateRow 9 8, 1628823676480⟩, ⟨.privateRow 9 9, 2129004357480⟩, ⟨.privateRow 10 4, 267827840280⟩, ⟨.privateRow 10 5, 559590988320⟩, ⟨.privateRow 10 6, 866127998736⟩, ⟨.privateRow 10 7, 605260656000⟩, ⟨.privateRow 11 2, 277202217600⟩, ⟨.privateRow 11 3, 300302402400⟩, ⟨.privateRow 12 0, 148155836400⟩, ⟨.privateRow 13 0, 87028603200⟩, ⟨.hall 7 9, 6396193440⟩, ⟨.hall 8 9, 2241717660⟩, ⟨.hall 7 10, 1154626200⟩, ⟨.hall 8 10, 1885993200⟩, ⟨.hall 6 12, 23419281600⟩, ⟨.hall 9 15, 3908470686120⟩, ⟨.hall 5 16, 750204655200⟩, ⟨.hall 4 19, 39211552201536⟩]
  caps := #[0, 11184611662224000, 0, 0, 0, 6173658691200, 0, 0, 1189035222375, 919327854172, 198679698360, 0, 55196341200, 9311702400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_25_12_checked :
    (Witness.linear .positive case_48_25_12).check 48 25 12 = true := by
  change case_48_25_12.check 48 25 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_25_13 : Certificate := {
  objectiveScale := 635778000000
  eta := 243865691961091200
  rows := #[⟨.count 2, 74514516988111200⟩, ⟨.count 3, 16275307724676000⟩, ⟨.count 4, 3307846326744960⟩, ⟨.count 5, 745469286962400⟩, ⟨.count 6, 174405858026400⟩, ⟨.count 7, 43851134527200⟩, ⟨.count 8, 12392711931600⟩, ⟨.count 9, 3813142132800⟩, ⟨.count 10, 1361836476000⟩, ⟨.count 11, 691393903200⟩, ⟨.count 12, 691393903200⟩, ⟨.path 14, 103943589750⟩, ⟨.path 15, 57905593200⟩, ⟨.privateRow 4 21, 21993659087400⟩, ⟨.privateRow 8 11, 1044074631600⟩, ⟨.privateRow 8 12, 973145648475⟩, ⟨.privateRow 9 8, 96505449040⟩, ⟨.privateRow 9 9, 471346735860⟩, ⟨.privateRow 9 10, 456971795280⟩, ⟨.privateRow 10 6, 98052226272⟩, ⟨.privateRow 10 7, 245130565680⟩, ⟨.privateRow 10 8, 495368018145⟩, ⟨.privateRow 10 9, 23345768160⟩, ⟨.privateRow 11 4, 68567990400⟩, ⟨.privateRow 11 5, 141421480200⟩, ⟨.privateRow 11 6, 240940299600⟩, ⟨.privateRow 11 7, 172848475800⟩, ⟨.privateRow 12 2, 50414138775⟩, ⟨.privateRow 12 3, 82932349500⟩, ⟨.privateRow 12 4, 43212118950⟩, ⟨.privateRow 13 0, 34650277200⟩, ⟨.privateRow 14 0, 9078909840⟩, ⟨.privateRow 15 0, 5777488080⟩, ⟨.hall 15 1, 11916069165⟩, ⟨.hall 16 1, 20175355200⟩, ⟨.hall 9 8, 1825834374⟩, ⟨.hall 8 9, 3324996675⟩, ⟨.hall 7 12, 13168755600⟩, ⟨.hall 6 14, 52296644400⟩, ⟨.hall 10 14, 1171179369360⟩, ⟨.hall 9 15, 95328553320⟩, ⟨.hall 5 17, 1250978208480⟩, ⟨.hall 4 20, 177624980058240⟩]
  caps := #[0, 0, 23691007840500, 59512254001200, 0, 0, 2431526603220, 4672968300, 371037391725, 74147150077, 20642295609, 0, 0, 82689888600, 0, 138790426320, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_25_13_checked :
    (Witness.linear .positive case_48_25_13).check 48 25 13 = true := by
  change case_48_25_13.check 48 25 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_25_14 : Certificate := {
  objectiveScale := 11521125000
  eta := 4689724845405600
  rows := #[⟨.count 2, 1342177144308000⟩, ⟨.count 3, 304527587364000⟩, ⟨.count 4, 77146988798880⟩, ⟨.count 5, 19589493924000⟩, ⟨.count 6, 5223865046400⟩, ⟨.count 7, 1564366003200⟩, ⟨.count 8, 488864376000⟩, ⟨.count 9, 166213887840⟩, ⟨.count 10, 62853991200⟩, ⟨.count 11, 29546748000⟩, ⟨.count 12, 20682723600⟩, ⟨.count 13, 20951330400⟩, ⟨.path 14, 2760461550⟩, ⟨.privateRow 8 11, 1745944200⟩, ⟨.privateRow 9 9, 8690922240⟩, ⟨.privateRow 9 10, 29487057600⟩, ⟨.privateRow 10 7, 4578253680⟩, ⟨.privateRow 10 8, 16979307345⟩, ⟨.privateRow 10 9, 17559210240⟩, ⟨.privateRow 11 5, 2310018480⟩, ⟨.privateRow 11 6, 8446191600⟩, ⟨.privateRow 11 7, 16250711400⟩, ⟨.privateRow 11 8, 15272215200⟩, ⟨.privateRow 12 3, 1231114500⟩, ⟨.privateRow 12 4, 4456634490⟩, ⟨.privateRow 12 5, 8316862400⟩, ⟨.privateRow 12 6, 1292670225⟩, ⟨.privateRow 13 2, 4322127600⟩, ⟨.privateRow 13 3, 107442720⟩, ⟨.privateRow 14 0, 1309458150⟩, ⟨.privateRow 15 0, 1036985040⟩, ⟨.hall 9 8, 99852543⟩, ⟨.hall 8 9, 65523780⟩, ⟨.hall 9 9, 57078945⟩, ⟨.hall 8 10, 205105950⟩, ⟨.hall 10 11, 462387420⟩, ⟨.hall 7 12, 817085500⟩, ⟨.hall 10 12, 15348960⟩, ⟨.hall 11 13, 27014169600⟩, ⟨.hall 6 14, 2758115360⟩, ⟨.hall 5 17, 69255786600⟩, ⟨.hall 4 19, 639131973480⟩, ⟨.hall 3 21, 7690090590000⟩, ⟨.assumptionRow 14, 19298959680⟩]
  caps := #[0, 52688381813760, 0, 182819757120, 0, 144719374800, 18019171170, 428828400, 1529083710, 1427851425, 1387845690, 3150649920, 0, 284423160, 0, 114289560, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_25_14_checked :
    (Witness.linear .conditional case_48_25_14).check 48 25 14 = true := by
  change case_48_25_14.check 48 25 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_25_15 : Certificate := {
  objectiveScale := 370351800000
  eta := 45160313326128000
  rows := #[⟨.count 2, 12726997391908800⟩, ⟨.count 3, 3636284969116800⟩, ⟨.count 4, 1079155539221760⟩, ⟨.count 5, 327203910633600⟩, ⟨.count 6, 102894311520000⟩, ⟨.count 7, 34741961654400⟩, ⟨.count 8, 12498632546400⟩, ⟨.count 9, 4829980034880⟩, ⟨.count 10, 1997360164800⟩, ⟨.count 11, 845036992800⟩, ⟨.count 12, 384107724000⟩, ⟨.count 13, 363156393600⟩, ⟨.count 14, 381314213280⟩, ⟨.count 16, 423682459200⟩, ⟨.path 12, 5309304000⟩, ⟨.path 13, 35837802000⟩, ⟨.privateRow 3 22, 469198060531200⟩, ⟨.privateRow 9 10, 689997147840⟩, ⟨.privateRow 10 8, 234916792110⟩, ⟨.privateRow 10 9, 904000022640⟩, ⟨.privateRow 11 6, 83805321600⟩, ⟨.privateRow 11 7, 395456361300⟩, ⟨.privateRow 11 8, 836057851200⟩, ⟨.privateRow 12 4, 24326822520⟩, ⟨.privateRow 12 5, 177116339400⟩, ⟨.privateRow 12 6, 407314232325⟩, ⟨.privateRow 12 7, 656641299600⟩, ⟨.privateRow 13 3, 86598832320⟩, ⟨.privateRow 13 4, 207961353600⟩, ⟨.privateRow 13 5, 192053862000⟩, ⟨.privateRow 14 1, 37140994800⟩, ⟨.privateRow 14 2, 73539169704⟩, ⟨.privateRow 15 0, 19258293600⟩, ⟨.hall 10 7, 650761020⟩, ⟨.hall 9 8, 2973924954⟩, ⟨.hall 10 8, 5982063360⟩, ⟨.hall 9 9, 7496449506⟩, ⟨.hall 8 10, 9960596100⟩, ⟨.hall 8 11, 9728218500⟩, ⟨.hall 11 11, 11959398000⟩, ⟨.hall 11 12, 148155836400⟩, ⟨.hall 12 12, 35456097600⟩, ⟨.hall 7 13, 94932958120⟩, ⟨.hall 6 15, 446711565300⟩, ⟨.hall 5 17, 3074193202080⟩, ⟨.hall 4 18, 3445489517184⟩, ⟨.hall 3 21, 629151944803200⟩, ⟨.assumptionRow 15, 334506647475⟩]
  caps := #[0, 1808843003767800, 178141499636100, 0, 0, 623776321350, 273123871020, 78865461675, 221751930400, 0, 0, 24395177625, 171607016295, 8246203875, 0, 90657218925, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_25_15_checked :
    (Witness.linear .conditional case_48_25_15).check 48 25 15 = true := by
  change case_48_25_15.check 48 25 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_25_16 : Certificate := {
  objectiveScale := 7045038000000
  eta := 830949765200755200
  rows := #[⟨.count 2, 231343968720664800⟩, ⟨.count 3, 66772748989346400⟩, ⟨.count 4, 19694588590797120⟩, ⟨.count 5, 5892757220750400⟩, ⟨.count 6, 1881422486143200⟩, ⟨.count 7, 623660579942400⟩, ⟨.count 8, 211947150214800⟩, ⟨.count 9, 71623519727760⟩, ⟨.count 10, 24013716526800⟩, ⟨.count 11, 9717925417200⟩, ⟨.count 12, 3533791060800⟩, ⟨.count 13, 3132223894800⟩, ⟨.count 14, 2923408968480⟩, ⟨.count 15, 2436174140400⟩, ⟨.count 17, 11832845824800⟩, ⟨.path 11, 123640416900⟩, ⟨.path 12, 1083761679000⟩, ⟨.privateRow 9 10, 8770226905440⟩, ⟨.privateRow 10 8, 1983741800040⟩, ⟨.privateRow 10 9, 14020430767200⟩, ⟨.privateRow 11 6, 214169155200⟩, ⟨.privateRow 11 7, 4778649275400⟩, ⟨.privateRow 11 8, 14433471280800⟩, ⟨.privateRow 12 5, 1227010785000⟩, ⟨.privateRow 12 6, 6073703385750⟩, ⟨.privateRow 12 7, 13178095830900⟩, ⟨.privateRow 13 3, 120470149800⟩, ⟨.privateRow 13 4, 2284470988800⟩, ⟨.privateRow 13 5, 6445153014300⟩, ⟨.privateRow 13 6, 11461874252400⟩, ⟨.privateRow 14 2, 532478062116⟩, ⟨.privateRow 14 3, 3074219748600⟩, ⟨.privateRow 14 4, 3993585465870⟩, ⟨.privateRow 15 1, 1380498679560⟩, ⟨.privateRow 15 2, 487234828080⟩, ⟨.privateRow 16 0, 365426121060⟩, ⟨.hall 11 7, 103039487100⟩, ⟨.hall 10 8, 248913696720⟩, ⟨.hall 11 8, 74870947800⟩, ⟨.hall 9 9, 216134400573⟩, ⟨.hall 10 9, 11438579880⟩, ⟨.hall 9 10, 199779665085⟩, ⟨.hall 8 11, 514360296450⟩, ⟨.hall 8 12, 523769566320⟩, ⟨.hall 12 12, 30037224016800⟩, ⟨.hall 7 13, 2301627267940⟩, ⟨.hall 6 15, 10407164968200⟩, ⟨.hall 5 17, 70156320113880⟩, ⟨.hall 4 18, 79212450764304⟩, ⟨.hall 3 20, 747467040153600⟩, ⟨.hall 2 22, 11084804180049600⟩, ⟨.assumptionRow 16, 2868893183520⟩]
  caps := #[0, 0, 548841315695400, 486295005716520, 0, 0, 4733138329920, 0, 581669648560, 639689130171, 815241733020, 299740748580, 810704393070, 0, 153709920, 850972274880, 504623262780, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_25_16_checked :
    (Witness.linear .conditional case_48_25_16).check 48 25 16 = true := by
  change case_48_25_16.check 48 25 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_26_1_checked :
    (Witness.rising).check 48 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_26_2_checked :
    (Witness.rising).check 48 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_26_3_checked :
    (Witness.rising).check 48 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_26_4_checked :
    (Witness.rising).check 48 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_26_5_checked :
    (Witness.rising).check 48 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_26_6_checked :
    (Witness.rising).check 48 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_26_7_checked :
    (Witness.rising).check 48 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_26_8_checked :
    (Witness.rising).check 48 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_26_9_checked :
    (Witness.rising).check 48 26 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_26_10 : Certificate := {
  objectiveScale := 51894644516000000
  eta := 9011839782176243812800
  rows := #[⟨.count 2, 1852504547396908204800⟩, ⟨.count 3, 248558522987887912800⟩, ⟨.count 4, 33275311039674063360⟩, ⟨.count 5, 5143361249411985600⟩, ⟨.count 6, 947115114981235200⟩, ⟨.count 7, 218691510924486600⟩, ⟨.count 8, 67525799864402880⟩, ⟨.count 9, 51302068728150240⟩, ⟨.count 11, 5565313175637600⟩, ⟨.path 10, 18345861630835200⟩, ⟨.path 11, 6552462026682000⟩, ⟨.privateRow 5 17, 166972886937432576⟩, ⟨.privateRow 6 14, 134675760397464000⟩, ⟨.privateRow 6 15, 22654759694767200⟩, ⟨.privateRow 6 16, 80680176461364480⟩, ⟨.privateRow 7 9, 7773040716386400⟩, ⟨.privateRow 7 10, 11838938937265440⟩, ⟨.privateRow 7 11, 1278897724704600⟩, ⟨.privateRow 7 12, 52000894984863825⟩, ⟨.privateRow 7 13, 24429556537214400⟩, ⟨.privateRow 7 14, 3014544636803700⟩, ⟨.privateRow 8 5, 712528732335420⟩, ⟨.privateRow 8 7, 12725032360810770⟩, ⟨.privateRow 8 8, 3348386770135680⟩, ⟨.privateRow 8 9, 4066894764560628⟩, ⟨.privateRow 9 2, 630313878604410⟩, ⟨.privateRow 9 3, 1812380775581376⟩, ⟨.privateRow 9 4, 876958439797440⟩, ⟨.privateRow 10 0, 446415495372000⟩, ⟨.hall 5 16, 73263027552000⟩, ⟨.hall 5 17, 84069324115920⟩, ⟨.hall 4 19, 8944976085933888⟩, ⟨.hall 3 22, 942139329051080160⟩]
  caps := #[0, 0, 1652910568536902400, 0, 210796137502896000, 87829481578696704, 10586903240203200, 5005351074183990, 3004347328051124, 679784960879728, 0, 987148851044400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_26_10_checked :
    (Witness.linear .positive case_48_26_10).check 48 26 10 = true := by
  change case_48_26_10.check 48 26 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_26_11 : Certificate := {
  objectiveScale := 410467200000
  eta := 118310360954385600
  rows := #[⟨.count 2, 26820189136540800⟩, ⟨.count 3, 4070638173682080⟩, ⟨.count 4, 626444778960000⟩, ⟨.count 5, 109975861195200⟩, ⟨.count 6, 21127157251200⟩, ⟨.count 7, 4729043919600⟩, ⟨.count 8, 1261078378560⟩, ⟨.count 9, 515895700320⟩, ⟨.count 10, 396842846400⟩, ⟨.path 11, 88070868600⟩, ⟨.path 12, 74669114520⟩, ⟨.privateRow 6 14, 608312390400⟩, ⟨.privateRow 6 15, 1405747543200⟩, ⟨.privateRow 6 16, 1703274693120⟩, ⟨.privateRow 7 11, 259312653600⟩, ⟨.privateRow 7 12, 449105631975⟩, ⟨.privateRow 7 13, 631709020800⟩, ⟨.privateRow 7 14, 777937960800⟩, ⟨.privateRow 7 15, 859826167200⟩, ⟨.privateRow 8 7, 3582609030⟩, ⟨.privateRow 8 8, 85982616720⟩, ⟨.privateRow 8 9, 156201753708⟩, ⟨.privateRow 8 10, 221325624520⟩, ⟨.privateRow 8 11, 213165237285⟩, ⟨.privateRow 8 12, 362355313320⟩, ⟨.privateRow 9 5, 31495464000⟩, ⟨.privateRow 9 6, 57321744480⟩, ⟨.privateRow 9 7, 80399329920⟩, ⟨.privateRow 9 8, 58140626544⟩, ⟨.privateRow 10 2, 12094258176⟩, ⟨.privateRow 10 3, 25511325840⟩, ⟨.privateRow 10 4, 5233092480⟩, ⟨.privateRow 11 0, 9743909175⟩, ⟨.privateRow 12 0, 5039274240⟩, ⟨.hall 5 16, 1053532480⟩, ⟨.hall 5 17, 15642220880⟩, ⟨.hall 4 19, 259255934496⟩, ⟨.hall 6 19, 3684969288000⟩, ⟨.hall 3 22, 21734910156960⟩]
  caps := #[0, 0, 0, 3050946035280, 4749999162480, 632772504000, 0, 291214934010, 0, 27927355872, 13624353600, 11631712950, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_26_11_checked :
    (Witness.linear .positive case_48_26_11).check 48 26 11 = true := by
  change case_48_26_11.check 48 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_26_12 : Certificate := {
  objectiveScale := 78078000000
  eta := 31406945176807200
  rows := #[⟨.count 2, 7741767998764800⟩, ⟨.count 3, 1319619545244000⟩, ⟨.count 4, 237068493742080⟩, ⟨.count 5, 45787968626400⟩, ⟨.count 6, 9623644430400⟩, ⟨.count 7, 2224332910800⟩, ⟨.count 8, 593155442880⟩, ⟨.count 9, 190657106640⟩, ⟨.count 10, 83805321600⟩, ⟨.count 11, 76821544800⟩, ⟨.path 12, 4225321100⟩, ⟨.path 13, 20240159940⟩, ⟨.privateRow 4 22, 12038634447840⟩, ⟨.privateRow 6 15, 287498811600⟩, ⟨.privateRow 6 16, 811049279040⟩, ⟨.privateRow 7 12, 70928983125⟩, ⟨.privateRow 7 13, 226972746000⟩, ⟨.privateRow 7 14, 344241998100⟩, ⟨.privateRow 7 15, 540195135480⟩, ⟨.privateRow 8 9, 13240076850⟩, ⟨.privateRow 8 10, 65906160320⟩, ⟨.privateRow 8 11, 107244622485⟩, ⟨.privateRow 8 12, 102894311520⟩, ⟨.privateRow 8 13, 316879172610⟩, ⟨.privateRow 8 14, 169472983680⟩, ⟨.privateRow 9 6, 252191940⟩, ⟨.privateRow 9 7, 19533412080⟩, ⟨.privateRow 9 8, 34197227064⟩, ⟨.privateRow 9 9, 53128435360⟩, ⟨.privateRow 9 10, 64308944700⟩, ⟨.privateRow 9 11, 59661407520⟩, ⟨.privateRow 10 4, 3867937920⟩, ⟨.privateRow 10 5, 11872420560⟩, ⟨.privateRow 10 6, 19618063920⟩, ⟨.privateRow 10 7, 16761064320⟩, ⟨.privateRow 11 2, 5362542900⟩, ⟨.privateRow 11 3, 4834922400⟩, ⟨.privateRow 12 0, 2444321880⟩, ⟨.privateRow 13 0, 1496523600⟩, ⟨.hall 6 13, 129497940⟩, ⟨.hall 6 14, 99939840⟩, ⟨.hall 5 16, 1188272800⟩, ⟨.hall 5 17, 7005753040⟩, ⟨.hall 7 18, 397202305500⟩, ⟨.hall 4 19, 104230601280⟩]
  caps := #[0, 0, 23873497808160, 0, 161907225480, 0, 12134622500, 41989958010, 0, 2640337700, 225398880, 6745318800, 5932466540, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_26_12_checked :
    (Witness.linear .positive case_48_26_12).check 48 26 12 = true := by
  change case_48_26_12.check 48 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_26_13 : Certificate := {
  objectiveScale := 46846800000
  eta := 25248720632335200
  rows := #[⟨.count 2, 6040925029339200⟩, ⟨.count 3, 1302024617974080⟩, ⟨.count 4, 275962543496640⟩, ⟨.count 5, 64308944700000⟩, ⟨.count 6, 14889412137600⟩, ⟨.count 7, 3813142132800⟩, ⟨.count 8, 974469656160⟩, ⟨.count 9, 299604024720⟩, ⟨.count 10, 104756652000⟩, ⟨.count 11, 38410772400⟩, ⟨.count 12, 41902660800⟩, ⟨.path 14, 11498366880⟩, ⟨.privateRow 9 15, 453945492000⟩, ⟨.privateRow 10 13, 393885011520⟩, ⟨.privateRow 13 0, 299304720⟩, ⟨.privateRow 13 4, 1676106432⟩, ⟨.privateRow 13 11, 1396755360⟩, ⟨.privateRow 14 0, 931170240⟩, ⟨.privateRow 14 4, 336255920⟩, ⟨.privateRow 15 0, 882671790⟩, ⟨.privateRow 15 2, 1059206148⟩, ⟨.privateRow 16 2, 5043838800⟩, ⟨.hall 11 3, 145815120⟩, ⟨.hall 10 5, 51017850⟩, ⟨.hall 8 10, 17549350⟩, ⟨.hall 7 12, 427251825⟩, ⟨.hall 5 17, 43216470440⟩, ⟨.hall 4 20, 2513561038560⟩]
  caps := #[0, 0, 0, 0, 0, 574997623200, 0, 0, 3339816480, 4271256990, 435314880, 21666194550, 10065163680, 0, 0, 27186291132, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_26_13_checked :
    (Witness.linear .positive case_48_26_13).check 48 26 13 = true := by
  change case_48_26_13.check 48 26 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_26_14 : Certificate := {
  objectiveScale := 1450449000000
  eta := 1076457650373705600
  rows := #[⟨.count 2, 258997329413222400⟩, ⟨.count 3, 60702499081224000⟩, ⟨.count 4, 13972224349923840⟩, ⟨.count 5, 3644516514038400⟩, ⟨.count 6, 952196064019200⟩, ⟨.count 7, 255798284742000⟩, ⟨.count 8, 77957572492800⟩, ⟨.count 9, 26310680716320⟩, ⟨.count 10, 9637611984000⟩, ⟨.count 11, 4417238826000⟩, ⟨.count 12, 2891283595200⟩, ⟨.count 13, 2505779115840⟩, ⟨.path 14, 414414000000⟩, ⟨.privateRow 3 23, 134894442402720⟩, ⟨.privateRow 6 16, 35916167327040⟩, ⟨.privateRow 7 14, 22534610798700⟩, ⟨.privateRow 7 15, 63270922674960⟩, ⟨.privateRow 8 12, 11032388607240⟩, ⟨.privateRow 8 13, 27650576493540⟩, ⟨.privateRow 8 14, 45166668563016⟩, ⟨.privateRow 8 15, 2862504614970⟩, ⟨.privateRow 9 9, 618710892800⟩, ⟨.privateRow 9 10, 4385113452720⟩, ⟨.privateRow 9 11, 12349911356640⟩, ⟨.privateRow 9 12, 20347854486960⟩, ⟨.privateRow 9 13, 26282838726144⟩, ⟨.privateRow 9 14, 12389685628320⟩, ⟨.privateRow 10 7, 491518211184⟩, ⟨.privateRow 10 8, 2130983094240⟩, ⟨.privateRow 10 9, 5180216441400⟩, ⟨.privateRow 10 10, 2946355663680⟩, ⟨.privateRow 10 11, 24736537425600⟩, ⟨.privateRow 10 12, 1060137318240⟩, ⟨.privateRow 11 5, 299350069200⟩, ⟨.privateRow 11 6, 1108325378160⟩, ⟨.privateRow 11 7, 2507563858800⟩, ⟨.privateRow 11 8, 4196376884700⟩, ⟨.privateRow 11 9, 2306142867600⟩, ⟨.privateRow 12 3, 180705224700⟩, ⟨.privateRow 12 4, 627905023200⟩, ⟨.privateRow 12 5, 1333202991120⟩, ⟨.privateRow 12 6, 472956884400⟩, ⟨.privateRow 13 1, 118616762880⟩, ⟨.privateRow 13 2, 409598509320⟩, ⟨.privateRow 13 3, 35045861760⟩, ⟨.privateRow 14 0, 149918408640⟩, ⟨.privateRow 15 0, 121808707020⟩, ⟨.hall 7 13, 68756462775⟩, ⟨.hall 8 14, 102701458860⟩, ⟨.hall 6 15, 59799940200⟩, ⟨.hall 8 15, 357464767660⟩, ⟨.hall 6 16, 1231340029920⟩, ⟨.hall 5 18, 13908783688800⟩, ⟨.hall 4 19, 16393870033632⟩, ⟨.hall 3 22, 2762403581377440⟩, ⟨.assumptionRow 14, 2706598269375⟩]
  caps := #[0, 1080911726294400, 0, 201854428776000, 68257892192490, 0, 1520386542675, 2088149263200, 908778820950, 0, 165653362875, 982436872950, 0, 82202390655, 20179544385, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_26_14_checked :
    (Witness.linear .conditional case_48_26_14).check 48 26 14 = true := by
  change case_48_26_14.check 48 26 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_26_15 : Certificate := {
  objectiveScale := 753737600000
  eta := 274562072767382400
  rows := #[⟨.count 2, 68484870758304000⟩, ⟨.count 3, 18490915104742080⟩, ⟨.count 4, 5072467939418880⟩, ⟨.count 5, 1441786752806400⟩, ⟨.count 6, 420199882502400⟩, ⟨.count 7, 128180239387200⟩, ⟨.count 8, 41377480784640⟩, ⟨.count 9, 13878161256960⟩, ⟨.count 10, 5337754329600⟩, ⟨.count 11, 2038725612000⟩, ⟨.count 12, 889625721600⟩, ⟨.count 13, 578256719040⟩, ⟨.count 14, 899510451840⟩, ⟨.path 12, 135452597280⟩, ⟨.privateRow 3 23, 2303582016415680⟩, ⟨.privateRow 6 16, 23772776227200⟩, ⟨.privateRow 7 14, 9637611984000⟩, ⟨.privateRow 7 15, 39755149434000⟩, ⟨.privateRow 8 12, 3710480613840⟩, ⟨.privateRow 8 13, 15197978675880⟩, ⟨.privateRow 8 14, 31842669995136⟩, ⟨.privateRow 9 10, 1381391051040⟩, ⟨.privateRow 9 11, 5975319430080⟩, ⟨.privateRow 9 12, 13214236875840⟩, ⟨.privateRow 9 13, 21009994125120⟩, ⟨.privateRow 9 14, 12368268712800⟩, ⟨.privateRow 10 8, 504121242240⟩, ⟨.privateRow 10 9, 2407549609080⟩, ⟨.privateRow 10 10, 5604642046080⟩, ⟨.privateRow 10 11, 9259521052320⟩, ⟨.privateRow 10 12, 12223457414784⟩, ⟨.privateRow 10 13, 4225722177600⟩, ⟨.privateRow 11 6, 177925144320⟩, ⟨.privateRow 11 7, 1000828936800⟩, ⟨.privateRow 11 8, 2488171940100⟩, ⟨.privateRow 11 9, 4368697740000⟩, ⟨.privateRow 11 10, 5980261795200⟩, ⟨.privateRow 12 4, 53916710400⟩, ⟨.privateRow 12 5, 437399313120⟩, ⟨.privateRow 12 6, 786659781600⟩, ⟨.privateRow 12 7, 2946885202800⟩, ⟨.privateRow 13 3, 210275170560⟩, ⟨.privateRow 13 4, 591601104864⟩, ⟨.privateRow 13 5, 321253732800⟩, ⟨.privateRow 14 1, 85667662080⟩, ⟨.privateRow 14 2, 157706377920⟩, ⟨.privateRow 15 0, 37479602160⟩, ⟨.hall 7 14, 169963613820⟩, ⟨.hall 8 14, 260446490304⟩, ⟨.hall 7 15, 58851968175⟩, ⟨.hall 9 16, 30851696715840⟩, ⟨.hall 6 17, 6870321057600⟩, ⟨.hall 5 18, 10780276890240⟩, ⟨.hall 4 19, 13592287156032⟩, ⟨.hall 3 21, 132146516698560⟩, ⟨.assumptionRow 15, 766975116600⟩]
  caps := #[0, 3067487606629600, 0, 0, 13187277863760, 0, 2720033258800, 0, 0, 558204054408, 0, 51546371800, 203998302200, 205989756280, 0, 548786924840, 753737600000, 0, 0, 0, 0, 0, 0] }

theorem case_48_26_15_checked :
    (Witness.linear .conditional case_48_26_15).check 48 26 15 = true := by
  change case_48_26_15.check 48 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_26_16 : Certificate := {
  objectiveScale := 594669600000
  eta := 150355420801185600
  rows := #[⟨.count 2, 41713512189148800⟩, ⟨.count 3, 11673557515620000⟩, ⟨.count 4, 3303002379156480⟩, ⟨.count 5, 961191168537600⟩, ⟨.count 6, 285273314726400⟩, ⟨.count 7, 86858978005800⟩, ⟨.count 8, 26985313555200⟩, ⟨.count 9, 9541235864160⟩, ⟨.count 10, 3558502886400⟩, ⟨.count 11, 1427107928400⟩, ⟨.count 12, 667219291200⟩, ⟨.count 13, 289128359520⟩, ⟨.count 14, 449755225920⟩, ⟨.path 11, 28683369000⟩, ⟨.path 12, 75194038920⟩, ⟨.privateRow 6 16, 7645838840640⟩, ⟨.privateRow 7 14, 2168462696400⟩, ⟨.privateRow 7 15, 24021747870120⟩, ⟨.privateRow 8 12, 457786569240⟩, ⟨.privateRow 8 13, 8058114464400⟩, ⟨.privateRow 8 14, 23297320702656⟩, ⟨.privateRow 8 15, 25523609070960⟩, ⟨.privateRow 9 11, 2648048626080⟩, ⟨.privateRow 9 12, 8722038845520⟩, ⟨.privateRow 9 13, 17431227541728⟩, ⟨.privateRow 9 14, 20054264270040⟩, ⟨.privateRow 10 9, 736721300700⟩, ⟨.privateRow 10 10, 3291615169920⟩, ⟨.privateRow 10 11, 7313464786320⟩, ⟨.privateRow 10 12, 11787540811200⟩, ⟨.privateRow 10 13, 12649365729000⟩, ⟨.privateRow 11 7, 203872561200⟩, ⟨.privateRow 11 8, 1179217427850⟩, ⟨.privateRow 11 9, 3113690025600⟩, ⟨.privateRow 11 10, 5532359956200⟩, ⟨.privateRow 11 11, 7528457669040⟩, ⟨.privateRow 11 12, 5532359956200⟩, ⟨.privateRow 12 5, 37067738400⟩, ⟨.privateRow 12 6, 436575585600⟩, ⟨.privateRow 12 7, 1318221446850⟩, ⟨.privateRow 12 8, 2679467947200⟩, ⟨.privateRow 12 9, 3320651565000⟩, ⟨.privateRow 13 4, 137891986848⟩, ⟨.privateRow 13 5, 311369002560⟩, ⟨.privateRow 13 6, 1893234738780⟩, ⟨.privateRow 13 7, 162038970720⟩, ⟨.privateRow 14 2, 23363907840⟩, ⟨.privateRow 14 3, 263428060896⟩, ⟨.privateRow 14 4, 428338310400⟩, ⟨.privateRow 15 1, 107327951640⟩, ⟨.privateRow 15 2, 61841343564⟩, ⟨.privateRow 16 0, 32855495400⟩, ⟨.hall 9 12, 19493269488⟩, ⟨.hall 8 13, 57783677952⟩, ⟨.hall 9 13, 56398252482⟩, ⟨.hall 8 14, 124564560120⟩, ⟨.hall 7 15, 490723157925⟩, ⟨.hall 7 16, 770768598600⟩, ⟨.hall 6 17, 6371532367200⟩, ⟨.hall 5 18, 9137776602240⟩, ⟨.hall 4 19, 10941067713888⟩, ⟨.hall 3 21, 111660115366800⟩, ⟨.hall 2 23, 1738063007881200⟩, ⟨.assumptionRow 16, 380976669920⟩]
  caps := #[0, 2488782452942720, 118433391981520, 0, 11143403229200, 2102751705600, 593669905920, 96554252080, 152241258312, 38465645280, 328759843060, 0, 6077695030, 354263824816, 0, 380976669920, 0, 594669600000, 0, 0, 0, 0, 0] }

theorem case_48_26_16_checked :
    (Witness.linear .conditional case_48_26_16).check 48 26 16 = true := by
  change case_48_26_16.check 48 26 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_27_1_checked :
    (Witness.rising).check 48 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_27_2_checked :
    (Witness.rising).check 48 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_27_3_checked :
    (Witness.rising).check 48 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_27_4_checked :
    (Witness.rising).check 48 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_27_5_checked :
    (Witness.rising).check 48 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_27_6_checked :
    (Witness.rising).check 48 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_27_7_checked :
    (Witness.rising).check 48 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_27_8_checked :
    (Witness.rising).check 48 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_27_9_checked :
    (Witness.rising).check 48 27 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_27_10_checked :
    (Witness.linear .positive case_48_27_10).check 48 27 10 = true := by
  change case_48_27_10.check 48 27 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_27_11 : Certificate := {
  objectiveScale := 275808000000
  eta := 101933278650403200
  rows := #[⟨.count 2, 20515685196726720⟩, ⟨.count 3, 2872603389015360⟩, ⟨.count 4, 443680271274240⟩, ⟨.count 5, 77231259705600⟩, ⟨.count 6, 14980201236000⟩, ⟨.count 7, 3262354935840⟩, ⟨.count 8, 798944065920⟩, ⟨.count 9, 368743415040⟩, ⟨.count 10, 307286179200⟩, ⟨.path 11, 62230396800⟩, ⟨.path 12, 48494245800⟩, ⟨.privateRow 5 18, 3462090952320⟩, ⟨.privateRow 5 19, 5059979084160⟩, ⟨.privateRow 6 14, 364102113375⟩, ⟨.privateRow 6 15, 1022458179600⟩, ⟨.privateRow 6 16, 1484149566900⟩, ⟨.privateRow 6 17, 2047294168920⟩, ⟨.privateRow 6 18, 2559117711150⟩, ⟨.privateRow 7 11, 169775614008⟩, ⟨.privateRow 7 12, 343989806160⟩, ⟨.privateRow 7 13, 503501208210⟩, ⟨.privateRow 7 15, 1930781492640⟩, ⟨.privateRow 7 16, 186420282048⟩, ⟨.privateRow 7 17, 16644668040⟩, ⟨.privateRow 8 8, 59643393810⟩, ⟨.privateRow 8 9, 124078434480⟩, ⟨.privateRow 8 10, 179762414832⟩, ⟨.privateRow 8 11, 220079499640⟩, ⟨.privateRow 8 12, 185171931945⟩, ⟨.privateRow 9 5, 21217379040⟩, ⟨.privateRow 9 6, 46486883520⟩, ⟨.privateRow 9 7, 69139390320⟩, ⟨.privateRow 9 8, 25141596480⟩, ⟨.privateRow 10 2, 8642423790⟩, ⟨.privateRow 10 3, 19461458016⟩, ⟨.privateRow 11 0, 5751345600⟩, ⟨.privateRow 12 0, 2880807930⟩, ⟨.hall 5 20, 345863232000⟩, ⟨.hall 4 21, 1440520361280⟩, ⟨.hall 3 23, 44990537712120⟩]
  caps := #[0, 49279746172800, 0, 0, 2970532833840, 0, 0, 65621652876, 128823518629, 0, 0, 5271427200, 2401318920, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_27_11_checked :
    (Witness.linear .positive case_48_27_11).check 48 27 11 = true := by
  change case_48_27_11.check 48 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_27_12 : Certificate := {
  objectiveScale := 217672000000
  eta := 113311331618284800
  rows := #[⟨.count 2, 23673974641677360⟩, ⟨.count 3, 3801893363508240⟩, ⟨.count 4, 688671627003360⟩, ⟨.count 5, 133641552844800⟩, ⟨.count 6, 28190015053200⟩, ⟨.count 7, 6577670179080⟩, ⟨.count 8, 1670519410560⟩, ⟨.count 9, 578256719040⟩, ⟨.count 10, 240940299600⟩, ⟨.count 11, 240940299600⟩, ⟨.path 12, 14411246850⟩, ⟨.path 13, 54605197920⟩, ⟨.privateRow 5 18, 2255201204256⟩, ⟨.privateRow 5 19, 10023116463360⟩, ⟨.privateRow 6 15, 764411783850⟩, ⟨.privateRow 6 16, 2631938133825⟩, ⟨.privateRow 6 17, 3810872405340⟩, ⟨.privateRow 6 18, 6460211783025⟩, ⟨.privateRow 6 19, 304521767550⟩, ⟨.privateRow 7 12, 185613267840⟩, ⟨.privateRow 7 13, 730852242120⟩, ⟨.privateRow 7 14, 1185770474460⟩, ⟨.privateRow 7 15, 1696621276350⟩, ⟨.privateRow 7 16, 2234319711624⟩, ⟨.privateRow 7 17, 2362218853995⟩, ⟨.privateRow 8 9, 30847659570⟩, ⟨.privateRow 8 10, 208814926320⟩, ⟨.privateRow 8 11, 368326328370⟩, ⟨.privateRow 8 12, 548139181590⟩, ⟨.privateRow 8 13, 499664287980⟩, ⟨.privateRow 8 14, 1200685826340⟩, ⟨.privateRow 9 7, 58896517680⟩, ⟨.privateRow 9 8, 119740027680⟩, ⟨.privateRow 9 9, 189539702352⟩, ⟨.privateRow 9 10, 242725042560⟩, ⟨.privateRow 9 11, 104407463160⟩, ⟨.privateRow 10 4, 11186513910⟩, ⟨.privateRow 10 5, 41701205700⟩, ⟨.privateRow 10 6, 70274254050⟩, ⟨.privateRow 10 7, 31760312220⟩, ⟨.privateRow 11 2, 16792808760⟩, ⟨.privateRow 11 3, 10951831800⟩, ⟨.privateRow 12 0, 6023507490⟩, ⟨.privateRow 13 0, 3212537328⟩, ⟨.privateRow 14 8, 8700621930⟩, ⟨.hall 14 11, 4684950270⟩, ⟨.hall 5 19, 138305990160⟩, ⟨.hall 6 20, 4101721767000⟩, ⟨.hall 4 21, 3732257299680⟩, ⟨.hall 3 23, 99839636646750⟩]
  caps := #[0, 0, 11069300336640, 16225693163680, 0, 0, 260077032150, 130765451154, 28729928682, 0, 0, 60995461800, 0, 6417138000, 113108085090, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_27_12_checked :
    (Witness.linear .positive case_48_27_12).check 48 27 12 = true := by
  change case_48_27_12.check 48 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_27_13 : Certificate := {
  objectiveScale := 168355687500
  eta := 124102887010502400
  rows := #[⟨.count 2, 26709099595738560⟩, ⟨.count 3, 5324780621160000⟩, ⟨.count 4, 1164352029160320⟩, ⟨.count 5, 253362110601600⟩, ⟨.count 6, 57424104738000⟩, ⟨.count 7, 14129810014320⟩, ⟨.count 8, 3619458722880⟩, ⟨.count 9, 1156513438080⟩, ⟨.count 10, 321253732800⟩, ⟨.count 11, 160626866400⟩, ⟨.count 12, 192752239680⟩, ⟨.path 14, 43165756920⟩, ⟨.privateRow 11 12, 84694165920⟩, ⟨.privateRow 13 0, 2855588736⟩, ⟨.privateRow 14 0, 2485891980⟩, ⟨.hall 14 1, 5354228880⟩, ⟨.hall 11 3, 544984011⟩, ⟨.hall 12 4, 47070144⟩, ⟨.hall 10 5, 113270400⟩, ⟨.hall 9 7, 121136400⟩, ⟨.hall 8 10, 84724640⟩, ⟨.hall 10 14, 157477320⟩, ⟨.hall 5 17, 40873826240⟩, ⟨.hall 4 20, 1281056449920⟩]
  caps := #[0, 0, 0, 3515051259720, 0, 0, 0, 114889769280, 6464858400, 0, 58623399120, 93592262400, 0, 0, 75482352660, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_27_13_checked :
    (Witness.linear .positive case_48_27_13).check 48 27 13 = true := by
  change case_48_27_13.check 48 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_27_14 : Certificate := {
  objectiveScale := 553104552000
  eta := 519343603250472000
  rows := #[⟨.count 2, 109804076115814080⟩, ⟨.count 3, 26240518901076480⟩, ⟨.count 4, 6091549030607040⟩, ⟨.count 5, 1546622554276800⟩, ⟨.count 6, 407711143639800⟩, ⟨.count 7, 109871453732040⟩, ⟨.count 8, 32157498653280⟩, ⟨.count 9, 10601373182400⟩, ⟨.count 10, 4417238826000⟩, ⟨.count 11, 1766895530400⟩, ⟨.count 12, 1060137318240⟩, ⟨.count 13, 1531309459680⟩, ⟨.path 14, 166326440280⟩, ⟨.privateRow 3 24, 2499097038197760⟩, ⟨.privateRow 5 19, 164615766915600⟩, ⟨.privateRow 6 16, 12282377957850⟩, ⟨.privateRow 6 17, 63549342576720⟩, ⟨.privateRow 6 18, 148824138112650⟩, ⟨.privateRow 6 19, 147069512690100⟩, ⟨.privateRow 7 14, 9515994499440⟩, ⟨.privateRow 7 15, 26287479057840⟩, ⟨.privateRow 7 16, 57270973792032⟩, ⟨.privateRow 7 17, 86614691313150⟩, ⟨.privateRow 7 18, 84349629404040⟩, ⟨.privateRow 8 12, 5120316005805⟩, ⟨.privateRow 8 13, 11703579441840⟩, ⟨.privateRow 8 14, 23192957858070⟩, ⟨.privateRow 8 15, 34416180106308⟩, ⟨.privateRow 8 16, 40579700681520⟩, ⟨.privateRow 8 17, 31774671288360⟩, ⟨.privateRow 9 9, 176689553040⟩, ⟨.privateRow 9 10, 2277332016960⟩, ⟨.privateRow 9 11, 5374307238300⟩, ⟨.privateRow 9 12, 10180683770400⟩, ⟨.privateRow 9 13, 9246753275760⟩, ⟨.privateRow 9 14, 27940507987392⟩, ⟨.privateRow 10 7, 192752239680⟩, ⟨.privateRow 10 8, 1051302840588⟩, ⟨.privateRow 10 9, 2424573311160⟩, ⟨.privateRow 10 10, 3379187701890⟩, ⟨.privateRow 10 11, 9730546099560⟩, ⟨.privateRow 11 5, 133855722000⟩, ⟨.privateRow 11 6, 554892811200⟩, ⟨.privateRow 11 7, 722820898800⟩, ⟨.privateRow 11 8, 3239308472400⟩, ⟨.privateRow 12 3, 88344776520⟩, ⟨.privateRow 12 4, 287120523690⟩, ⟨.privateRow 12 5, 730852242120⟩, ⟨.privateRow 13 1, 58896517680⟩, ⟨.privateRow 13 2, 163098048960⟩, ⟨.privateRow 14 0, 54689623560⟩, ⟨.privateRow 15 0, 29448258840⟩, ⟨.hall 6 18, 437516988480⟩, ⟨.hall 6 19, 11101993582680⟩, ⟨.hall 7 19, 48236247979920⟩, ⟨.hall 5 20, 43851134527200⟩, ⟨.hall 4 21, 110199807637920⟩, ⟨.hall 3 22, 139216003486560⟩, ⟨.assumptionRow 14, 1081187707600⟩]
  caps := #[0, 0, 29860534463760, 20417459462400, 0, 4508855631280, 2117529735750, 986236211532, 815567242061, 322827400896, 0, 394041575200, 21050389360, 0, 0, 170277187080, 0, 0, 0, 0, 0, 0] }

theorem case_48_27_14_checked :
    (Witness.linear .conditional case_48_27_14).check 48 27 14 = true := by
  change case_48_27_14.check 48 27 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_27_15 : Certificate := {
  objectiveScale := 21252000000
  eta := 11932969904856000
  rows := #[⟨.count 2, 2957301237290400⟩, ⟨.count 3, 745469286962400⟩, ⟨.count 4, 191145971016000⟩, ⟨.count 5, 53542288800000⟩, ⟨.count 6, 15460335891000⟩, ⟨.count 7, 4591251264600⟩, ⟨.count 8, 1445641797600⟩, ⟨.count 9, 481880599200⟩, ⟨.count 10, 185338692000⟩, ⟨.count 11, 61779564000⟩, ⟨.count 12, 37067738400⟩, ⟨.path 12, 4360765500⟩, ⟨.privateRow 2 25, 77823716770800⟩, ⟨.privateRow 5 19, 8058114464400⟩, ⟨.privateRow 6 16, 267711444000⟩, ⟨.privateRow 6 17, 2817662948100⟩, ⟨.privateRow 6 18, 7504286414625⟩, ⟨.privateRow 6 19, 8823323008500⟩, ⟨.privateRow 7 14, 177836887800⟩, ⟨.privateRow 7 15, 1061922061200⟩, ⟨.privateRow 7 16, 2794907475360⟩, ⟨.privateRow 7 17, 4848923529450⟩, ⟨.privateRow 7 18, 5720101186800⟩, ⟨.privateRow 8 12, 87006219300⟩, ⟨.privateRow 8 13, 417821075100⟩, ⟨.privateRow 8 14, 1089808669950⟩, ⟨.privateRow 8 15, 1922168167920⟩, ⟨.privateRow 8 16, 2643650509500⟩, ⟨.privateRow 8 17, 2556644290200⟩, ⟨.privateRow 9 10, 37067738400⟩, ⟨.privateRow 9 11, 169893801000⟩, ⟨.privateRow 9 12, 446577991200⟩, ⟨.privateRow 9 13, 804507211200⟩, ⟨.privateRow 9 14, 541188980640⟩, ⟨.privateRow 9 15, 2446470734400⟩, ⟨.privateRow 9 16, 181220054400⟩, ⟨.privateRow 10 8, 14827095360⟩, ⟨.privateRow 10 9, 71046498600⟩, ⟨.privateRow 10 10, 192675015225⟩, ⟨.privateRow 10 11, 240499017000⟩, ⟨.privateRow 10 12, 764522104500⟩, ⟨.privateRow 10 13, 251442825480⟩, ⟨.privateRow 11 6, 5616324000⟩, ⟨.privateRow 11 7, 30889782000⟩, ⟨.privateRow 11 8, 87989076000⟩, ⟨.privateRow 11 9, 172701963000⟩, ⟨.privateRow 11 10, 192158514000⟩, ⟨.privateRow 12 4, 1801903950⟩, ⟨.privateRow 12 5, 14040810000⟩, ⟨.privateRow 12 6, 42627899160⟩, ⟨.privateRow 12 7, 82715971800⟩, ⟨.privateRow 13 3, 6864396000⟩, ⟨.privateRow 13 4, 22465296000⟩, ⟨.privateRow 13 5, 6589820160⟩, ⟨.privateRow 14 1, 2574148500⟩, ⟨.privateRow 14 2, 5019589575⟩, ⟨.privateRow 15 0, 2059318800⟩, ⟨.privateRow 16 0, 2788660875⟩, ⟨.hall 7 17, 31096014950⟩, ⟨.hall 7 18, 72000288360⟩, ⟨.hall 6 19, 729991741050⟩, ⟨.hall 6 20, 7926170967000⟩, ⟨.hall 4 21, 6396716289600⟩, ⟨.hall 5 21, 57387598632000⟩, ⟨.hall 3 22, 8919155945700⟩, ⟨.hall 2 24, 182626322022144⟩, ⟨.assumptionRow 15, 23615243652⟩]
  caps := #[0, 0, 0, 2505349779072, 0, 337541452248, 649801152, 67420830672, 1590886080, 0, 16420302669, 5859862260, 0, 23988703116, 72327606351, 38203636548, 0, 0, 0, 0, 0, 0] }

theorem case_48_27_15_checked :
    (Witness.linear .conditional case_48_27_15).check 48 27 15 = true := by
  change case_48_27_15.check 48 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_27_16 : Certificate := {
  objectiveScale := 403788000000
  eta := 175362775123536000
  rows := #[⟨.count 2, 43840693780884000⟩, ⟨.count 3, 11288534916859200⟩, ⟨.count 4, 2958211456200000⟩, ⟨.count 5, 828299207736000⟩, ⟨.count 6, 234916792110000⟩, ⟨.count 7, 66994788861000⟩, ⟨.count 8, 20881492632000⟩, ⟨.count 9, 7228208988000⟩, ⟨.count 10, 2409402996000⟩, ⟨.count 11, 803134332000⟩, ⟨.count 12, 481880599200⟩, ⟨.path 11, 94127592000⟩, ⟨.privateRow 2 25, 3035124954061200⟩, ⟨.privateRow 5 19, 149650697196000⟩, ⟨.privateRow 6 16, 1305093289500⟩, ⟨.privateRow 6 17, 48897495246600⟩, ⟨.privateRow 6 18, 146061690649875⟩, ⟨.privateRow 6 19, 196489045252500⟩, ⟨.privateRow 7 14, 596614075200⟩, ⟨.privateRow 7 15, 16386171301500⟩, ⟨.privateRow 7 16, 51925311678240⟩, ⟨.privateRow 7 17, 102754344993300⟩, ⟨.privateRow 7 18, 142690199652000⟩, ⟨.privateRow 8 12, 87006219300⟩, ⟨.privateRow 8 13, 5481391815900⟩, ⟨.privateRow 8 14, 18865848551550⟩, ⟨.privateRow 8 15, 39570428537640⟩, ⟨.privateRow 8 16, 63231769876275⟩, ⟨.privateRow 8 17, 76768487495700⟩, ⟨.privateRow 9 11, 1699967669400⟩, ⟨.privateRow 9 12, 6975795340800⟩, ⟨.privateRow 9 13, 15786051481200⟩, ⟨.privateRow 9 14, 26546266787040⟩, ⟨.privateRow 9 15, 35378067324600⟩, ⟨.privateRow 9 16, 34320607120800⟩, ⟨.privateRow 10 9, 486342456600⟩, ⟨.privateRow 10 10, 2539912324950⟩, ⟨.privateRow 10 11, 6528334784400⟩, ⟨.privateRow 10 12, 11792689108200⟩, ⟨.privateRow 10 13, 16721256792240⟩, ⟨.privateRow 10 14, 15992412385950⟩, ⟨.privateRow 11 7, 120470149800⟩, ⟨.privateRow 11 8, 912652650000⟩, ⟨.privateRow 11 9, 2747084476500⟩, ⟨.privateRow 11 10, 5538497796000⟩, ⟨.privateRow 11 11, 8548513155000⟩, ⟨.privateRow 11 12, 1452943018800⟩, ⟨.privateRow 12 5, 10951831800⟩, ⟨.privateRow 12 6, 321253732800⟩, ⟨.privateRow 12 7, 1173468496200⟩, ⟨.privateRow 12 8, 2710578370500⟩, ⟨.privateRow 12 9, 2397929648400⟩, ⟨.privateRow 13 4, 77879692800⟩, ⟨.privateRow 13 5, 514005972480⟩, ⟨.privateRow 13 6, 1380201222400⟩, ⟨.privateRow 13 7, 53542288800⟩, ⟨.privateRow 14 2, 14501036550⟩, ⟨.privateRow 14 3, 197741407500⟩, ⟨.privateRow 14 4, 348024877200⟩, ⟨.privateRow 15 1, 72505182750⟩, ⟨.privateRow 15 2, 47457937800⟩, ⟨.privateRow 16 0, 36252591375⟩, ⟨.hall 7 18, 3667083179760⟩, ⟨.hall 8 18, 48979922191200⟩, ⟨.hall 7 19, 165111702365610⟩, ⟨.hall 6 20, 617495567832000⟩, ⟨.hall 4 21, 141807069331200⟩, ⟨.hall 5 21, 1385139011256000⟩, ⟨.hall 3 22, 196206590279700⟩, ⟨.hall 2 24, 4397558822328672⟩, ⟨.assumptionRow 16, 302163061200⟩]
  caps := #[0, 0, 0, 0, 7722375120000, 0, 222564110925, 1005146374440, 2778926700, 0, 200913809460, 101039128800, 20820584400, 655810406160, 302163061200, 1888935961500, 0, 403788000000, 0, 0, 0, 0] }

theorem case_48_27_16_checked :
    (Witness.linear .conditional case_48_27_16).check 48 27 16 = true := by
  change case_48_27_16.check 48 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_27_17 : Certificate := {
  objectiveScale := 88803000000
  eta := 44515165992897600
  rows := #[⟨.count 2, 11196238719425760⟩, ⟨.count 3, 2832783290457120⟩, ⟨.count 4, 728903302807680⟩, ⟨.count 5, 196286030740800⟩, ⟨.count 6, 52725768895800⟩, ⟨.count 7, 14129810014320⟩, ⟨.count 8, 3758668673760⟩, ⟨.count 9, 1060137318240⟩, ⟨.count 10, 240940299600⟩, ⟨.count 11, 80313433200⟩, ⟨.path 11, 30841012800⟩, ⟨.privateRow 2 25, 876813875617680⟩, ⟨.privateRow 5 19, 37029846934080⟩, ⟨.privateRow 6 16, 319022804100⟩, ⟨.privateRow 6 17, 11589228410760⟩, ⟨.privateRow 6 18, 36694872989775⟩, ⟨.privateRow 6 19, 53102795846100⟩, ⟨.privateRow 7 14, 149153518800⟩, ⟨.privateRow 7 15, 3677462869080⟩, ⟨.privateRow 7 16, 12514974584112⟩, ⟨.privateRow 7 17, 26684807459310⟩, ⟨.privateRow 7 18, 40452091559880⟩, ⟨.privateRow 8 12, 34802487720⟩, ⟨.privateRow 8 13, 1148482094760⟩, ⟨.privateRow 8 14, 4303907648040⟩, ⟨.privateRow 8 15, 9890867010024⟩, ⟨.privateRow 8 16, 17357740750350⟩, ⟨.privateRow 8 17, 23717895381180⟩, ⟨.privateRow 9 11, 338654976660⟩, ⟨.privateRow 9 12, 1477767170880⟩, ⟨.privateRow 9 13, 3744390730080⟩, ⟨.privateRow 9 14, 7035456748320⟩, ⟨.privateRow 9 15, 10545153779160⟩, ⟨.privateRow 9 16, 11975625261600⟩, ⟨.privateRow 10 9, 81205804680⟩, ⟨.privateRow 10 10, 494931532095⟩, ⟨.privateRow 10 11, 1442199793320⟩, ⟨.privateRow 10 12, 2970258471180⟩, ⟨.privateRow 10 13, 4791499424712⟩, ⟨.privateRow 10 14, 6119883609840⟩, ⟨.privateRow 10 15, 4701012956640⟩, ⟨.privateRow 11 7, 15332564520⟩, ⟨.privateRow 11 8, 149269411200⟩, ⟨.privateRow 11 9, 555805463850⟩, ⟨.privateRow 11 10, 1301703436800⟩, ⟨.privateRow 11 11, 2312053380000⟩, ⟨.privateRow 11 12, 3272407341840⟩, ⟨.privateRow 11 13, 89439959700⟩, ⟨.privateRow 12 6, 38550447936⟩, ⟨.privateRow 12 7, 202568325960⟩, ⟨.privateRow 12 8, 584280226530⟩, ⟨.privateRow 12 9, 1180607468040⟩, ⟨.privateRow 12 10, 926281596240⟩, ⟨.privateRow 13 4, 1946992320⟩, ⟨.privateRow 13 5, 67463283888⟩, ⟨.privateRow 13 6, 172525152800⟩, ⟨.privateRow 13 7, 793764431460⟩, ⟨.privateRow 14 3, 7909656300⟩, ⟨.privateRow 14 4, 106147587546⟩, ⟨.privateRow 14 5, 228149641720⟩, ⟨.privateRow 15 2, 22147037640⟩, ⟨.privateRow 15 3, 80045721756⟩, ⟨.privateRow 16 1, 23728968900⟩, ⟨.hall 8 17, 537301564800⟩, ⟨.hall 8 18, 16470735240960⟩, ⟨.hall 7 19, 82476675523242⟩, ⟨.hall 6 20, 190966221903600⟩, ⟨.hall 4 21, 38688261131520⟩, ⟨.hall 5 21, 397317855261600⟩, ⟨.hall 3 22, 52630440342480⟩, ⟨.hall 2 24, 1187071093143936⟩, ⟨.assumptionRow 17, 23775037440⟩]
  caps := #[0, 64583075620800, 17718006316560, 9268571357280, 2199744729600, 0, 397460229075, 143617338852, 31654880634, 0, 29603234910, 69849300300, 28076880804, 24382447200, 82886962678, 23775037440, 23775037440, 775451962560, 88803000000, 0, 0, 0] }

theorem case_48_27_17_checked :
    (Witness.linear .conditional case_48_27_17).check 48 27 17 = true := by
  change case_48_27_17.check 48 27 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_28_1_checked :
    (Witness.rising).check 48 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_28_2_checked :
    (Witness.rising).check 48 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_28_3_checked :
    (Witness.rising).check 48 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_28_4_checked :
    (Witness.rising).check 48 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_28_5_checked :
    (Witness.rising).check 48 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_28_6_checked :
    (Witness.rising).check 48 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_28_7_checked :
    (Witness.rising).check 48 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_28_8_checked :
    (Witness.rising).check 48 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_28_9_checked :
    (Witness.rising).check 48 28 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_28_10_checked :
    (Witness.linear .positive case_48_28_10).check 48 28 10 = true := by
  change case_48_28_10.check 48 28 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_28_11_checked :
    (Witness.linear .positive case_48_28_11).check 48 28 11 = true := by
  change case_48_28_11.check 48 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_28_12 : Certificate := {
  objectiveScale := 64974000000
  eta := 48665764220673600
  rows := #[⟨.count 2, 8639797889923200⟩, ⟨.count 3, 1554653897596800⟩, ⟨.count 4, 290841712761600⟩, ⟨.count 5, 57156393294000⟩, ⟨.count 6, 11993472691200⟩, ⟨.count 7, 2623572151200⟩, ⟨.count 8, 691931116800⟩, ⟨.count 9, 172982779200⟩, ⟨.count 10, 78628536000⟩, ⟨.count 11, 86491389600⟩, ⟨.path 12, 12761658000⟩, ⟨.path 13, 10441704000⟩, ⟨.privateRow 3 25, 127430647344000⟩, ⟨.privateRow 4 22, 24236809396800⟩, ⟨.privateRow 5 19, 4909827882960⟩, ⟨.privateRow 5 20, 8386060983300⟩, ⟨.privateRow 5 21, 16553490954000⟩, ⟨.privateRow 6 17, 1343019077400⟩, ⟨.privateRow 6 19, 19223912607900⟩, ⟨.privateRow 7 15, 2000186931600⟩, ⟨.privateRow 7 16, 303406303200⟩, ⟨.privateRow 7 17, 776363187600⟩, ⟨.privateRow 7 18, 5956579629000⟩, ⟨.privateRow 9 14, 241855552400⟩, ⟨.privateRow 10 11, 117942804000⟩, ⟨.privateRow 11 12, 3931426800⟩, ⟨.privateRow 12 3, 1372879200⟩, ⟨.privateRow 13 0, 900951975⟩, ⟨.hall 13 2, 254963280⟩, ⟨.hall 10 3, 57815100⟩, ⟨.hall 6 14, 147828590⟩, ⟨.hall 4 21, 243444583200⟩, ⟨.hall 5 21, 1248085566000⟩, ⟨.hall 3 23, 4523787980712⟩]
  caps := #[0, 251505166676400, 4616805538800, 5434542313200, 1338698306400, 230936706000, 34627893300, 56215504800, 0, 69467868400, 0, 31310470800, 14634740400, 21253127700, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_28_12_checked :
    (Witness.linear .positive case_48_28_12).check 48 28 12 = true := by
  change case_48_28_12.check 48 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_28_13 : Certificate := {
  objectiveScale := 3549000000
  eta := 3709597166074800
  rows := #[⟨.count 2, 830665776900960⟩, ⟨.count 3, 176309402789520⟩, ⟨.count 4, 41206145460480⟩, ⟨.count 5, 9309665465100⟩, ⟨.count 6, 2227359214080⟩, ⟨.count 7, 539438559660⟩, ⟨.count 8, 139209950880⟩, ⟨.count 9, 40156716600⟩, ⟨.count 10, 14602442400⟩, ⟨.count 11, 8031343320⟩, ⟨.path 13, 1092027300⟩, ⟨.hall 14 3, 15935205⟩, ⟨.hall 12 4, 1470942⟩, ⟨.hall 8 11, 13912976⟩]
  caps := #[0, 0, 0, 242608646280, 64148458920, 0, 0, 1126665540, 0, 0, 0, 0, 3549000000, 0, 34802487720, 0, 0, 0, 0, 0, 0] }

theorem case_48_28_13_checked :
    (Witness.linear .positive case_48_28_13).check 48 28 13 = true := by
  change case_48_28_13.check 48 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_28_14 : Certificate := {
  objectiveScale := 1360450000
  eta := 1377047432861100
  rows := #[⟨.count 2, 335461179133080⟩, ⟨.count 3, 86971416812280⟩, ⟨.count 4, 22900036919760⟩, ⟨.count 5, 5988928095150⟩, ⟨.count 6, 1583513191260⟩, ⟨.count 7, 426330474570⟩, ⟨.count 8, 118685406840⟩, ⟨.count 9, 37479602160⟩, ⟨.count 10, 12777137100⟩, ⟨.count 11, 4684950270⟩, ⟨.path 13, 247394875⟩, ⟨.hall 13 3, 3187041⟩, ⟨.hall 14 4, 3380195⟩, ⟨.hall 8 11, 18471530⟩, ⟨.hall 11 11, 9589965⟩]
  caps := #[0, 1539746426400, 0, 288713918220, 0, 25241316100, 8472829365, 0, 797001660, 0, 0, 988393770, 1855239750, 1607844875, 2699840234, 0, 0, 0, 0, 0, 0] }

theorem case_48_28_14_checked :
    (Witness.linear .positive case_48_28_14).check 48 28 14 = true := by
  change case_48_28_14.check 48 28 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_28_15 : Certificate := {
  objectiveScale := 1481530050000
  eta := 1765768251051604800
  rows := #[⟨.count 2, 382674233974032000⟩, ⟨.count 3, 94757429364998400⟩, ⟨.count 4, 23153399030361600⟩, ⟨.count 5, 5627562264324000⟩, ⟨.count 6, 1500683270486400⟩, ⟨.count 7, 415367690938200⟩, ⟨.count 8, 115437174652800⟩, ⟨.count 9, 37104806138400⟩, ⟨.count 10, 11243880648000⟩, ⟨.count 11, 6184134356400⟩, ⟨.path 11, 628710082000⟩, ⟨.privateRow 2 26, 21867099084230400⟩, ⟨.privateRow 4 21, 817336424104200⟩, ⟨.privateRow 4 22, 3912495669482400⟩, ⟨.privateRow 5 19, 541317893996880⟩, ⟨.privateRow 5 20, 1443737699954550⟩, ⟨.privateRow 5 21, 3059428691319000⟩, ⟨.privateRow 6 17, 256813357300500⟩, ⟨.privateRow 6 18, 562756226432400⟩, ⟨.privateRow 6 19, 1137794830822650⟩, ⟨.privateRow 6 20, 1664448309924400⟩, ⟨.privateRow 7 14, 8613615710700⟩, ⟨.privateRow 7 15, 99808562997000⟩, ⟨.privateRow 7 16, 227782282127400⟩, ⟨.privateRow 7 17, 444079743307200⟩, ⟨.privateRow 7 18, 644585575684050⟩, ⟨.privateRow 7 19, 749703589635000⟩, ⟨.privateRow 8 12, 7100302409200⟩, ⟨.privateRow 8 13, 39552692654475⟩, ⟨.privateRow 8 14, 91142361109800⟩, ⟨.privateRow 8 15, 183634434083100⟩, ⟨.privateRow 8 16, 266330052948960⟩, ⟨.privateRow 8 17, 314617835381850⟩, ⟨.privateRow 8 18, 274163289800400⟩, ⟨.privateRow 9 10, 3985331029680⟩, ⟨.privateRow 9 11, 16949108976800⟩, ⟨.privateRow 9 12, 38049604442850⟩, ⟨.privateRow 9 13, 78528690240000⟩, ⟨.privateRow 9 14, 119674451897000⟩, ⟨.privateRow 9 15, 144708743939760⟩, ⟨.privateRow 9 16, 14773209851400⟩, ⟨.privateRow 10 8, 1839907742400⟩, ⟨.privateRow 10 9, 7702058243880⟩, ⟨.privateRow 10 10, 17240616993600⟩, ⟨.privateRow 10 11, 35910143819550⟩, ⟨.privateRow 10 12, 57825671904000⟩, ⟨.privateRow 10 13, 18083908042200⟩, ⟨.privateRow 11 6, 796441545900⟩, ⟨.privateRow 11 7, 3679815484800⟩, ⟨.privateRow 11 8, 3710480613840⟩, ⟨.privateRow 11 9, 27922303609200⟩, ⟨.privateRow 11 10, 6535505626650⟩, ⟨.privateRow 12 4, 264279246000⟩, ⟨.privateRow 12 5, 1832336105600⟩, ⟨.privateRow 12 6, 4622484266400⟩, ⟨.privateRow 12 7, 5016020089080⟩, ⟨.privateRow 13 2, 73620647100⟩, ⟨.privateRow 13 3, 951405285600⟩, ⟨.privateRow 13 4, 1803705853950⟩, ⟨.privateRow 14 1, 410172176700⟩, ⟨.privateRow 14 2, 147241294200⟩, ⟨.hall 6 20, 65834705937000⟩, ⟨.hall 7 20, 73375244943000⟩, ⟨.hall 6 21, 96228878545800⟩, ⟨.hall 5 22, 4654681417386000⟩, ⟨.hall 4 23, 10835290518452400⟩, ⟨.hall 3 24, 20992415120861184⟩, ⟨.hall 2 25, 31328824649522400⟩, ⟨.assumptionRow 15, 1711204919424⟩]
  caps := #[0, 0, 2865225396121088, 0, 115425930772152, 0, 11149615827350, 0, 8109162316255, 0, 8905643479278, 0, 6057143951320, 1563963625224, 1301032742724, 16067155680576, 1481530050000, 0, 0, 0, 0] }

theorem case_48_28_15_checked :
    (Witness.linear .conditional case_48_28_15).check 48 28 15 = true := by
  change case_48_28_15.check 48 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_28_16 : Certificate := {
  objectiveScale := 549005032699200000
  eta := 784066852367084040955200
  rows := #[⟨.count 2, 162009914914056351542400⟩, ⟨.count 3, 36936222739839891468000⟩, ⟨.count 4, 8331253486146442051200⟩, ⟨.count 5, 1873033607496951900000⟩, ⟨.count 6, 427051662509305033200⟩, ⟨.count 7, 104889882019829306400⟩, ⟨.count 8, 27663265587647289600⟩, ⟨.count 9, 8644770496139778000⟩, ⟨.count 10, 3143552907687192000⟩, ⟨.count 11, 1728954099227955600⟩, ⟨.path 9, 531691632978105600⟩, ⟨.path 10, 127358937678772800⟩, ⟨.privateRow 2 26, 9170372542305076502400⟩, ⟨.privateRow 4 21, 307177511629500111600⟩, ⟨.privateRow 4 22, 1558363961437463980800⟩, ⟨.privateRow 5 19, 185055720420698847720⟩, ⟨.privateRow 5 20, 551608397407852334550⟩, ⟨.privateRow 5 21, 1268668096811268753600⟩, ⟨.privateRow 6 17, 79499870895981736200⟩, ⟨.privateRow 6 18, 204285532124334220560⟩, ⟨.privateRow 6 19, 459829750640501691450⟩, ⟨.privateRow 6 20, 747964753927116125400⟩, ⟨.privateRow 7 15, 29662736314645605600⟩, ⟨.privateRow 7 16, 77329530366659871300⟩, ⟨.privateRow 7 17, 173817518775717136320⟩, ⟨.privateRow 7 18, 287243082521139694950⟩, ⟨.privateRow 7 19, 387628764675321569400⟩, ⟨.privateRow 8 12, 96053005512664200⟩, ⟨.privateRow 8 13, 10049545701762491925⟩, ⟨.privateRow 8 14, 29351054113084103400⟩, ⟨.privateRow 8 15, 68581845936042238800⟩, ⟨.privateRow 8 16, 116646769894579404480⟩, ⟨.privateRow 8 17, 161080890244737863400⟩, ⟨.privateRow 8 18, 175296735060612165000⟩, ⟨.privateRow 9 11, 3287147299766730400⟩, ⟨.privateRow 9 12, 11046095633956383000⟩, ⟨.privateRow 9 13, 28157252473140991200⟩, ⟨.privateRow 9 14, 50523880899661369200⟩, ⟨.privateRow 9 15, 72577650965369069520⟩, ⟨.privateRow 9 16, 83470061790505189800⟩, ⟨.privateRow 9 17, 16905328970228899200⟩, ⟨.privateRow 10 9, 943065872306157600⟩, ⟨.privateRow 10 10, 4191403876916256000⟩, ⟨.privateRow 10 11, 11866912226519149800⟩, ⟨.privateRow 10 12, 23374561263588334800⟩, ⟨.privateRow 10 13, 35810306873403262200⟩, ⟨.privateRow 10 14, 21407595301349777520⟩, ⟨.privateRow 11 7, 228622029649977600⟩, ⟨.privateRow 11 8, 1524623160228288120⟩, ⟨.privateRow 11 9, 5169398114863382400⟩, ⟨.privateRow 11 10, 11395379290366071000⟩, ⟨.privateRow 11 11, 15785126386457828400⟩, ⟨.privateRow 12 5, 16008834252110700⟩, ⟨.privateRow 12 6, 523925484614532000⟩, ⟨.privateRow 12 7, 2247640328996342280⟩, ⟨.privateRow 12 8, 5869905892440590000⟩, ⟨.privateRow 12 9, 2593431148841933400⟩, ⟨.privateRow 13 4, 120066256890830250⟩, ⟨.privateRow 13 5, 995458420767610800⟩, ⟨.privateRow 13 6, 2247640328996342280⟩, ⟨.privateRow 14 3, 356768306189895600⟩, ⟨.privateRow 14 4, 535152459284843400⟩, ⟨.privateRow 15 1, 96053005512664200⟩, ⟨.privateRow 15 2, 104057422638719550⟩, ⟨.hall 7 20, 219234124153690846200⟩, ⟨.hall 6 21, 944008938178463757600⟩, ⟨.hall 5 22, 2411327179042815033000⟩, ⟨.hall 4 23, 5034714336951806707200⟩, ⟨.hall 3 24, 9149993936655509665728⟩, ⟨.hall 2 25, 13285283298467610830400⟩, ⟨.assumptionRow 16, 454299703826328360⟩]
  caps := #[0, 0, 27587951665663989600, 0, 0, 0, 8034293510404251090, 0, 0, 1063993658006879600, 100165493356629120, 0, 5045650832372730580, 454299703826328360, 481612704203113560, 454299703826328360, 5584755655864871640, 549005032699200000, 0, 0, 0] }

theorem case_48_28_16_checked :
    (Witness.linear .conditional case_48_28_16).check 48 28 16 = true := by
  change case_48_28_16.check 48 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_28_17 : Certificate := {
  objectiveScale := 13852999660500000
  eta := 21667944353164430761440
  rows := #[⟨.count 2, 4467617392405037270400⟩, ⟨.count 3, 995416506728841637440⟩, ⟨.count 4, 217617689289492011520⟩, ⟨.count 5, 46681760679154801200⟩, ⟨.count 6, 9797406562291748400⟩, ⟨.count 7, 2074744919073546720⟩, ⟨.count 8, 425588701348419840⟩, ⟨.count 9, 106397175337104960⟩, ⟨.count 10, 24181176212978400⟩, ⟨.count 11, 26599293834276240⟩, ⟨.path 9, 16762031304480000⟩, ⟨.path 10, 3706357465530720⟩, ⟨.privateRow 2 26, 270408421119252255840⟩, ⟨.privateRow 4 21, 7780293446525800200⟩, ⟨.privateRow 4 22, 42954904065263430240⟩, ⟨.privateRow 5 19, 4587491543284842192⟩, ⟨.privateRow 5 20, 14681701892610722970⟩, ⟨.privateRow 5 21, 35904613460633877960⟩, ⟨.privateRow 6 17, 1892244208599484740⟩, ⟨.privateRow 6 18, 5217599259447919344⟩, ⟨.privateRow 6 19, 12654983476293508350⟩, ⟨.privateRow 6 20, 22265086677835561560⟩, ⟨.privateRow 7 14, 3087418034335635⟩, ⟨.privateRow 7 15, 663353817662970720⟩, ⟨.privateRow 7 16, 1873033607496951900⟩, ⟨.privateRow 7 17, 4605604395752944584⟩, ⟨.privateRow 7 18, 8368961151739127940⟩, ⟨.privateRow 7 19, 12470424487129889280⟩, ⟨.privateRow 8 12, 5418374669945160⟩, ⟨.privateRow 8 13, 205590375260760105⟩, ⟨.privateRow 8 14, 664982345856906000⟩, ⟨.privateRow 8 15, 1731909576320652960⟩, ⟨.privateRow 8 16, 3289446004172161680⟩, ⟨.privateRow 8 17, 5095981377083422980⟩, ⟨.privateRow 8 18, 6354275749299324000⟩, ⟨.privateRow 9 11, 61408246259378480⟩, ⟨.privateRow 9 12, 228310605410871060⟩, ⟨.privateRow 9 13, 665826767883390960⟩, ⟨.privateRow 9 14, 1360504621671684720⟩, ⟨.privateRow 9 15, 2220745487452796304⟩, ⟨.privateRow 9 16, 2949566138511965280⟩, ⟨.privateRow 9 17, 2898337868905211040⟩, ⟨.privateRow 10 9, 13541458679267904⟩, ⟨.privateRow 10 10, 77111084145831120⟩, ⟨.privateRow 10 11, 256622732560233270⟩, ⟨.privateRow 10 12, 589675254222201840⟩, ⟨.privateRow 10 13, 784679168111149080⟩, ⟨.privateRow 10 14, 1996881531667756272⟩, ⟨.privateRow 10 15, 402616583946090360⟩, ⟨.privateRow 11 7, 1318973247980640⟩, ⟨.privateRow 11 8, 22004870353810344⟩, ⟨.privateRow 11 9, 99948861680310720⟩, ⟨.privateRow 11 10, 263574820721464560⟩, ⟨.privateRow 11 11, 521622515451391200⟩, ⟨.privateRow 11 12, 666594424271104560⟩, ⟨.privateRow 12 6, 3492836564096880⟩, ⟨.privateRow 12 7, 34874629693828848⟩, ⟨.privateRow 12 8, 121502947144224800⟩, ⟨.privateRow 12 9, 275967673530615990⟩, ⟨.privateRow 12 10, 149462698687837920⟩, ⟨.privateRow 13 5, 8060392070992800⟩, ⟨.privateRow 13 6, 52311944540743272⟩, ⟨.privateRow 13 7, 140385161903124600⟩, ⟨.privateRow 14 4, 16466229516456720⟩, ⟨.privateRow 14 5, 47752065597724488⟩, ⟨.privateRow 15 2, 1600883425211070⟩, ⟨.privateRow 15 3, 15717764538435960⟩, ⟨.privateRow 16 1, 4802650275633210⟩, ⟨.hall 7 19, 64218295114181208⟩, ⟨.hall 8 19, 273086083365236064⟩, ⟨.hall 7 20, 10351769622679124640⟩, ⟨.hall 6 21, 35359730956634764680⟩, ⟨.hall 5 22, 79807518928130994000⟩, ⟨.hall 4 23, 155375341717285609920⟩, ⟨.hall 3 24, 270408421119252255840⟩, ⟨.hall 2 25, 383455419914926275840⟩, ⟨.assumptionRow 17, 5896314051189408⟩]
  caps := #[0, 36792312558366324960, 0, 243527528033475840, 395167263180233544, 221841815350045968, 0, 8590904834226957, 37796131061508435, 0, 11728101023708454, 0, 25329296133787954, 5896314051189408, 7544928993145236, 147193438705813500, 5896314051189408, 132633682553810592, 13852999660500000, 0, 0] }

theorem case_48_28_17_checked :
    (Witness.linear .conditional case_48_28_17).check 48 28 17 = true := by
  change case_48_28_17.check 48 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_28_18 : Certificate := {
  objectiveScale := 7534800000
  eta := 6755098615705440
  rows := #[⟨.count 2, 1674438706100160⟩, ⟨.count 3, 447281572177440⟩, ⟨.count 4, 119634890094720⟩, ⟨.count 5, 32045059846800⟩, ⟨.count 6, 8657788098960⟩, ⟨.count 7, 2361214936080⟩, ⟨.count 8, 622738005120⟩, ⟨.count 9, 155684501280⟩, ⟨.count 10, 47177121600⟩, ⟨.path 11, 1424230080⟩, ⟨.path 12, 1406878200⟩, ⟨.privateRow 4 21, 899510451840⟩, ⟨.privateRow 5 19, 517218509808⟩, ⟨.privateRow 6 17, 199891211520⟩, ⟨.privateRow 7 15, 63103411800⟩, ⟨.privateRow 7 16, 750930600420⟩, ⟨.privateRow 8 13, 16757706735⟩, ⟨.privateRow 8 14, 232291160640⟩, ⟨.privateRow 8 15, 861310088100⟩, ⟨.privateRow 9 11, 3203384800⟩, ⟨.privateRow 9 12, 69553492470⟩, ⟨.privateRow 9 14, 1377135125520⟩, ⟨.privateRow 10 10, 19132943760⟩, ⟨.privateRow 10 11, 100546240410⟩, ⟨.privateRow 10 12, 111540194640⟩, ⟨.privateRow 10 13, 952977856320⟩, ⟨.privateRow 10 16, 2253493841760⟩, ⟨.privateRow 11 8, 4010055336⟩, ⟨.privateRow 11 10, 181042204140⟩, ⟨.privateRow 11 11, 123671454480⟩, ⟨.privateRow 11 12, 693503687520⟩, ⟨.privateRow 11 14, 274217019300⟩, ⟨.privateRow 11 15, 960054424560⟩, ⟨.privateRow 12 6, 786285360⟩, ⟨.privateRow 12 7, 8649138960⟩, ⟨.privateRow 12 11, 216228474000⟩, ⟨.privateRow 12 13, 176586587100⟩, ⟨.privateRow 12 14, 1010027227440⟩, ⟨.privateRow 13 9, 135915040800⟩, ⟨.privateRow 13 12, 391373537940⟩, ⟨.privateRow 15 3, 1703618280⟩, ⟨.privateRow 15 9, 14991840864⟩, ⟨.privateRow 15 10, 14054850810⟩, ⟨.privateRow 16 6, 8031343320⟩, ⟨.privateRow 17 11, 224877612960⟩, ⟨.hall 14 4, 131047560⟩, ⟨.hall 13 5, 537562440⟩, ⟨.hall 15 5, 43682520⟩, ⟨.hall 15 7, 65523780⟩, ⟨.hall 14 10, 421224300⟩, ⟨.hall 7 15, 2484411930⟩, ⟨.hall 8 15, 4752117216⟩, ⟨.hall 6 17, 11005630272⟩, ⟨.hall 9 17, 221463479160⟩, ⟨.hall 5 19, 56449550430⟩]
  caps := #[0, 0, 13193659839360, 515974127760, 142549465968, 259144677792, 23420222280, 0, 25914553245, 6230750400, 32140374420, 11830489440, 1406878200, 0, 3473195040, 0, 0, 263718000000, 67813200000, 7534800000, 0] }

theorem case_48_28_18_checked :
    (Witness.linear .negative case_48_28_18).check 48 28 18 = true := by
  change case_48_28_18.check 48 28 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_29_1_checked :
    (Witness.rising).check 48 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_29_2_checked :
    (Witness.rising).check 48 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_29_3_checked :
    (Witness.rising).check 48 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_29_4_checked :
    (Witness.rising).check 48 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_29_5_checked :
    (Witness.rising).check 48 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_29_6_checked :
    (Witness.rising).check 48 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_29_7_checked :
    (Witness.rising).check 48 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_29_8_checked :
    (Witness.rising).check 48 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_29_9_checked :
    (Witness.rising).check 48 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_29_10_checked :
    (Witness.linear .positive case_48_29_10).check 48 29 10 = true := by
  change case_48_29_10.check 48 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_29_11_checked :
    (Witness.linear .positive case_48_29_11).check 48 29 11 = true := by
  change case_48_29_11.check 48 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_29_12_checked :
    (Witness.linear .positive case_48_29_12).check 48 29 12 = true := by
  change case_48_29_12.check 48 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_29_13 : Certificate := {
  objectiveScale := 40222000000
  eta := 126516787558761600
  rows := #[⟨.count 2, 25239460144298400⟩, ⟨.count 3, 5431276233583200⟩, ⟨.count 4, 1127600602128000⟩, ⟨.count 5, 247445687689200⟩, ⟨.count 6, 54366457602600⟩, ⟨.count 7, 12287955279600⟩, ⟨.count 8, 2891283595200⟩, ⟨.count 9, 788531889600⟩, ⟨.count 10, 197132972400⟩, ⟨.path 11, 35753094468⟩, ⟨.hall 10 7, 229086900⟩, ⟨.hall 9 9, 85092525⟩, ⟨.hall 10 13, 38750400⟩]
  caps := #[0, 303102775209780, 0, 0, 0, 0, 0, 100522482060, 111976340112, 0, 26323405472, 75975094468, 40222000000, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_29_13_checked :
    (Witness.linear .positive case_48_29_13).check 48 29 13 = true := by
  change case_48_29_13.check 48 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_29_14 : Certificate := {
  objectiveScale := 13000000
  eta := 35043428019600
  rows := #[⟨.count 2, 8141402469200⟩, ⟨.count 3, 1873980108000⟩, ⟨.count 4, 417183666900⟩, ⟨.count 5, 101135434400⟩, ⟨.count 6, 24221511600⟩, ⟨.count 7, 5663126700⟩, ⟨.count 8, 1487285800⟩, ⟨.count 9, 374421600⟩, ⟨.count 10, 93605400⟩, ⟨.path 10, 1927341⟩, ⟨.path 11, 7221396⟩]
  caps := #[0, 143716716585, 13949098995, 0, 0, 162948604, 95161053, 51479340, 12012065, 25196216, 16650317, 33221396, 13000000, 13000000, 0, 0, 0, 0, 0, 0] }

theorem case_48_29_14_checked :
    (Witness.linear .positive case_48_29_14).check 48 29 14 = true := by
  change case_48_29_14.check 48 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_29_15 : Certificate := {
  objectiveScale := 1044323280000
  eta := 3690072970463880000
  rows := #[⟨.count 2, 721614269779603200⟩, ⟨.count 3, 154355993535744000⟩, ⟨.count 4, 32559467386446000⟩, ⟨.count 5, 7315830943621200⟩, ⟨.count 6, 1619359753611600⟩, ⟨.count 7, 389600464453200⟩, ⟨.count 8, 98946149702400⟩, ⟨.count 9, 30358477749600⟩, ⟨.count 10, 10119492583200⟩, ⟨.path 10, 1384987696092⟩, ⟨.privateRow 2 27, 16400324313172800⟩, ⟨.privateRow 3 25, 14792449380508800⟩, ⟨.privateRow 4 22, 2019892884159150⟩, ⟨.privateRow 4 23, 5647660700982300⟩, ⟨.privateRow 4 24, 10431088625657700⟩, ⟨.privateRow 5 19, 96472495959840⟩, ⟨.privateRow 5 20, 1189827450171360⟩, ⟨.privateRow 5 21, 2182690221091380⟩, ⟨.privateRow 5 22, 4089361912075440⟩, ⟨.privateRow 5 23, 4936176043278480⟩, ⟨.privateRow 6 17, 141099228784800⟩, ⟨.privateRow 6 18, 468963522027000⟩, ⟨.privateRow 6 19, 886628177154720⟩, ⟨.privateRow 6 20, 1544708417452200⟩, ⟨.privateRow 6 21, 1998358844882400⟩, ⟨.privateRow 6 22, 1863412198748100⟩, ⟨.privateRow 7 15, 88123914578700⟩, ⟨.privateRow 7 16, 196125403874400⟩, ⟨.privateRow 7 17, 349845315019200⟩, ⟨.privateRow 7 18, 622300605806880⟩, ⟨.privateRow 7 19, 559222435371600⟩, ⟨.privateRow 7 20, 1250962035523200⟩, ⟨.privateRow 7 21, 206726777056800⟩, ⟨.privateRow 8 12, 4328894049480⟩, ⟨.privateRow 8 13, 38650839727500⟩, ⟨.privateRow 8 14, 89283439770525⟩, ⟨.privateRow 8 15, 147977500671000⟩, ⟨.privateRow 8 16, 259218298439100⟩, ⟨.privateRow 8 17, 341364216473280⟩, ⟨.privateRow 8 18, 271328894887050⟩, ⟨.privateRow 9 10, 3679815484800⟩, ⟨.privateRow 9 11, 17315576197920⟩, ⟨.privateRow 9 12, 40727834347200⟩, ⟨.privateRow 9 13, 63246828645000⟩, ⟨.privateRow 9 14, 132838418512800⟩, ⟨.privateRow 9 15, 131178607560000⟩, ⟨.privateRow 10 8, 2108227621500⟩, ⟨.privateRow 10 9, 8555571002160⟩, ⟨.privateRow 10 10, 19733010537240⟩, ⟨.privateRow 10 11, 35418224041200⟩, ⟨.privateRow 10 12, 57554614066950⟩, ⟨.privateRow 11 6, 1037896675200⟩, ⟨.privateRow 11 7, 4591251264600⟩, ⟨.privateRow 11 8, 10732795164000⟩, ⟨.privateRow 11 9, 19564352327520⟩, ⟨.privateRow 12 4, 441723882600⟩, ⟨.privateRow 12 5, 2616364535400⟩, ⟨.privateRow 12 6, 6312970488825⟩, ⟨.privateRow 13 2, 176689553040⟩, ⟨.privateRow 13 3, 1703792118600⟩, ⟨.privateRow 13 4, 407745122400⟩, ⟨.privateRow 14 1, 382827364920⟩, ⟨.hall 6 22, 97371308034000⟩, ⟨.hall 5 23, 1597825714334850⟩, ⟨.hall 4 24, 4939391793143808⟩, ⟨.hall 3 25, 11094337035381600⟩, ⟨.hall 2 26, 19842367687542400⟩, ⟨.assumptionRow 15, 1261596035700⟩]
  caps := #[0, 8142035309307900, 1386270092106900, 334042843902768, 0, 4113749615976, 0, 2601949289940, 17729466820065, 0, 0, 2782867550400, 23321587194675, 731527376580, 909759810960, 12314606604300, 1044323280000, 0, 0, 0] }

theorem case_48_29_15_checked :
    (Witness.linear .conditional case_48_29_15).check 48 29 15 = true := by
  change case_48_29_15.check 48 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_29_16 : Certificate := {
  objectiveScale := 2143542302131230000000
  eta := 5344297496801034842718648000
  rows := #[⟨.count 2, 1093365978181516828492704000⟩, ⟨.count 3, 214570300992011669688984000⟩, ⟨.count 4, 46157564748281580107514000⟩, ⟨.count 5, 9702791388527659482060000⟩, ⟨.count 6, 2079169583255927031870000⟩, ⟨.count 7, 447821141008968899172000⟩, ⟨.count 8, 127948897431133971192000⟩, ⟨.count 9, 34895153844854719416000⟩, ⟨.count 10, 17447576922427359708000⟩, ⟨.path 8, 2984891005629860286960⟩, ⟨.path 9, 3071512310688912714624⟩, ⟨.privateRow 2 27, 117819609717835865139300000⟩, ⟨.privateRow 3 24, 12012979814367578406360000⟩, ⟨.privateRow 3 25, 37147829887505896302744000⟩, ⟨.privateRow 4 22, 7225114301814346435748250⟩, ⟨.privateRow 4 23, 14034394686977507465122500⟩, ⟨.privateRow 4 24, 25885661311536291546781500⟩, ⟨.privateRow 5 19, 452796931464624109162800⟩, ⟨.privateRow 5 20, 2650248162123554989956960⟩, ⟨.privateRow 5 21, 5253368480359975633858200⟩, ⟨.privateRow 5 22, 10063180782958686834250800⟩, ⟨.privateRow 5 23, 12974018199516984678868800⟩, ⟨.privateRow 6 17, 298438627256462995731000⟩, ⟨.privateRow 6 18, 965328735083108979082500⟩, ⟨.privateRow 6 19, 1946498762229120259360200⟩, ⟨.privateRow 6 20, 3777158076248267441230500⟩, ⟨.privateRow 6 21, 5333234994510441402384000⟩, ⟨.privateRow 6 22, 5613757874791002986049000⟩, ⟨.privateRow 7 15, 135374503085619424877250⟩, ⟨.privateRow 7 16, 375360285831132823650000⟩, ⟨.privateRow 7 17, 741037364288650916487000⟩, ⟨.privateRow 7 18, 1466842716978357312594000⟩, ⟨.privateRow 7 19, 2129435221532443949124000⟩, ⟨.privateRow 7 20, 2491957097587323534168000⟩, ⟨.privateRow 7 21, 1868967823190492650626000⟩, ⟨.privateRow 8 13, 52127328583054580856000⟩, ⟨.privateRow 8 14, 152605716206925413557125⟩, ⟨.privateRow 8 15, 301593829659101503524000⟩, ⟨.privateRow 8 16, 600648990718378920318000⟩, ⟨.privateRow 8 17, 830068472084481638108100⟩, ⟨.privateRow 8 18, 1257497757565363560621375⟩, ⟨.privateRow 8 19, 644187157205362007737500⟩, ⟨.privateRow 9 11, 18223024785646353472800⟩, ⟨.privateRow 9 12, 63328242162884490792000⟩, ⟨.privateRow 9 13, 132310791661740811119000⟩, ⟨.privateRow 9 14, 267252567145117493940000⟩, ⟨.privateRow 9 15, 419711155967280375198000⟩, ⟨.privateRow 9 16, 504816558955564940884800⟩, ⟨.privateRow 10 9, 5868730419361930083600⟩, ⟨.privateRow 10 10, 26171365383641039562000⟩, ⟨.privateRow 10 11, 61454243160105255860400⟩, ⟨.privateRow 10 12, 66300792305223966890400⟩, ⟨.privateRow 10 13, 346209776360737180491600⟩, ⟨.privateRow 11 7, 1615516381706237010000⟩, ⟨.privateRow 11 8, 10750527194626959012000⟩, ⟨.privateRow 11 9, 29660880768126511503600⟩, ⟨.privateRow 11 10, 70436514242391933636000⟩, ⟨.privateRow 11 11, 59370227027704210117500⟩, ⟨.privateRow 12 5, 205046309985791620500⟩, ⟨.privateRow 12 6, 4220536547207544188625⟩, ⟨.privateRow 12 7, 14539647435356133090000⟩, ⟨.privateRow 12 8, 34386266184617254757850⟩, ⟨.privateRow 13 4, 1406031839902571112000⟩, ⟨.privateRow 13 5, 7235205509498647180500⟩, ⟨.privateRow 13 6, 6646695970448517984000⟩, ⟨.privateRow 14 3, 3046402319788904076000⟩, ⟨.hall 6 22, 1133857698197952754026000⟩, ⟨.hall 5 23, 5405840916465410282862000⟩, ⟨.hall 4 24, 14071819739476114151696160⟩, ⟨.hall 3 25, 29620169755307514330948000⟩, ⟨.hall 2 26, 54109746685228323249160000⟩, ⟨.assumptionRow 16, 1931837490203541200280⟩]
  caps := #[0, 0, 3843148635482347423552320, 880520470225844359111200, 108468629291842640176356, 193960998527099678338464, 38842131815284913962704, 16337373428339833874004, 15235464691111634933964, 8148849510337086174624, 0, 5583807658682934801120, 27523673595343984090725, 1931837490203541200280, 61532439583287003130800, 139938869891458674396360, 23790670135371218799720, 2143542302131230000000, 0, 0] }

theorem case_48_29_16_checked :
    (Witness.linear .conditional case_48_29_16).check 48 29 16 = true := by
  change case_48_29_16.check 48 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_29_17 : Certificate := {
  objectiveScale := 7255066253367240000000
  eta := 20189568321248353850270448000
  rows := #[⟨.count 2, 3996441161628992545525056000⟩, ⟨.count 3, 745174378638924248222208000⟩, ⟨.count 4, 148036874327822004669144000⟩, ⟨.count 5, 28276706332280607633432000⟩, ⟨.count 6, 5227626380757759394416000⟩, ⟨.count 7, 959616730733504783940000⟩, ⟨.count 8, 213248162385223285320000⟩, ⟨.count 9, 69790307689709438832000⟩, ⟨.path 8, 28471268053700205814080⟩, ⟨.path 9, 4882603234919825390976⟩, ⟨.privateRow 2 27, 443001732539062852923768000⟩, ⟨.privateRow 3 24, 42877097183588895235008000⟩, ⟨.privateRow 3 25, 136947969883790393832504000⟩, ⟨.privateRow 4 22, 24742118040745531679253000⟩, ⟨.privateRow 4 23, 50593126525894224442170000⟩, ⟨.privateRow 4 24, 98136804329679755904264000⟩, ⟨.privateRow 5 19, 1404594562910670705974400⟩, ⟨.privateRow 5 20, 8704789988564814506762400⟩, ⟨.privateRow 5 21, 18379859115982394961730800⟩, ⟨.privateRow 5 22, 37720756617114196195970400⟩, ⟨.privateRow 5 23, 52256462192498966067666000⟩, ⟨.privateRow 6 17, 865613459151447172452000⟩, ⟨.privateRow 6 18, 3009845491951437227088000⟩, ⟨.privateRow 6 19, 6566215560073003845410400⟩, ⟨.privateRow 6 20, 13856180151269856576676500⟩, ⟨.privateRow 6 21, 21497953437030331246986000⟩, ⟨.privateRow 6 22, 25029241459385635888416000⟩, ⟨.privateRow 7 15, 356429071415301776892000⟩, ⟨.privateRow 7 16, 1099316037112395956568000⟩, ⟨.privateRow 7 17, 2391425821034289699660000⟩, ⟨.privateRow 7 18, 5229454222149632736861600⟩, ⟨.privateRow 7 19, 8469760049593100557299000⟩, ⟨.privateRow 7 20, 11204667732183589191528000⟩, ⟨.privateRow 7 21, 10121671707498633792510000⟩, ⟨.privateRow 8 13, 119655913338375287874000⟩, ⟨.privateRow 8 14, 412501914113916292540875⟩, ⟨.privateRow 8 15, 919251899996301804933000⟩, ⟨.privateRow 8 16, 2060510369047219994404500⟩, ⟨.privateRow 8 17, 3521793401791962557059800⟩, ⟨.privateRow 8 18, 4884715719636520879361250⟩, ⟨.privateRow 8 19, 5265452542895138286693000⟩, ⟨.privateRow 8 20, 2209784082716876294128500⟩, ⟨.privateRow 9 11, 33731982050026228768800⟩, ⟨.privateRow 9 12, 152504746433068773744000⟩, ⟨.privateRow 9 13, 372699629259628878207000⟩, ⟨.privateRow 9 14, 867947715474402306744000⟩, ⟨.privateRow 9 15, 1563173650938954930876000⟩, ⟨.privateRow 9 16, 2310059184529382425339200⟩, ⟨.privateRow 9 17, 2194517452909752354384000⟩, ⟨.privateRow 10 9, 6979030768970943883200⟩, ⟨.privateRow 10 10, 53389585382627720706480⟩, ⟨.privateRow 10 11, 155089572643798752960000⟩, ⟨.privateRow 10 12, 393879049023797645408100⟩, ⟨.privateRow 10 13, 756227834037780133629600⟩, ⟨.privateRow 10 14, 1196903776878516875968800⟩, ⟨.privateRow 10 15, 357326375371312326819840⟩, ⟨.privateRow 11 8, 16566386168769412248000⟩, ⟨.privateRow 11 9, 63974448715566985596000⟩, ⟨.privateRow 11 10, 189123117751743479304000⟩, ⟨.privateRow 11 11, 402748233959364886593000⟩, ⟨.privateRow 11 12, 425942433439575860808000⟩, ⟨.privateRow 12 6, 2221335024846075888750⟩, ⟨.privateRow 12 7, 24232745725593555150000⟩, ⟨.privateRow 12 8, 53845161002268879543300⟩, ⟨.privateRow 12 9, 309802191465199383951000⟩, ⟨.privateRow 13 5, 4569603479683356114000⟩, ⟨.privateRow 13 6, 43203523807915366896000⟩, ⟨.privateRow 13 7, 83166783330237081274800⟩, ⟨.privateRow 14 4, 11550942129199594621500⟩, ⟨.privateRow 14 5, 28802349205276911264000⟩, ⟨.privateRow 15 3, 9240753703359675697200⟩, ⟨.hall 6 22, 8063562035931682227948000⟩, ⟨.hall 5 23, 26289944286058277358534000⟩, ⟨.hall 4 24, 60611951691076784833074240⟩, ⟨.hall 3 25, 119248372405816861150944000⟩, ⟨.hall 2 26, 208758893663009918083856000⟩, ⟨.assumptionRow 17, 4014426023431367544000⟩]
  caps := #[0, 0, 9765898717399329855430080, 0, 136810023186497590984824, 47192131799141286345696, 0, 39480426950607076931640, 16569486825203818557051, 0, 60264761527060406496180, 14475681934555611924000, 6581302815512154287250, 28989952027559436513600, 4014426023431367544000, 137557168607335053376800, 423406194187694189472000, 75791302763608272456000, 7255066253367240000000, 0] }

theorem case_48_29_17_checked :
    (Witness.linear .conditional case_48_29_17).check 48 29 17 = true := by
  change case_48_29_17.check 48 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_29_18 : Certificate := {
  objectiveScale := 73832443685000000
  eta := 222356253050969349312000
  rows := #[⟨.count 2, 49412500677993188736000⟩, ⟨.count 3, 10710254302966554336000⟩, ⟨.count 4, 2239201397412255276000⟩, ⟨.count 5, 501549519349834956000⟩, ⟨.count 6, 108321156035059968000⟩, ⟨.count 7, 22783897002566700000⟩, ⟨.count 8, 4252994107145784000⟩, ⟨.count 9, 497103207328728000⟩, ⟨.path 9, 56132690432442624⟩, ⟨.path 10, 79742353009999680⟩, ⟨.privateRow 4 22, 222142995775025325000⟩, ⟨.privateRow 4 23, 621013085966626353000⟩, ⟨.privateRow 5 20, 104733017741398606560⟩, ⟨.privateRow 5 21, 230633794724648515200⟩, ⟨.privateRow 6 17, 3788016617297484000⟩, ⟨.privateRow 6 18, 35636908105284486000⟩, ⟨.privateRow 6 19, 85979917602828849600⟩, ⟨.privateRow 6 20, 182509864465322394000⟩, ⟨.privateRow 7 15, 2506228670282337000⟩, ⟨.privateRow 7 16, 12201009333619392000⟩, ⟨.privateRow 7 17, 30682314630123156000⟩, ⟨.privateRow 7 18, 71059719908576599200⟩, ⟨.privateRow 7 19, 116262971561668932000⟩, ⟨.privateRow 7 20, 83497557777025392000⟩, ⟨.privateRow 8 13, 1122317889385693000⟩, ⟨.privateRow 8 14, 4404886753829562000⟩, ⟨.privateRow 8 15, 11142410581731429000⟩, ⟨.privateRow 8 16, 27555857652548725500⟩, ⟨.privateRow 8 18, 130209971369668690500⟩, ⟨.privateRow 8 19, 117995271032181543000⟩, ⟨.privateRow 9 11, 414252672773940000⟩, ⟨.privateRow 9 12, 1638599461194696000⟩, ⟨.privateRow 9 13, 4239185684719986000⟩, ⟨.privateRow 9 14, 10928380034131560000⟩, ⟨.privateRow 9 15, 21743662513156584000⟩, ⟨.privateRow 9 16, 12107224782939686400⟩, ⟨.privateRow 9 17, 57097826730674730000⟩, ⟨.privateRow 9 18, 57093223923199464000⟩, ⟨.privateRow 10 9, 135573601998744000⟩, ⟨.privateRow 10 11, 2921862185298856800⟩, ⟨.privateRow 10 12, 3989253238813042200⟩, ⟨.privateRow 10 13, 9771628761204710400⟩, ⟨.privateRow 10 14, 17017499797553455200⟩, ⟨.privateRow 10 15, 7237822698706279680⟩, ⟨.privateRow 11 7, 23014037376330000⟩, ⟨.privateRow 11 8, 180764802664992000⟩, ⟨.privateRow 11 9, 149130962198618400⟩, ⟨.privateRow 11 10, 785545809112064000⟩, ⟨.privateRow 11 13, 5827154263686756000⟩, ⟨.privateRow 11 15, 35239094030636496000⟩, ⟨.privateRow 12 6, 37973161670944500⟩, ⟨.privateRow 12 11, 4252994107145784000⟩, ⟨.privateRow 13 6, 82850534554788000⟩, ⟨.privateRow 14 13, 1034316594084774000⟩, ⟨.privateRow 15 9, 394920881377822800⟩, ⟨.privateRow 15 10, 157968352551129120⟩, ⟨.privateRow 15 12, 526561175170430400⟩, ⟨.hall 12 4, 711142043297400⟩, ⟨.hall 13 4, 1549924966161000⟩, ⟨.hall 12 5, 6564388091976000⟩, ⟨.hall 13 5, 2001986414624625⟩, ⟨.hall 11 6, 3424212057593250⟩, ⟨.hall 9 12, 1243053983556000⟩, ⟨.hall 6 17, 21477761981676000⟩, ⟨.hall 7 17, 14050675450812000⟩, ⟨.hall 5 19, 172578120899484300⟩, ⟨.hall 4 21, 1421715172960162080⟩, ⟨.hall 3 23, 10201110151282530480⟩]
  caps := #[0, 0, 0, 0, 18786167149969339120, 0, 1827477786920146504, 29995354413282544, 11970466311067264, 278310111967311424, 212043708024530200, 0, 657612513239181500, 54703234099800, 851035463255727750, 1033654211590000000, 15357148286480000000, 3986951958990000000, 738324436850000000, 73832443685000000] }

theorem case_48_29_18_checked :
    (Witness.linear .negative case_48_29_18).check 48 29 18 = true := by
  change case_48_29_18.check 48 29 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_30_1_checked :
    (Witness.rising).check 48 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_30_2_checked :
    (Witness.rising).check 48 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_30_3_checked :
    (Witness.rising).check 48 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_30_4_checked :
    (Witness.rising).check 48 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_30_5_checked :
    (Witness.rising).check 48 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_30_6_checked :
    (Witness.rising).check 48 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_30_7_checked :
    (Witness.rising).check 48 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_30_8_checked :
    (Witness.rising).check 48 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_30_9_checked :
    (Witness.rising).check 48 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_30_10_checked :
    (Witness.linear .positive case_48_30_10).check 48 30 10 = true := by
  change case_48_30_10.check 48 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_30_11_checked :
    (Witness.linear .positive case_48_30_11).check 48 30 11 = true := by
  change case_48_30_11.check 48 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_30_12_checked :
    (Witness.linear .positive case_48_30_12).check 48 30 12 = true := by
  change case_48_30_12.check 48 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_48_30_13_checked :
    (Witness.linear .positive case_48_30_13).check 48 30 13 = true := by
  change case_48_30_13.check 48 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_30_14 : Certificate := {
  objectiveScale := 6156734330500
  eta := 51278211847100878640
  rows := #[⟨.count 2, 10010355512491574240⟩, ⟨.count 3, 1895586774405999675⟩, ⟨.count 4, 361300910881318408⟩, ⟨.count 5, 71029012624112400⟩, ⟨.count 6, 13386236994544260⟩, ⟨.count 7, 2709119391753005⟩, ⟨.count 8, 579490778984600⟩, ⟨.count 9, 104308340217228⟩, ⟨.path 8, 6162979223982⟩, ⟨.path 9, 28084409440920⟩]
  caps := #[0, 85527001119572740, 7445792197431960, 241377740933273, 570897615820062, 2707717584960, 39282119592450, 31096313661499, 0, 9970349850692, 30783671652500, 12313468661000, 6156734330500, 6156734330500, 0, 0, 0, 0, 0] }

theorem case_48_30_14_checked :
    (Witness.linear .positive case_48_30_14).check 48 30 14 = true := by
  change case_48_30_14.check 48 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_30_15 : Certificate := {
  objectiveScale := 4897589697000000
  eta := 27407699004054618849600
  rows := #[⟨.count 2, 5244563239613569872000⟩, ⟨.count 3, 1019776185480416364000⟩, ⟨.count 4, 198127944607623750720⟩, ⟨.count 5, 42317243070956053200⟩, ⟨.count 6, 8644884460901488800⟩, ⟨.count 7, 1867721951429334000⟩, ⟨.count 8, 407502971220945600⟩, ⟨.count 9, 122250891366283680⟩, ⟨.path 9, 10207194852254400⟩, ⟨.path 10, 3674744990076160⟩, ⟨.privateRow 2 28, 388486165897301472000⟩, ⟨.privateRow 3 25, 62319655779358777800⟩, ⟨.privateRow 3 26, 144468292943058984900⟩, ⟨.privateRow 4 22, 7089872527625751864⟩, ⟨.privateRow 4 23, 34720951077071319060⟩, ⟨.privateRow 4 24, 55844886347737086600⟩, ⟨.privateRow 4 25, 89837425863750965400⟩, ⟨.privateRow 5 20, 6659762843953739520⟩, ⟨.privateRow 5 21, 13430521735306708032⟩, ⟨.privateRow 5 22, 21574856713225135320⟩, ⟨.privateRow 5 23, 34732513165342072080⟩, ⟨.privateRow 5 24, 36489950582496531120⟩, ⟨.privateRow 6 17, 627020940836990700⟩, ⟨.privateRow 6 18, 3026471896805900400⟩, ⟨.privateRow 6 19, 5523120627798173400⟩, ⟨.privateRow 6 20, 8282012767480932480⟩, ⟨.privateRow 6 21, 13247484984066633300⟩, ⟨.privateRow 6 22, 14639382533584208400⟩, ⟨.privateRow 6 23, 10939514286943242000⟩, ⟨.privateRow 7 15, 512882377138531400⟩, ⟨.privateRow 7 16, 1297399712689305225⟩, ⟨.privateRow 7 17, 2340369955464512400⟩, ⟨.privateRow 7 18, 3424156910953779000⟩, ⟨.privateRow 7 19, 2673510564760275240⟩, ⟨.privateRow 7 20, 11246354321820918300⟩, ⟨.privateRow 7 21, 88939140544254000⟩, ⟨.privateRow 8 12, 24697149770966400⟩, ⟨.privateRow 8 13, 266574860340368580⟩, ⟨.privateRow 8 14, 609367869001691800⟩, ⟨.privateRow 8 15, 1046348775062115525⟩, ⟨.privateRow 8 16, 1540264206698217000⟩, ⟨.privateRow 8 17, 2365781138477156400⟩, ⟨.privateRow 8 18, 1517948567798022360⟩, ⟨.privateRow 9 10, 23771006654555160⟩, ⟨.privateRow 9 11, 133364608763218560⟩, ⟨.privateRow 9 12, 309702258127918656⟩, ⟨.privateRow 9 13, 526735322059666720⟩, ⟨.privateRow 9 14, 769161858179534820⟩, ⟨.privateRow 9 15, 630659360222892000⟩, ⟨.privateRow 10 8, 15673191200805600⟩, ⟨.privateRow 10 9, 72444972661501440⟩, ⟨.privateRow 10 10, 171645190908216480⟩, ⟨.privateRow 10 11, 302910541940902896⟩, ⟨.privateRow 10 12, 161491918224596960⟩, ⟨.privateRow 11 6, 9702451695736800⟩, ⟨.privateRow 11 7, 44407375068949200⟩, ⟨.privateRow 11 8, 107535506294416200⟩, ⟨.privateRow 11 9, 41676440238505800⟩, ⟨.privateRow 12 4, 5336348432655240⟩, ⟨.privateRow 12 5, 30493419615172800⟩, ⟨.privateRow 12 6, 14367091934071800⟩, ⟨.privateRow 13 2, 3335217770409525⟩, ⟨.privateRow 13 3, 7115131243540320⟩, ⟨.hall 5 24, 4550837943368388672⟩, ⟨.hall 4 25, 26895196100582409600⟩, ⟨.hall 3 26, 75269194642602160200⟩, ⟨.hall 2 27, 163719169913862763200⟩, ⟨.assumptionRow 15, 6146894863137600⟩]
  caps := #[0, 216722685251414971200, 17254831507515201600, 0, 751407434526749572, 633461488156356288, 89030222930794860, 93187414313078800, 140505704676375415, 0, 158528259315582544, 13543094892412800, 102804608544438240, 0, 417145905540936000, 62419360894862400, 4897589697000000, 0, 0] }

theorem case_48_30_15_checked :
    (Witness.linear .conditional case_48_30_15).check 48 30 15 = true := by
  change case_48_30_15.check 48 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_30_16 : Certificate := {
  objectiveScale := 29866318237255500000
  eta := 184684633352755466527396800
  rows := #[⟨.count 2, 33505183620895714103376000⟩, ⟨.count 3, 6091851567435584382432000⟩, ⟨.count 4, 1076227110246953240896320⟩, ⟨.count 5, 206687821037993041546800⟩, ⟨.count 6, 38492468695334736482400⟩, ⟨.count 7, 7810066112096903054400⟩, ⟨.count 8, 2130018030571882651200⟩, ⟨.count 9, 639005409171564795360⟩, ⟨.path 8, 252855593642596744800⟩, ⟨.path 9, 5635036746423564480⟩, ⟨.privateRow 2 28, 3248987502632311670630400⟩, ⟨.privateRow 3 25, 486502034899369586097000⟩, ⟨.privateRow 3 26, 1047036988152991065730500⟩, ⟨.privateRow 4 22, 50765429728629869853600⟩, ⟨.privateRow 4 23, 234155544623305274699730⟩, ⟨.privateRow 4 24, 400200804360698807345880⟩, ⟨.privateRow 4 25, 676449351133993015799220⟩, ⟨.privateRow 5 20, 39524513145861827243160⟩, ⟨.privateRow 5 21, 86881406878426548692304⟩, ⟨.privateRow 5 22, 150483238124152828494600⟩, ⟨.privateRow 5 23, 263496754305745514954400⟩, ⟨.privateRow 5 24, 304592578371779219121600⟩, ⟨.privateRow 6 17, 2510378393174004553200⟩, ⟨.privateRow 6 18, 16855397782739744857200⟩, ⟨.privateRow 6 19, 34354993195473877126200⟩, ⟨.privateRow 6 20, 56957696431792414418160⟩, ⟨.privateRow 6 21, 100624333926391349174100⟩, ⟨.privateRow 6 22, 126355712456424895844400⟩, ⟨.privateRow 6 23, 113664355024267428381000⟩, ⟨.privateRow 7 15, 1797554898815953877600⟩, ⟨.privateRow 7 16, 6764075114941067823900⟩, ⟨.privateRow 7 17, 14046164818949787381000⟩, ⟨.privateRow 7 18, 23128023159334578985500⟩, ⟨.privateRow 7 19, 40361305943586495427560⟩, ⟨.privateRow 7 20, 52369282590935483873700⟩, ⟨.privateRow 7 21, 52113595902741835261800⟩, ⟨.privateRow 7 22, 14434675760750526180900⟩, ⟨.privateRow 8 13, 887507512738284438000⟩, ⟨.privateRow 8 14, 2879468819106433954400⟩, ⟨.privateRow 8 15, 6023957242711105622925⟩, ⟨.privateRow 8 16, 10142943002723250720000⟩, ⟨.privateRow 8 17, 12291979051425239466300⟩, ⟨.privateRow 8 18, 34630543147047858770760⟩, ⟨.privateRow 8 19, 8453509058832159271950⟩, ⟨.privateRow 9 11, 374366805373239981120⟩, ⟨.privateRow 9 12, 1327711239056473519248⟩, ⟨.privateRow 9 13, 2816357173756155949920⟩, ⟨.privateRow 9 14, 4854666094678415875860⟩, ⟨.privateRow 9 15, 8712788039339272368480⟩, ⟨.privateRow 9 16, 8898741994389198631680⟩, ⟨.privateRow 10 9, 147917918789714073000⟩, ⟨.privateRow 10 10, 645460009264206864000⟩, ⟨.privateRow 10 11, 1469712441094599029328⟩, ⟨.privateRow 10 12, 2619133282036537185920⟩, ⟨.privateRow 10 13, 4331036662162828057440⟩, ⟨.privateRow 11 7, 54615846937740580800⟩, ⟨.privateRow 11 8, 325419421337370960600⟩, ⟨.privateRow 11 9, 847166262159271509000⟩, ⟨.privateRow 11 10, 1624138748311060521540⟩, ⟨.privateRow 11 11, 108473140445790320200⟩, ⟨.privateRow 12 5, 19923638041063528200⟩, ⟨.privateRow 12 6, 171649804661470396800⟩, ⟨.privateRow 12 7, 534617620768538006700⟩, ⟨.privateRow 12 8, 164822823794252824200⟩, ⟨.privateRow 13 4, 99618190205317641000⟩, ⟨.privateRow 13 5, 128737353496102797600⟩, ⟨.privateRow 14 2, 48348028312980828432⟩, ⟨.hall 5 24, 66575234986974600750864⟩, ⟨.hall 4 25, 248360102364681517129920⟩, ⟨.hall 3 26, 612005458395148986568400⟩, ⟨.hall 2 27, 1261883538968799622075200⟩, ⟨.assumptionRow 16, 28904622790015872900⟩]
  caps := #[0, 0, 189419000835422264306400, 5259949329958724501100, 3017347645210943564520, 5813812582909356881856, 0, 0, 0, 0, 225466809636689220600, 1082131934799634587400, 28904622790015872900, 1527871495247139081600, 610537676573546017296, 2283303922292772779400, 359357514294305627100, 29866318237255500000, 0] }

theorem case_48_30_16_checked :
    (Witness.linear .conditional case_48_30_16).check 48 30 16 = true := by
  change case_48_30_16.check 48 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_30_17 : Certificate := {
  objectiveScale := 862713132781500000
  eta := 6091696927169760543436800
  rows := #[⟨.count 2, 1030213450918415386022400⟩, ⟨.count 3, 172868697266880842627400⟩, ⟨.count 4, 27621664988392296581760⟩, ⟨.count 5, 4532512594620357547200⟩, ⟨.count 6, 707564183323087490400⟩, ⟨.count 7, 125618278923301764600⟩, ⟨.count 8, 26102499516530236800⟩, ⟨.count 9, 11746124782438606560⟩, ⟨.path 7, 16393893844131203400⟩, ⟨.path 8, 3068928845969706720⟩, ⟨.privateRow 2 28, 104514408064187068147200⟩, ⟨.privateRow 3 25, 14619574937549976794400⟩, ⟨.privateRow 3 26, 32660752520058458796000⟩, ⟨.privateRow 4 22, 1399746536573933948400⟩, ⟨.privateRow 4 23, 6765441593440680750600⟩, ⟨.privateRow 4 24, 12302216782555352813160⟩, ⟨.privateRow 4 25, 22046007951039459687300⟩, ⟨.privateRow 5 20, 1010928054192285629400⟩, ⟨.privateRow 5 21, 2426227330061485510560⟩, ⟨.privateRow 5 22, 4519181675224415319120⟩, ⟨.privateRow 5 23, 8562893891993557836720⟩, ⟨.privateRow 5 24, 10804710170411175858840⟩, ⟨.privateRow 6 17, 48709128562096602600⟩, ⟨.privateRow 6 18, 407984730963726430800⟩, ⟨.privateRow 6 19, 916927981528590431400⟩, ⟨.privateRow 6 20, 1668415835169077314320⟩, ⟨.privateRow 6 21, 3231466134343303556700⟩, ⟨.privateRow 6 22, 4532512594620357547200⟩, ⟨.privateRow 6 23, 4668385426925153333400⟩, ⟨.privateRow 7 15, 30193962734399063600⟩, ⟨.privateRow 7 16, 152216026756551883125⟩, ⟨.privateRow 7 17, 357078198105595395000⟩, ⟨.privateRow 7 18, 655009597242930629700⟩, ⟨.privateRow 7 19, 1274128257650632183800⟩, ⟨.privateRow 7 20, 1870174172949972189300⟩, ⟨.privateRow 7 21, 2178238047452355088200⟩, ⟨.privateRow 7 22, 1558692113987091283200⟩, ⟨.privateRow 8 13, 12072406026395234520⟩, ⟨.privateRow 8 14, 58730623912193032800⟩, ⟨.privateRow 8 15, 144175524673334979825⟩, ⟨.privateRow 8 16, 274542360986362669200⟩, ⟨.privateRow 8 17, 542986370151155030100⟩, ⟨.privateRow 8 18, 829733203381704902280⟩, ⟨.privateRow 8 19, 1029825176238106998750⟩, ⟨.privateRow 8 20, 346401920667286684200⟩, ⟨.privateRow 9 11, 3796727202404398080⟩, ⟨.privateRow 9 12, 23361737067294561936⟩, ⟨.privateRow 9 13, 61920929408657839520⟩, ⟨.privateRow 9 14, 123497450837583682860⟩, ⟨.privateRow 9 15, 253567138160579443200⟩, ⟨.privateRow 9 16, 406981471628567275440⟩, ⟨.privateRow 9 17, 385794942854316899904⟩, ⟨.privateRow 10 9, 870083317217674560⟩, ⟨.privateRow 10 10, 9254522555860720320⟩, ⟨.privateRow 10 11, 28451724473017958112⟩, ⟨.privateRow 10 12, 60760818319034273440⟩, ⟨.privateRow 10 13, 130838778826607811960⟩, ⟨.privateRow 10 14, 224108602991923890240⟩, ⟨.privateRow 10 15, 18706791320180003040⟩, ⟨.privateRow 11 8, 3398762957881541250⟩, ⟨.privateRow 11 9, 13644488383640805600⟩, ⟨.privateRow 11 10, 20555718369267561480⟩, ⟨.privateRow 11 11, 100603383553293621000⟩, ⟨.privateRow 11 12, 34463456392918828275⟩, ⟨.privateRow 12 6, 788811798576463200⟩, ⟨.privateRow 12 7, 6622732392214888950⟩, ⟨.privateRow 12 8, 19343816606000086200⟩, ⟨.privateRow 12 9, 32301843151706168040⟩, ⟨.privateRow 13 5, 2760841295017621200⟩, ⟨.privateRow 13 6, 11536372554180774300⟩, ⟨.privateRow 13 7, 4195044565156645200⟩, ⟨.privateRow 14 3, 952208528281587720⟩, ⟨.privateRow 14 4, 4101821352597608640⟩, ⟨.hall 6 23, 255082015364663787300⟩, ⟨.hall 5 24, 3274073803643411216448⟩, ⟨.hall 4 25, 9582880135006163185200⟩, ⟨.hall 3 26, 21333174066673104435800⟩, ⟨.hall 2 27, 41459159321380329328800⟩, ⟨.assumptionRow 17, 566896642397385300⟩]
  caps := #[0, 0, 676958397212845347600, 0, 0, 30580050668879154300, 4735460741384364420, 7842183140083273410, 24380650314912136245, 0, 2688690966824182320, 26175502872215055450, 566896642397385300, 10519733299634143200, 0, 250928898657760323000, 59059254873009491100, 9785660950980614700, 862713132781500000] }

theorem case_48_30_17_checked :
    (Witness.linear .conditional case_48_30_17).check 48 30 17 = true := by
  change case_48_30_17.check 48 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_30_18 : Certificate := {
  objectiveScale := 1794443316185520000
  eta := 16942532078690896511433600
  rows := #[⟨.count 2, 2993591259552786737644800⟩, ⟨.count 3, 516506471995781626959600⟩, ⟨.count 4, 85104589423695184062720⟩, ⟨.count 5, 14130774559698761764800⟩, ⟨.count 6, 2091928889824780406400⟩, ⟨.count 7, 251236557846603529200⟩, ⟨.count 8, 26102499516530236800⟩, ⟨.path 7, 10669768898554665900⟩, ⟨.path 8, 22093740862064071200⟩, ⟨.privateRow 2 28, 313543224192561204441600⟩, ⟨.privateRow 3 25, 41059231739502062486400⟩, ⟨.privateRow 3 26, 97282384291888409413800⟩, ⟨.privateRow 4 22, 3639340995092228265840⟩, ⟨.privateRow 4 23, 19596451512035075277600⟩, ⟨.privateRow 4 24, 36300093515150687061840⟩, ⟨.privateRow 4 25, 66627935140919255943840⟩, ⟨.privateRow 5 20, 2861704030328931627840⟩, ⟨.privateRow 5 21, 6964072292440219948992⟩, ⟨.privateRow 5 22, 13210941121378748027280⟩, ⟨.privateRow 5 23, 25693125315779320919520⟩, ⟨.privateRow 5 24, 33567255038982530305440⟩, ⟨.privateRow 6 17, 187145599212265894200⟩, ⟨.privateRow 6 18, 1157299595911468152000⟩, ⟨.privateRow 6 19, 2592692913287738461200⟩, ⟨.privateRow 6 20, 4795029161186604500160⟩, ⟨.privateRow 6 21, 9572625581624669163600⟩, ⟨.privateRow 6 22, 14007719919120833505600⟩, ⟨.privateRow 6 23, 15233139048209369086800⟩, ⟨.privateRow 7 14, 3589093683522907560⟩, ⟨.privateRow 7 15, 123624337988011260400⟩, ⟨.privateRow 7 16, 433895789954465788950⟩, ⟨.privateRow 7 17, 991029337511529373200⟩, ⟨.privateRow 7 18, 1839837785863052375400⟩, ⟨.privateRow 7 19, 3700868315381192395440⟩, ⟨.privateRow 7 20, 5700249860937989256900⟩, ⟨.privateRow 7 21, 7085896386612368925600⟩, ⟨.privateRow 7 22, 5696404403419928998800⟩, ⟨.privateRow 8 12, 5339147628381184800⟩, ⟨.privateRow 8 13, 54488967740756869320⟩, ⟨.privateRow 8 14, 172203989865998090000⟩, ⟨.privateRow 8 15, 393168898967736691800⟩, ⟨.privateRow 8 16, 751379093225834673600⟩, ⟨.privateRow 8 17, 1537872263182239784800⟩, ⟨.privateRow 8 18, 2475169516654979704560⟩, ⟨.privateRow 8 19, 3289730642192701406700⟩, ⟨.privateRow 8 20, 2327472873557279448000⟩, ⟨.privateRow 9 10, 3045291610261860960⟩, ⟨.privateRow 9 11, 22780363214426388480⟩, ⟨.privateRow 9 12, 72825973651119360672⟩, ⟨.privateRow 9 13, 169086191312634756160⟩, ⟨.privateRow 9 14, 330196618884107495520⟩, ⟨.privateRow 9 15, 697309629941593468800⟩, ⟨.privateRow 9 16, 923158399567952708160⟩, ⟨.privateRow 9 17, 2188955609456225658048⟩, ⟨.privateRow 10 8, 1405519204736243520⟩, ⟨.privateRow 10 9, 10005958148003257440⟩, ⟨.privateRow 10 10, 33221363021038483200⟩, ⟨.privateRow 10 11, 80395698510913129344⟩, ⟨.privateRow 10 12, 161545469230081576640⟩, ⟨.privateRow 10 13, 278644182338960277840⟩, ⟨.privateRow 10 14, 770023735737641985600⟩, ⟨.privateRow 10 15, 418510075581701463360⟩, ⟨.privateRow 11 6, 699174094192774200⟩, ⟨.privateRow 11 7, 4768725873212254800⟩, ⟨.privateRow 11 8, 16585963234461921300⟩, ⟨.privateRow 11 9, 42713181027049478400⟩, ⟨.privateRow 11 10, 90053623332029316960⟩, ⟨.privateRow 11 11, 200844232391079877600⟩, ⟨.privateRow 11 12, 308335775539013422200⟩, ⟨.privateRow 12 4, 341818446049800720⟩, ⟨.privateRow 12 5, 2563638345373505400⟩, ⟨.privateRow 12 6, 9465741582917558400⟩, ⟨.privateRow 12 7, 26063656511297304900⟩, ⟨.privateRow 12 8, 58264507849397850000⟩, ⟨.privateRow 12 9, 135360104635721085120⟩, ⟨.privateRow 12 10, 7406066331079015600⟩, ⟨.privateRow 13 3, 2050910676298804320⟩, ⟨.privateRow 13 4, 6592212888103299600⟩, ⟨.privateRow 13 5, 18931483165835116800⟩, ⟨.privateRow 13 6, 44436397986474093600⟩, ⟨.privateRow 13 7, 9322321255903656000⟩, ⟨.privateRow 14 1, 1666364924492778510⟩, ⟨.privateRow 14 2, 3554911838917927488⟩, ⟨.privateRow 14 3, 19044170565631754400⟩, ⟨.privateRow 15 0, 5832277235724724785⟩, ⟨.hall 6 23, 1725328606436369134200⟩, ⟨.hall 5 24, 11384605164134662780320⟩, ⟨.hall 4 25, 30823136554094730125280⟩, ⟨.hall 3 26, 66254669397832873557600⟩, ⟨.hall 2 27, 125843879097694633075200⟩, ⟨.assumptionRow 18, 197561307406963500⟩]
  caps := #[0, 52742323598622815757600, 5271078791545779712500, 698001252859421210700, 262482999111731558160, 64047855191637805488, 0, 17024122123276210800, 63880452243614393660, 15099540194948736800, 635454222864712020, 0, 27270259781425924340, 2179092593567479590, 159576220548894300294, 245702304862598173590, 474670804648310770500, 114268079863175238000, 19541315170633756500] }

theorem case_48_30_18_checked :
    (Witness.linear .conditional case_48_30_18).check 48 30 18 = true := by
  change case_48_30_18.check 48 30 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_30_19 : Certificate := {
  objectiveScale := 560763536307975000
  eta := 4949503753325430441542400
  rows := #[⟨.count 2, 925699042854228317875200⟩, ⟨.count 3, 160270978437715437091800⟩, ⟨.count 4, 28368196474565061354240⟩, ⟨.count 5, 4465857997640646406800⟩, ⟨.count 6, 676800523178605425600⟩, ⟨.count 7, 89727342088072689000⟩, ⟨.count 8, 13051249758265118400⟩, ⟨.path 7, 641101993904572200⟩, ⟨.path 8, 6927374656462740480⟩, ⟨.privateRow 8 13, 2610249951653023680⟩, ⟨.privateRow 8 14, 10513506749713567600⟩, ⟨.privateRow 9 11, 1423772700901649280⟩, ⟨.privateRow 9 12, 5612037396054000912⟩, ⟨.privateRow 10 9, 326281243956627960⟩, ⟨.privateRow 10 10, 1067829525676236960⟩, ⟨.privateRow 10 17, 95926685723248620240⟩, ⟨.privateRow 11 7, 125492786137164600⟩, ⟨.privateRow 11 8, 407851554945784950⟩, ⟨.privateRow 11 9, 741548281719609000⟩, ⟨.privateRow 11 10, 489421865934941940⟩, ⟨.privateRow 15 10, 7776369647632966380⟩, ⟨.hall 12 5, 1795264947740550⟩, ⟨.hall 11 6, 47054839156568100⟩, ⟨.hall 12 6, 33419547488708700⟩, ⟨.hall 13 7, 15765690359248830⟩, ⟨.hall 10 8, 21847918494674580⟩, ⟨.hall 9 10, 15411394788774600⟩, ⟨.hall 14 10, 5826450784939785⟩, ⟨.hall 8 12, 4321178161226640⟩, ⟨.hall 8 14, 38702341005331640⟩, ⟨.hall 7 16, 157160189970583800⟩, ⟨.hall 5 19, 905601747220110798⟩, ⟨.hall 6 19, 2492273370541820580⟩, ⟨.hall 4 21, 4860171920849597352⟩, ⟨.hall 3 23, 30906084497002815100⟩]
  caps := #[0, 8721910881172072584000, 0, 0, 28684671925549199560, 26891276173500538800, 12611645644862392128, 0, 12683795443562283040, 0, 1385881579591421640, 0, 24533490984787184400, 0, 0, 65074103644744989795, 357206372628180075000, 116638815552058800000, 30281230960630650000] }

theorem case_48_30_19_checked :
    (Witness.linear .negative case_48_30_19).check 48 30 19 = true := by
  change case_48_30_19.check 48 30 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_31_1_checked :
    (Witness.rising).check 48 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_31_2_checked :
    (Witness.rising).check 48 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_31_3_checked :
    (Witness.rising).check 48 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_31_4_checked :
    (Witness.rising).check 48 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_31_5_checked :
    (Witness.rising).check 48 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_31_6_checked :
    (Witness.rising).check 48 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_31_7_checked :
    (Witness.rising).check 48 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_31_8_checked :
    (Witness.rising).check 48 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_31_9_checked :
    (Witness.rising).check 48 31 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_31_10_checked :
    (Witness.linear .positive case_48_31_10).check 48 31 10 = true := by
  change case_48_31_10.check 48 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_31_11_checked :
    (Witness.linear .positive case_48_31_11).check 48 31 11 = true := by
  change case_48_31_11.check 48 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_48_31_12_checked :
    (Witness.linear .positive case_48_31_12).check 48 31 12 = true := by
  change case_48_31_12.check 48 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_48_31_13_checked :
    (Witness.linear .positive case_48_31_13).check 48 31 13 = true := by
  change case_48_31_13.check 48 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_48_31_14_checked :
    (Witness.linear .positive case_48_31_14).check 48 31 14 = true := by
  change case_48_31_14.check 48 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_31_15 : Certificate := {
  objectiveScale := 39663980000
  eta := 1357849536731287600
  rows := #[⟨.count 2, 179204560952326910⟩, ⟨.count 3, 23288698449751735⟩, ⟨.count 4, 2977344499145016⟩, ⟨.count 5, 390386079433350⟩, ⟨.count 6, 65064346572225⟩, ⟨.count 7, 16561833672930⟩, ⟨.count 8, 4416488979448⟩, ⟨.count 9, 2208244489724⟩, ⟨.path 5, 26662572536600⟩, ⟨.path 6, 9334030588960⟩]
  caps := #[0, 0, 195514205785090, 0, 0, 0, 989175416735, 454013747070, 819156380552, 0, 555295720000, 198319900000, 79327960000, 39663980000, 39663980000, 0, 0, 0] }

theorem case_48_31_15_checked :
    (Witness.linear .positive case_48_31_15).check 48 31 15 = true := by
  change case_48_31_15.check 48 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_31_16 : Certificate := {
  objectiveScale := 42963778857799800000
  eta := 680354532791091939273292800
  rows := #[⟨.count 2, 104562684342893228371920000⟩, ⟨.count 3, 16079417236729358674081920⟩, ⟨.count 4, 2522782225415836621036800⟩, ⟨.count 5, 388120342371667172467200⟩, ⟨.count 6, 61282159321842185126400⟩, ⟨.count 7, 9749434437565802179200⟩, ⟨.count 8, 2599849183350880581120⟩, ⟨.path 7, 1926017795090650060800⟩, ⟨.path 8, 116080668901778666085⟩, ⟨.privateRow 2 29, 9062099309717413125566400⟩, ⟨.privateRow 3 25, 92944608304793980775040⟩, ⟨.privateRow 3 26, 1796929093892683628317440⟩, ⟨.privateRow 3 27, 2912264393550211397617920⟩, ⟨.privateRow 4 23, 334600589897258330790144⟩, ⟨.privateRow 4 24, 735258240696852383631120⟩, ⟨.privateRow 4 25, 1121974200250727339355840⟩, ⟨.privateRow 4 26, 1739391955418287354504320⟩, ⟨.privateRow 5 20, 43481151137878502780160⟩, ⟨.privateRow 5 21, 159333614236789681328640⟩, ⟨.privateRow 5 22, 276995360134726676771328⟩, ⟨.privateRow 5 23, 420293476015634319658560⟩, ⟨.privateRow 5 24, 676146491184325442561280⟩, ⟨.privateRow 5 25, 685338815082601770330240⟩, ⟨.privateRow 6 17, 3404564406769010284800⟩, ⟨.privateRow 6 18, 27981263718132803278200⟩, ⟨.privateRow 6 19, 65173090072435339737600⟩, ⟨.privateRow 6 20, 111073913770838960541600⟩, ⟨.privateRow 6 21, 163248863304574043156160⟩, ⟨.privateRow 6 22, 262151459321213791929600⟩, ⟨.privateRow 6 23, 288253119773109537446400⟩, ⟨.privateRow 6 24, 201294870550217733088800⟩, ⟨.privateRow 7 15, 2971256209543863521280⟩, ⟨.privateRow 7 16, 13515089008689101433600⟩, ⟨.privateRow 7 17, 28261753399372295602800⟩, ⟨.privateRow 7 18, 47354395839605324870400⟩, ⟨.privateRow 7 19, 69329311556023482163200⟩, ⟨.privateRow 7 20, 89880500338701871518720⟩, ⟨.privateRow 7 21, 165740385438618637046400⟩, ⟨.privateRow 8 13, 1743080702473885844160⟩, ⟨.privateRow 8 14, 6499622958377201452800⟩, ⟨.privateRow 8 15, 13432554113979549669120⟩, ⟨.privateRow 8 16, 22342453919421629994000⟩, ⟨.privateRow 8 17, 32683818304982498734080⟩, ⟨.privateRow 8 18, 51942820142364468276960⟩, ⟨.privateRow 8 19, 21903729369731168895936⟩, ⟨.privateRow 9 11, 914761749697532056320⟩, ⟨.privateRow 9 12, 3361421166352653680640⟩, ⟨.privateRow 9 13, 7135141647640750039296⟩, ⟨.privateRow 9 14, 12068435715307791339520⟩, ⟨.privateRow 9 15, 17765636086231017304320⟩, ⟨.privateRow 9 16, 10688268864886953500160⟩, ⟨.privateRow 10 9, 474972446958333952320⟩, ⟨.privateRow 10 10, 1949886887513160435840⟩, ⟨.privateRow 10 11, 4342929885824766425280⟩, ⟨.privateRow 10 12, 7604558861301325699776⟩, ⟨.privateRow 10 13, 2599849183350880581120⟩, ⟨.privateRow 11 7, 265290732994987814400⟩, ⟨.privateRow 11 8, 1249927491995615664000⟩, ⟨.privateRow 11 9, 3095058551608191168000⟩, ⟨.privateRow 11 10, 633080158283493648000⟩, ⟨.privateRow 12 5, 170228220338450514240⟩, ⟨.privateRow 12 6, 911936894670270612000⟩, ⟨.privateRow 12 7, 392834354627193494400⟩, ⟨.privateRow 13 3, 127671165253837885680⟩, ⟨.privateRow 13 4, 272365152541520822784⟩, ⟨.hall 5 25, 18856049022105287731200⟩, ⟨.hall 4 26, 382597382334019666894080⟩, ⟨.hall 3 27, 1208279907962321750075520⟩, ⟨.hall 2 28, 2900512776408225951772800⟩, ⟨.assumptionRow 16, 44165723119664065920⟩]
  caps := #[0, 0, 123996985470430720297650, 28006856226700785676242, 10225401148398810638979, 2074809977074058909256, 6067577713985375771700, 661306690599734436075, 1292273260752700586997, 988108192646681895488, 360537450528498122880, 142879003838729421120, 6402893136348022855200, 0, 18116574647403067355520, 3805747154416218211200, 557327180889533134080, 42963778857799800000] }

theorem case_48_31_16_checked :
    (Witness.linear .conditional case_48_31_16).check 48 31 16 = true := by
  change case_48_31_16.check 48 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_31_17 : Certificate := {
  objectiveScale := 6816116868561000000
  eta := 124291712417795795794521600
  rows := #[⟨.count 2, 17674031254040593445613600⟩, ⟨.count 3, 2450381914277014430512800⟩, ⟨.count 4, 333669026624955156495360⟩, ⟨.count 5, 42396133190670813153600⟩, ⟨.count 6, 5156286469135639437600⟩, ⟨.count 7, 1093757735877256850400⟩, ⟨.count 8, 291668729567268493440⟩, ⟨.path 6, 929932330820954630400⟩, ⟨.path 7, 154920802145190681600⟩, ⟨.privateRow 2 29, 1590141455009551917673200⟩, ⟨.privateRow 3 25, 15640735623044772960720⟩, ⟨.privateRow 3 26, 295436117324179044813600⟩, ⟨.privateRow 3 27, 505717118478447659063280⟩, ⟨.privateRow 4 23, 49603475833084851389712⟩, ⟨.privateRow 4 24, 118050314107266500679720⟩, ⟨.privateRow 4 25, 193150671662362434340320⟩, ⟨.privateRow 4 26, 319517884870771790483280⟩, ⟨.privateRow 5 20, 5303608939682371992960⟩, ⟨.privateRow 5 21, 22764049893369193368960⟩, ⟨.privateRow 5 22, 43404473655746227088064⟩, ⟨.privateRow 5 23, 71615089849106103300000⟩, ⟨.privateRow 5 24, 125431442701047703059840⟩, ⟨.privateRow 5 25, 141626001685592229886080⟩, ⟨.privateRow 6 17, 222802501752774543600⟩, ⟨.privateRow 6 18, 3282358284750696401250⟩, ⟨.privateRow 6 19, 8948475988764495955200⟩, ⟨.privateRow 6 20, 16932990133210865313600⟩, ⟨.privateRow 6 21, 27481097144763648706320⟩, ⟨.privateRow 6 22, 48722132794008518945100⟩, ⟨.privateRow 6 23, 61079714409082049881200⟩, ⟨.privateRow 6 24, 52708706128942092028800⟩, ⟨.privateRow 7 15, 161459475296166487440⟩, ⟨.privateRow 7 16, 1493066115641969668800⟩, ⟨.privateRow 7 17, 3691432358585741870100⟩, ⟨.privateRow 7 18, 6994097086562050608000⟩, ⟨.privateRow 7 19, 11415011291099942526000⟩, ⟨.privateRow 7 20, 20239726483900095812640⟩, ⟨.privateRow 7 21, 26679876200148801029400⟩, ⟨.privateRow 7 22, 23784890446854633096000⟩, ⟨.privateRow 8 13, 66288347628924657600⟩, ⟨.privateRow 8 14, 652608782406763254072⟩, ⟨.privateRow 8 15, 1652789467547854796160⟩, ⟨.privateRow 8 16, 3149110814546602015110⟩, ⟨.privateRow 8 17, 5197953430502392079520⟩, ⟨.privateRow 8 18, 5414100792592421409480⟩, ⟨.privateRow 8 19, 20664729489840972760224⟩, ⟨.privateRow 9 11, 18904454694174809760⟩, ⟨.privateRow 9 12, 288722580783760730880⟩, ⟨.privateRow 9 13, 806950151802776165184⟩, ⟨.privateRow 9 14, 1591575042823860174080⟩, ⟨.privateRow 9 15, 2665528111878648176160⟩, ⟨.privateRow 9 16, 4847256505665557343360⟩, ⟨.privateRow 9 17, 3699871847288498481600⟩, ⟨.privateRow 10 9, 2804507015069889360⟩, ⟨.privateRow 10 10, 133681501051664726160⟩, ⟨.privateRow 10 11, 434188676969456507280⟩, ⟨.privateRow 10 12, 918756498136895754336⟩, ⟨.privateRow 10 13, 1587974194310684019840⟩, ⟨.privateRow 10 14, 1968763924579062330720⟩, ⟨.privateRow 11 8, 60096578894354772000⟩, ⟨.privateRow 11 9, 256078200066500611800⟩, ⟨.privateRow 11 10, 606064892607311155200⟩, ⟨.privateRow 11 11, 822922486993364677920⟩, ⟨.privateRow 12 6, 27281938990135658400⟩, ⟨.privateRow 12 7, 161593023249265053600⟩, ⟨.privateRow 12 8, 381947145861899217600⟩, ⟨.privateRow 13 4, 15277885834475968704⟩, ⟨.privateRow 13 5, 114584143758569765280⟩, ⟨.privateRow 13 6, 52884989427032199360⟩, ⟨.privateRow 14 3, 49653128962046898288⟩, ⟨.hall 5 25, 16879125792127776962400⟩, ⟨.hall 4 26, 89927333564596049121600⟩, ⟨.hall 3 27, 240941808288332573942520⟩, ⟨.hall 2 28, 533942354028080180383200⟩, ⟨.assumptionRow 17, 5074944683141998665⟩]
  caps := #[0, 107350193505576229933725, 27984634584697809018000, 5253972177920255669880, 1316210749349075623890, 895307511432942981516, 370613804847747914970, 0, 0, 832612989714697951942, 45727436472772533444, 18558606547148993325, 427137367668317448120, 0, 0, 2471297175120072138840, 542401292606502018690, 83534574608151001335] }

theorem case_48_31_17_checked :
    (Witness.linear .conditional case_48_31_17).check 48 31 17 = true := by
  change case_48_31_17.check 48 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_31_18 : Certificate := {
  objectiveScale := 11139482425191120000
  eta := 256090977934653082610188800
  rows := #[⟨.count 2, 36599321357924768728084800⟩, ⟨.count 3, 5078025498948536287913760⟩, ⟨.count 4, 676275616463078754682560⟩, ⟨.count 5, 81354742068584533348800⟩, ⟨.count 6, 8020890063099883569600⟩, ⟨.count 7, 364585911959085616800⟩, ⟨.path 6, 1505352763121260838400⟩, ⟨.path 7, 451658203246599148800⟩, ⟨.privateRow 2 29, 3414893944364775429757200⟩, ⟨.privateRow 3 25, 22592173677731338721040⟩, ⟨.privateRow 3 26, 610567975803303359281440⟩, ⟨.privateRow 3 27, 1073997179449074409969440⟩, ⟨.privateRow 4 23, 97568398410422155135920⟩, ⟨.privateRow 4 24, 241314206755547925679680⟩, ⟨.privateRow 4 25, 405914329264733393504400⟩, ⟨.privateRow 4 26, 693033547487769582854760⟩, ⟨.privateRow 5 20, 11294722741916162577600⟩, ⟨.privateRow 5 21, 44458647778325068928640⟩, ⟨.privateRow 5 22, 86946448284002737894464⟩, ⟨.privateRow 5 23, 148329174095468561154960⟩, ⟨.privateRow 5 24, 271029694703603684808960⟩, ⟨.privateRow 5 25, 322898117111649598559040⟩, ⟨.privateRow 6 17, 976087150535964667200⟩, ⟨.privateRow 6 18, 6481165631344102348650⟩, ⟨.privateRow 6 19, 17160339624795329133600⟩, ⟨.privateRow 6 20, 33133914903519757126800⟩, ⟨.privateRow 6 21, 55802478010423475691360⟩, ⟨.privateRow 6 22, 103985110460902061991600⟩, ⟨.privateRow 6 23, 139347050381949564554400⟩, ⟨.privateRow 6 24, 132344686041148078898400⟩, ⟨.privateRow 7 14, 33144173814462328800⟩, ⟨.privateRow 7 15, 682296492380574511440⟩, ⟨.privateRow 7 16, 2881964827867057732800⟩, ⟨.privateRow 7 17, 6894580013654851217700⟩, ⟨.privateRow 7 18, 13311106050914370784800⟩, ⟨.privateRow 7 19, 22595645924511901441200⟩, ⟨.privateRow 7 20, 42375299709987436832640⟩, ⟨.privateRow 7 21, 60143654547822016571400⟩, ⟨.privateRow 7 22, 66094217468011378245600⟩, ⟨.privateRow 7 23, 16224073082179309947600⟩, ⟨.privateRow 8 12, 24305727463939041120⟩, ⟨.privateRow 8 13, 351328242433300685280⟩, ⟨.privateRow 8 14, 1279696550976390514968⟩, ⟨.privateRow 8 15, 3009859250951117925360⟩, ⟨.privateRow 8 16, 5819702619646904158170⟩, ⟨.privateRow 8 17, 9979237247337257739840⟩, ⟨.privateRow 8 18, 18970620285604421594160⟩, ⟨.privateRow 8 19, 28299158486264225576016⟩, ⟨.privateRow 8 20, 25074396094986113295420⟩, ⟨.privateRow 9 10, 9971580498026273280⟩, ⟨.privateRow 9 11, 175541365017337519200⟩, ⟨.privateRow 9 12, 615745095753122375040⟩, ⟨.privateRow 9 13, 1461584411498201006016⟩, ⟨.privateRow 9 14, 2859073719461866466560⟩, ⟨.privateRow 9 15, 4954317448066241214960⟩, ⟨.privateRow 9 16, 9532474828238187745920⟩, ⟨.privateRow 9 17, 14972328117786449329920⟩, ⟨.privateRow 9 18, 2022236524999728221184⟩, ⟨.privateRow 10 8, 5208370170844080240⟩, ⟨.privateRow 10 9, 92548731497306348880⟩, ⟨.privateRow 10 10, 334203752629161815400⟩, ⟨.privateRow 10 11, 815346675835773288480⟩, ⟨.privateRow 10 12, 1626053167337521850928⟩, ⟨.privateRow 10 13, 2859973931590160505120⟩, ⟨.privateRow 10 14, 5550820509577078515780⟩, ⟨.privateRow 10 15, 2848978483451711891280⟩, ⟨.privateRow 11 6, 3472246780562720160⟩, ⟨.privateRow 11 7, 55803966116186574000⟩, ⟨.privateRow 11 8, 212341245426720194400⟩, ⟨.privateRow 11 9, 538198250987221624800⟩, ⟨.privateRow 11 10, 1103227499824246087200⟩, ⟨.privateRow 11 11, 1979180664920750491200⟩, ⟨.privateRow 11 12, 1296305464743415526400⟩, ⟨.privateRow 12 5, 38194714586189921760⟩, ⟨.privateRow 12 6, 163691633940813950400⟩, ⟨.privateRow 12 7, 374602008441478078800⟩, ⟨.privateRow 12 8, 1026482954503854147300⟩, ⟨.privateRow 12 9, 199654189882356409200⟩, ⟨.privateRow 13 3, 28646035939642441320⟩, ⟨.privateRow 13 4, 152778858344759687040⟩, ⟨.privateRow 13 5, 409229084852034876000⟩, ⟨.privateRow 14 1, 43811584378276674960⟩, ⟨.privateRow 14 2, 139649425205756901435⟩, ⟨.hall 5 25, 53413839321302521353600⟩, ⟨.hall 4 26, 217922066000094720264000⟩, ⟨.hall 3 27, 544818957536059591465080⟩, ⟨.hall 2 28, 1161369564653669348577600⟩, ⟨.assumptionRow 18, 3485080554895239300⟩]
  caps := #[0, 175613797847617122193200, 19093407814614743309700, 0, 653679258578622793440, 2136185027597075625456, 290194397861533903650, 188060838379734804120, 20226242568866033700, 23716256924069413816, 192410497880063041572, 0, 271073105253774246060, 929095030631842897680, 0, 12502312411586905908000, 3585161598876320463000, 812434099526078129100] }

theorem case_48_31_18_checked :
    (Witness.linear .conditional case_48_31_18).check 48 31 18 = true := by
  change case_48_31_18.check 48 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_31_19 : Certificate := {
  objectiveScale := 4943557289286000000
  eta := 160578219063259669063392000
  rows := #[⟨.count 2, 21983922847946264217012000⟩, ⟨.count 3, 2884846792694924790532800⟩, ⟨.count 4, 347571902734328288016000⟩, ⟨.count 5, 35330110992225677628000⟩, ⟨.count 6, 2387169661636870110000⟩, ⟨.path 6, 1673349073241120352000⟩, ⟨.path 7, 71587776680500080000⟩, ⟨.privateRow 6 18, 2476688523948252739125⟩, ⟨.privateRow 6 22, 77801837888848325001750⟩, ⟨.privateRow 7 14, 27620144845385274000⟩, ⟨.privateRow 7 16, 1331027932549042728000⟩, ⟨.privateRow 7 18, 5729207187928488264000⟩, ⟨.privateRow 7 19, 4506686967272030541000⟩, ⟨.privateRow 7 20, 11536539928419637731600⟩, ⟨.privateRow 7 22, 137746923323906911014000⟩, ⟨.privateRow 8 12, 17722926275788884150⟩, ⟨.privateRow 8 15, 1741910468248964613600⟩, ⟨.privateRow 8 19, 25205039380104785641440⟩, ⟨.privateRow 9 10, 4154825207510947200⟩, ⟨.privateRow 9 12, 9820495945025875200⟩, ⟨.privateRow 9 20, 21893158960111017779200⟩, ⟨.privateRow 10 8, 2170154237851700100⟩, ⟨.privateRow 10 20, 334203752629161815400⟩, ⟨.privateRow 14 12, 206888037341862076200⟩, ⟨.privateRow 14 15, 206888037341862076200⟩, ⟨.hall 11 6, 30794242281177375⟩, ⟨.hall 10 7, 96301994042954700⟩, ⟨.hall 14 7, 148932153578057850⟩, ⟨.hall 9 8, 18147394790053620⟩, ⟨.hall 10 8, 198149617864684200⟩, ⟨.hall 11 8, 187607999128403700⟩, ⟨.hall 12 8, 146549009420167200⟩, ⟨.hall 9 9, 207548103017733660⟩, ⟨.hall 13 9, 63828065819167650⟩, ⟨.hall 8 11, 118345765410180000⟩, ⟨.hall 7 13, 118673463336553125⟩, ⟨.hall 5 19, 2316351919426993800⟩, ⟨.hall 4 22, 68498315031625951472⟩, ⟨.hall 6 23, 2772299700380951821080⟩, ⟨.hall 3 24, 565387872305016925164⟩, ⟨.hall 2 27, 72981538689905139294000⟩]
  caps := #[0, 131792579190564259968000, 18493782932494657788000, 4772377921897640854800, 0, 639662328973179512000, 254894840427731188575, 227426097223517828160, 0, 9170296411065575520, 313385711778307759500, 234036241336948050, 0, 2047831036051326926400, 98295221361518181000, 0, 4498637133250260000000, 1349591139975078000000] }

theorem case_48_31_19_checked :
    (Witness.linear .negative case_48_31_19).check 48 31 19 = true := by
  change case_48_31_19.check 48 31 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_31_20 : Certificate := {
  objectiveScale := 8320466663530560000
  eta := 274216798183893642277200000
  rows := #[⟨.count 2, 32723204583277974645079200⟩, ⟨.count 3, 3546537256511691106785120⟩, ⟨.count 4, 323836980712407729927360⟩, ⟨.count 5, 22098056996504249560800⟩, ⟨.count 6, 1004457136204738616400⟩, ⟨.path 5, 12701239258003219123200⟩, ⟨.path 6, 333960724503566899200⟩, ⟨.path 7, 33185498191572272000⟩, ⟨.hall 14 8, 250666665006530136⟩, ⟨.hall 12 9, 139178715099056640⟩, ⟨.hall 13 9, 241714284113439774⟩, ⟨.hall 11 10, 236495082297225150⟩, ⟨.hall 9 11, 152317330782235815⟩, ⟨.hall 10 11, 217725631321254900⟩, ⟨.hall 8 12, 63706199302587520⟩, ⟨.hall 12 12, 231239636023953480⟩]
  caps := #[0, 0, 0, 0, 644481053346028664640, 0, 0, 33185498191572272000, 0, 0, 319599997883325923400, 0, 131016148200618080400, 2530220630512989173760, 0, 0, 13628924394863057280000, 5300137264668966720000] }

theorem case_48_31_20_checked :
    (Witness.linear .negative case_48_31_20).check 48 31 20 = true := by
  change case_48_31_20.check 48 31 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_32_1_checked :
    (Witness.rising).check 48 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_32_2_checked :
    (Witness.rising).check 48 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_32_3_checked :
    (Witness.rising).check 48 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_32_4_checked :
    (Witness.rising).check 48 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_32_5_checked :
    (Witness.rising).check 48 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_32_6_checked :
    (Witness.rising).check 48 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_32_7_checked :
    (Witness.rising).check 48 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_32_8_checked :
    (Witness.rising).check 48 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_32_9_checked :
    (Witness.rising).check 48 32 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_32_10_checked :
    (Witness.linear .positive case_48_32_10).check 48 32 10 = true := by
  change case_48_32_10.check 48 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_48_32_11_checked :
    (Witness.linear .positive case_48_32_11).check 48 32 11 = true := by
  change case_48_32_11.check 48 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_48_32_12_checked :
    (Witness.linear .positive case_48_32_12).check 48 32 12 = true := by
  change case_48_32_12.check 48 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_48_32_13_checked :
    (Witness.linear .positive case_48_32_13).check 48 32 13 = true := by
  change case_48_32_13.check 48 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_48_32_14_checked :
    (Witness.linear .positive case_48_32_14).check 48 32 14 = true := by
  change case_48_32_14.check 48 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_32_15 : Certificate := {
  objectiveScale := 817
  eta := 574707440
  rows := #[⟨.assumptionRow 15, 2073⟩]
  caps := #[0, 0, 164205448, 47973898, 14234610, 4301102, 1328756, 421993, 138831, 47850, 17584, 2085573, 1057635, 336870, 75054, 10999, 817] }

theorem case_48_32_15_checked :
    (Witness.linear .conditional case_48_32_15).check 48 32 15 = true := by
  change case_48_32_15.check 48 32 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_32_16 : Certificate := {
  objectiveScale := 5852124210240000
  eta := 250342507850098866602400
  rows := #[⟨.count 2, 32058927558958046947200⟩, ⟨.count 3, 3980425669610127257520⟩, ⟨.count 4, 472490981476563329280⟩, ⟨.count 5, 51808221653131944000⟩, ⟨.count 6, 5651805998523484800⟩, ⟨.count 7, 989066049741609840⟩, ⟨.path 6, 2583332979475248000⟩, ⟨.privateRow 2 30, 2310128603513153382960⟩, ⟨.privateRow 3 26, 166692953168952029820⟩, ⟨.privateRow 3 27, 502885138179734069760⟩, ⟨.privateRow 3 28, 737490035232333222840⟩, ⟨.privateRow 4 23, 43259865080365173240⟩, ⟨.privateRow 4 24, 122474635988003915616⟩, ⟨.privateRow 4 25, 200497817797620623280⟩, ⟨.privateRow 4 26, 277692068060787219840⟩, ⟨.privateRow 4 27, 398664265620850309080⟩, ⟨.privateRow 5 20, 7317911308504887090⟩, ⟨.privateRow 5 21, 27680392711816210080⟩, ⟨.privateRow 5 22, 51203792400512071320⟩, ⟨.privateRow 5 23, 76676168046635277120⟩, ⟨.privateRow 5 24, 104134525522795207440⟩, ⟨.privateRow 5 25, 153179642021093447760⟩, ⟨.privateRow 5 26, 130038636349361179440⟩, ⟨.privateRow 6 17, 730024941475950120⟩, ⟨.privateRow 6 18, 5259319470848242800⟩, ⟨.privateRow 6 19, 12922618923707342850⟩, ⟨.privateRow 6 20, 21497047815812540400⟩, ⟨.privateRow 6 21, 31516668172321932600⟩, ⟨.privateRow 6 22, 41682069239110700400⟩, ⟨.privateRow 6 23, 60698041504976175300⟩, ⟨.privateRow 6 24, 48668329431730008000⟩, ⟨.privateRow 7 15, 629405668017388080⟩, ⟨.privateRow 7 16, 2938939119232212096⟩, ⟨.privateRow 7 17, 6138489292840784880⟩, ⟨.privateRow 7 18, 9961308072397641960⟩, ⟨.privateRow 7 19, 14311180189118395440⟩, ⟨.privateRow 7 20, 18721607370109043400⟩, ⟨.privateRow 7 21, 26620006253045613408⟩, ⟨.privateRow 8 13, 421268873038093080⟩, ⟨.privateRow 8 14, 1658433982395022560⟩, ⟨.privateRow 8 15, 3285897209697126024⟩, ⟨.privateRow 8 16, 5262808239983133840⟩, ⟨.privateRow 8 17, 7500417543873874620⟩, ⟨.privateRow 8 18, 9231283130921691840⟩, ⟨.privateRow 9 11, 278967347363018160⟩, ⟨.privateRow 9 12, 1025698125657965760⟩, ⟨.privateRow 9 13, 2048066062596262800⟩, ⟨.privateRow 9 14, 3296886832472032800⟩, ⟨.privateRow 9 15, 2478770470340083920⟩, ⟨.privateRow 10 9, 201850214232981600⟩, ⟨.privateRow 10 10, 739082322883840320⟩, ⟨.privateRow 10 11, 1542472053763701060⟩, ⟨.privateRow 10 12, 423885449889261360⟩, ⟨.privateRow 11 7, 172694072177106480⟩, ⟨.privateRow 11 8, 639192345071108400⟩, ⟨.privateRow 11 9, 54344288447341200⟩, ⟨.privateRow 12 5, 161900692666037325⟩, ⟨.privateRow 12 6, 69077628870842592⟩, ⟨.privateRow 13 3, 91426273505526960⟩, ⟨.hall 4 27, 35081567233692202080⟩, ⟨.hall 3 28, 200658601933785515520⟩, ⟨.hall 2 29, 603462165815680883712⟩, ⟨.assumptionRow 16, 6328524449317840⟩]
  caps := #[0, 0, 0, 0, 2212944936274095408, 2685256766923559400, 15453472112958880, 414464540282631436, 400472871011043600, 651118986409367280, 110146710534653760, 19461973587031360, 4169450818876242207, 0, 3025607550731211600, 595146389829474560, 81453338704282160] }

theorem case_48_32_16_checked :
    (Witness.linear .conditional case_48_32_16).check 48 32 16 = true := by
  change case_48_32_16.check 48 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_32_17 : Certificate := {
  objectiveScale := 19259584614408600000
  eta := 1042660044277065256874832000
  rows := #[⟨.count 2, 115933866827949874990606320⟩, ⟨.count 3, 11862917850703344504239160⟩, ⟨.count 4, 1063938820690882915178400⟩, ⟨.count 5, 95481689036361287259600⟩, ⟨.count 7, 2604046064628035107080⟩, ⟨.path 5, 48054715994362534657200⟩, ⟨.path 6, 470651295118872067200⟩, ⟨.privateRow 2 30, 8812959898056146814061080⟩, ⟨.privateRow 3 26, 616197900316803021707490⟩, ⟨.privateRow 3 27, 1761409825366017270684240⟩, ⟨.privateRow 3 28, 2739642463279023506584380⟩, ⟨.privateRow 4 23, 137766437038178428760280⟩, ⟨.privateRow 4 24, 398567850520353830532216⟩, ⟨.privateRow 4 25, 691560233449073894865960⟩, ⟨.privateRow 4 26, 1031202241592701902403680⟩, ⟨.privateRow 4 27, 1589770122455415432872340⟩, ⟨.privateRow 5 20, 17732313678181381919640⟩, ⟨.privateRow 5 21, 79697981256881156100360⟩, ⟨.privateRow 5 22, 160727509877874833553660⟩, ⟨.privateRow 5 23, 262438242437084452410672⟩, ⟨.privateRow 5 24, 388405870758626807816730⟩, ⟨.privateRow 5 25, 626996424672105786338040⟩, ⟨.privateRow 5 26, 615174882219984865058280⟩, ⟨.privateRow 6 12, 289338451625337234120⟩, ⟨.privateRow 6 17, 372006580661147872440⟩, ⟨.privateRow 6 18, 11917988602662700357800⟩, ⟨.privateRow 6 19, 35650630646693337775500⟩, ⟨.privateRow 6 20, 65898308574260480260800⟩, ⟨.privateRow 6 21, 106538551294900960134900⟩, ⟨.privateRow 6 22, 155870757297020958552360⟩, ⟨.privateRow 6 23, 194373438395449763349900⟩, ⟨.privateRow 6 24, 390813580016794792657800⟩, ⟨.privateRow 6 25, 58281030970246500015600⟩, ⟨.privateRow 7 15, 338187800601043520400⟩, ⟨.privateRow 7 16, 6361312529305628618724⟩, ⟨.privateRow 7 17, 16244287355536790429880⟩, ⟨.privateRow 7 18, 29667524807726542827090⟩, ⟨.privateRow 7 19, 47457410932915007155560⟩, ⟨.privateRow 7 20, 69131222906196646295100⟩, ⟨.privateRow 7 21, 111750776830608820880976⟩, ⟨.privateRow 7 22, 107137895230410587262720⟩, ⟨.privateRow 8 13, 96446150541779078040⟩, ⟨.privateRow 8 14, 3340543941492529884840⟩, ⟨.privateRow 8 15, 8217212026159577449008⟩, ⟨.privateRow 8 16, 15077748201364795866920⟩, ⟨.privateRow 8 17, 24015091484902990431960⟩, ⟨.privateRow 8 18, 32157902194930338306480⟩, ⟨.privateRow 8 19, 61966651723093057640700⟩, ⟨.privateRow 9 12, 1832476860293802482760⟩, ⟨.privateRow 9 13, 4787236199619216055440⟩, ⟨.privateRow 9 14, 8911624310060386810896⟩, ⟨.privateRow 9 15, 12473702136736760759840⟩, ⟨.privateRow 9 16, 24485266468794163437405⟩, ⟨.privateRow 10 10, 1058787960343267021560⟩, ⟨.privateRow 10 11, 3255057580785043883850⟩, ⟨.privateRow 10 12, 6324111871239513831480⟩, ⟨.privateRow 10 13, 7737736877751875746752⟩, ⟨.privateRow 11 8, 708583963164091185600⟩, ⟨.privateRow 11 9, 2527737022441132979400⟩, ⟨.privateRow 11 10, 2945052096900753990150⟩, ⟨.privateRow 12 6, 545609651636350212912⟩, ⟨.privateRow 12 7, 1461454424025938070300⟩, ⟨.privateRow 13 4, 511509048409078324605⟩, ⟨.hall 4 27, 231494380765708590335520⟩, ⟨.hall 3 28, 891507356647877753063280⟩, ⟨.hall 2 29, 2374947878631093085103784⟩, ⟨.assumptionRow 17, 15768207115508608992⟩]
  caps := #[0, 570788028000246172901400, 109227853868499216968040, 0, 4047380360868240396000, 4341138829262486615760, 616697545102379991900, 154521188128169350488, 2037236245168631824100, 905681703645708173464, 253217094566860058976, 5324718177039390740820, 15768207115508608992, 3206348357932589237676, 32764186557150690638304, 8600797383492753929952, 1766473693165865265120] }

theorem case_48_32_17_checked :
    (Witness.linear .conditional case_48_32_17).check 48 32 17 = true := by
  change case_48_32_17.check 48 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_32_18 : Certificate := {
  objectiveScale := 70104887996447304000
  eta := 4215325607577278109936820800
  rows := #[⟨.count 2, 480616629933428175549922560⟩, ⟨.count 3, 50324306218678761887938320⟩, ⟨.count 4, 4583121073745341788460800⟩, ⟨.count 5, 327365790981810127747200⟩, ⟨.count 6, 14880263226445914897600⟩, ⟨.path 5, 161035495364430021535200⟩, ⟨.path 6, 9160481304996583161600⟩, ⟨.privateRow 2 30, 38727373073148138112493760⟩, ⟨.privateRow 3 26, 2189940739255400667075540⟩, ⟨.privateRow 3 27, 7447571744836180406248800⟩, ⟨.privateRow 3 28, 12075705614841521087274840⟩, ⟨.privateRow 4 23, 486956614085442565023960⟩, ⟨.privateRow 4 24, 1553350678208689056160464⟩, ⟨.privateRow 4 25, 2911509503544473823651660⟩, ⟨.privateRow 4 26, 4547656446388979024621520⟩, ⟨.privateRow 4 27, 7341177862767092114730960⟩, ⟨.privateRow 5 20, 67178188357725619964790⟩, ⟨.privateRow 5 21, 290732000086226613451680⟩, ⟨.privateRow 5 22, 628360448801196661870320⟩, ⟨.privateRow 5 23, 1084671987453064223269056⟩, ⟨.privateRow 5 24, 1699574064847230913220880⟩, ⟨.privateRow 5 25, 2911736840899322302907040⟩, ⟨.privateRow 5 26, 3111339038456287089130680⟩, ⟨.privateRow 6 17, 5208092129256070214160⟩, ⟨.privateRow 6 18, 43125207313681216323600⟩, ⟨.privateRow 6 19, 128807278553922450832350⟩, ⟨.privateRow 6 20, 251901598904834416480800⟩, ⟨.privateRow 6 21, 431114292921752478838800⟩, ⟨.privateRow 6 22, 670603862738495898051840⟩, ⟨.privateRow 6 23, 1165310613921045710418300⟩, ⟨.privateRow 6 24, 1405358193608780851440000⟩, ⟨.privateRow 6 25, 1046578513593362681131200⟩, ⟨.privateRow 7 15, 3720065806611478724400⟩, ⟨.privateRow 7 16, 22245993523536642771912⟩, ⟨.privateRow 7 17, 57371681550852582994080⟩, ⟨.privateRow 7 18, 110020946230534483274130⟩, ⟨.privateRow 7 19, 186641015897421618287040⟩, ⟨.privateRow 7 20, 290165132915695340503200⟩, ⟨.privateRow 7 21, 507268173389541238859184⟩, ⟨.privateRow 7 22, 656219608286264846984160⟩, ⟨.privateRow 7 23, 226924014203300202188400⟩, ⟨.privateRow 8 13, 2121815311919139716880⟩, ⟨.privateRow 8 14, 11573538065013489364800⟩, ⟨.privateRow 8 15, 28239432878632914050112⟩, ⟨.privateRow 8 16, 54009844303396283702400⟩, ⟨.privateRow 8 17, 91213946874887563056330⟩, ⟨.privateRow 8 18, 141527836909307812803840⟩, ⟨.privateRow 8 19, 248831068397790021343200⟩, ⟨.privateRow 8 20, 235637235003674643467328⟩, ⟨.privateRow 9 11, 1290894630328427659920⟩, ⟨.privateRow 9 12, 6606561312111866845740⟩, ⟨.privateRow 9 13, 16150346299814278340880⟩, ⟨.privateRow 9 14, 30901346633586016604016⟩, ⟨.privateRow 9 15, 52209516159949740912320⟩, ⟨.privateRow 9 16, 80942431842188091245070⟩, ⟨.privateRow 9 17, 122266162843963934075280⟩, ⟨.privateRow 10 9, 850300755796909422720⟩, ⟨.privateRow 10 10, 4406847186293597873520⟩, ⟨.privateRow 10 11, 11036195226280720215720⟩, ⟨.privateRow 10 12, 21441106558106159193360⟩, ⟨.privateRow 10 13, 36307842272528032350144⟩, ⟨.privateRow 10 14, 40838055743690455330080⟩, ⟨.privateRow 11 7, 744013161322295744880⟩, ⟨.privateRow 11 8, 3454346820424944529800⟩, ⟨.privateRow 11 9, 9252471365161882981200⟩, ⟨.privateRow 11 10, 18496993871762630324100⟩, ⟨.privateRow 11 11, 9131070616228175050800⟩, ⟨.privateRow 12 5, 682012064545437766140⟩, ⟨.privateRow 12 6, 3455527793696884681776⟩, ⟨.privateRow 12 7, 9743029493506253802000⟩, ⟨.privateRow 13 3, 962840561711206258080⟩, ⟨.privateRow 13 4, 3580563338863548272235⟩, ⟨.privateRow 14 1, 1970257075353486879960⟩, ⟨.hall 4 27, 1356229705496070529238400⟩, ⟨.hall 3 28, 4395167955819578387530080⟩, ⟨.hall 2 29, 10890004906893792682914912⟩, ⟨.assumptionRow 18, 32325286816823394240⟩]
  caps := #[0, 737721157359474041292000, 56870412457735920859200, 24785892075440410318404, 713796392814745030560, 459601399945028976492, 6343367979222678968850, 2166841938130191241920, 3091311094425649734870, 4744700974252072462048, 434583172168745917680, 0, 23053789115902167761556, 39690350347094771288580, 0, 101593353565608490333440, 27484320889487180759040] }

theorem case_48_32_18_checked :
    (Witness.linear .conditional case_48_32_18).check 48 32 18 = true := by
  change case_48_32_18.check 48 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_32_19 : Certificate := {
  objectiveScale := 20685194841854400000
  eta := 1485021973879332824046111000
  rows := #[⟨.count 2, 192716978441885980132050000⟩, ⟨.count 3, 23692389349671860088070800⟩, ⟨.count 4, 2642975704345864870382400⟩, ⟨.count 5, 248081510710120100013000⟩, ⟨.count 6, 16502096056105549890000⟩, ⟨.path 6, 14960829760363062576000⟩, ⟨.path 7, 20147641753995756000⟩, ⟨.privateRow 4 23, 43565533588118651709600⟩, ⟨.privateRow 5 22, 344288730717215455871700⟩, ⟨.privateRow 5 24, 871008133334677765777350⟩, ⟨.privateRow 5 25, 439689181583790095958000⟩, ⟨.privateRow 6 17, 1815230566171610487900⟩, ⟨.privateRow 6 18, 7150908290979071619000⟩, ⟨.privateRow 6 21, 412460723091215938639500⟩, ⟨.privateRow 7 17, 20499270434140005307800⟩, ⟨.privateRow 7 19, 78172786460065719193200⟩, ⟨.privateRow 7 21, 483709439596565878375680⟩, ⟨.privateRow 7 24, 587969682479040742580700⟩, ⟨.privateRow 8 12, 19746097844912623800⟩, ⟨.privateRow 8 13, 85566423994621369800⟩, ⟨.privateRow 8 14, 536734841420806774200⟩, ⟨.privateRow 8 15, 8188706776285265089860⟩, ⟨.privateRow 8 16, 10410581586012266659000⟩, ⟨.privateRow 8 17, 16589190451957218069975⟩, ⟨.privateRow 8 18, 8287719352621898389200⟩, ⟨.privateRow 8 19, 4620586895709553969200⟩, ⟨.privateRow 8 21, 468861220278527795819100⟩, ⟨.privateRow 9 10, 18335662284561722100⟩, ⟨.privateRow 9 11, 59238293534737871400⟩, ⟨.privateRow 9 12, 320874089979830136750⟩, ⟨.privateRow 9 13, 3407099428149469088400⟩, ⟨.privateRow 9 14, 7136239761151422241320⟩, ⟨.privateRow 9 16, 33499254993894266276700⟩, ⟨.privateRow 10 8, 22002794741474066520⟩, ⟨.privateRow 10 9, 47148845874587285400⟩, ⟨.privateRow 10 10, 203102720690529844800⟩, ⟨.privateRow 10 12, 420053354155413997200⟩, ⟨.privateRow 10 13, 462058689570955396920⟩, ⟨.privateRow 10 14, 586741193105975107200⟩, ⟨.privateRow 10 15, 3712971612623748725250⟩, ⟨.privateRow 10 18, 115250638855841160431760⟩, ⟨.privateRow 13 16, 1815230566171610487900⟩, ⟨.privateRow 13 18, 1815230566171610487900⟩, ⟨.hall 11 5, 2973496758516570000⟩, ⟨.hall 10 6, 1990522623469770000⟩, ⟨.hall 10 7, 1141785893740298625⟩, ⟨.hall 11 7, 822171853729831605⟩, ⟨.hall 12 8, 547580864606820660⟩, ⟨.hall 13 8, 624434319288479700⟩, ⟨.hall 8 10, 542780687945420925⟩, ⟨.hall 7 12, 59136151344474204⟩, ⟨.hall 14 16, 719764625366520934200⟩, ⟨.hall 5 18, 1754491465919336760⟩, ⟨.hall 4 21, 13011049032504094440⟩, ⟨.hall 3 25, 3602641506808023880200⟩, ⟨.hall 2 27, 38407775013893110185360⟩]
  caps := #[0, 0, 0, 35027068900648995490320, 2066769903346131297600, 0, 629828234834620186200, 20147641753995756000, 3284931631490788142353, 2863265394408229442310, 11943135740818620000, 2731747946163688452000, 3647999591919758275200, 0, 44481225793377862288800, 41909407076547197187000, 26063345500736544000000] }

theorem case_48_32_19_checked :
    (Witness.linear .negative case_48_32_19).check 48 32 19 = true := by
  change case_48_32_19.check 48 32 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_32_20 : Certificate := {
  objectiveScale := 901896256954000000
  eta := 60458017756213246113945000
  rows := #[⟨.count 2, 7661582427159059153554800⟩, ⟨.count 3, 904959456679601560036800⟩, ⟨.count 4, 95011335888398916386400⟩, ⟨.count 5, 8231180089341490281000⟩, ⟨.count 6, 427593770874882612000⟩, ⟨.path 5, 698666621316517854000⟩, ⟨.path 6, 445647532734508104000⟩, ⟨.hall 13 7, 20225023562193450⟩, ⟨.hall 12 8, 16802327267053020⟩, ⟨.hall 9 10, 10147291222056300⟩, ⟨.hall 11 10, 25114589698108350⟩, ⟨.hall 10 11, 25053975241878000⟩, ⟨.hall 12 12, 18669252518947800⟩, ⟨.hall 13 12, 20225023562193450⟩, ⟨.hall 8 13, 22516659960544750⟩, ⟨.hall 9 13, 18818273039798700⟩, ⟨.hall 7 14, 16701765834402649⟩]
  caps := #[0, 26390393686284556929000, 1638785636314271645200, 349164685801017209200, 293502125473410453600, 0, 18053761859625492000, 0, 0, 124714849838507428500, 0, 104144215531120765000, 63189840904077430400, 98387880709036999080, 0, 5580934038031352000000, 2298031662718792000000] }

theorem case_48_32_20_checked :
    (Witness.linear .negative case_48_32_20).check 48 32 20 = true := by
  change case_48_32_20.check 48 32 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_33_1_checked :
    (Witness.rising).check 48 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_33_2_checked :
    (Witness.rising).check 48 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_33_3_checked :
    (Witness.rising).check 48 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_33_4_checked :
    (Witness.rising).check 48 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_33_5_checked :
    (Witness.rising).check 48 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_33_6_checked :
    (Witness.rising).check 48 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_33_7_checked :
    (Witness.rising).check 48 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_33_8_checked :
    (Witness.rising).check 48 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_33_9_checked :
    (Witness.rising).check 48 33 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_48_33_10_checked :
    (Witness.linear .positive case_48_33_10).check 48 33 10 = true := by
  change case_48_33_10.check 48 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_48_33_11_checked :
    (Witness.linear .positive case_48_33_11).check 48 33 11 = true := by
  change case_48_33_11.check 48 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_48_33_12_checked :
    (Witness.linear .positive case_48_33_12).check 48 33 12 = true := by
  change case_48_33_12.check 48 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_48_33_13_checked :
    (Witness.linear .positive case_48_33_13).check 48 33 13 = true := by
  change case_48_33_13.check 48 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_48_33_14_checked :
    (Witness.linear .positive case_48_33_14).check 48 33 14 = true := by
  change case_48_33_14.check 48 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_48_33_15_checked :
    (Witness.linear .positive case_48_33_15).check 48 33 15 = true := by
  change case_48_33_15.check 48 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_16 : Certificate := {
  objectiveScale := 689
  eta := 1187414215
  rows := #[⟨.assumptionRow 16, 1476⟩]
  caps := #[0, 0, 339059560, 97856726, 28595190, 8478444, 2557672, 787787, 248897, 81165, 28920, 5192187, 3026016, 1150545, 325470, 67923] }

theorem case_48_33_16_checked :
    (Witness.linear .conditional case_48_33_16).check 48 33 16 = true := by
  change case_48_33_16.check 48 33 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_17 : Certificate := {
  objectiveScale := 526216748238720000
  eta := 44639526551676187044513600
  rows := #[⟨.count 2, 4774630678787343083149440⟩, ⟨.count 3, 493059859347902657690880⟩, ⟨.count 4, 44442470315372178329280⟩, ⟨.count 5, 3811532617098814608000⟩, ⟨.path 5, 1768144647264512967450⟩, ⟨.path 6, 36020608498895248800⟩, ⟨.privateRow 2 30, 106284587027800445344080⟩, ⟨.privateRow 2 31, 430588839753653086265760⟩, ⟨.privateRow 3 27, 52408573485108700860000⟩, ⟨.privateRow 3 28, 99785923915646966437440⟩, ⟨.privateRow 3 29, 140035708352210448697920⟩, ⟨.privateRow 3 30, 211311368291958281867520⟩, ⟨.privateRow 4 23, 2066395183127143062480⟩, ⟨.privateRow 4 24, 8909457492468479146200⟩, ⟨.privateRow 4 25, 25743091295885393862432⟩, ⟨.privateRow 4 26, 37105270027456960208880⟩, ⟨.privateRow 4 27, 50941133427525657235920⟩, ⟨.privateRow 4 28, 73476820026122398605720⟩, ⟨.privateRow 5 20, 491264203981624993920⟩, ⟨.privateRow 5 21, 1667545519980731391000⟩, ⟨.privateRow 5 22, 5238134825212942361280⟩, ⟨.privateRow 5 23, 9998920565522556988320⟩, ⟨.privateRow 5 24, 14575300727785867060992⟩, ⟨.privateRow 5 25, 19591277651887907085120⟩, ⟨.privateRow 5 26, 28993058107398316451520⟩, ⟨.privateRow 5 27, 23669617552183638715680⟩, ⟨.privateRow 6 14, 2722523297927724720⟩, ⟨.privateRow 6 15, 23455585335992705280⟩, ⟨.privateRow 6 17, 10395088955724039840⟩, ⟨.privateRow 6 18, 289676478899509910208⟩, ⟨.privateRow 6 19, 1067229132787668090240⟩, ⟨.privateRow 6 20, 2453674122257361903900⟩, ⟨.privateRow 6 21, 4192685878808696068800⟩, ⟨.privateRow 6 22, 6212798165871067811040⟩, ⟨.privateRow 6 23, 8271025779104427699360⟩, ⟨.privateRow 6 24, 12206433206258953782120⟩, ⟨.privateRow 6 25, 6543130992686298410400⟩, ⟨.privateRow 7 12, 5082043489465086144⟩, ⟨.privateRow 7 15, 8470072482441810240⟩, ⟨.privateRow 7 16, 203281739578603445760⟩, ⟨.privateRow 7 17, 599681131756880164992⟩, ⟨.privateRow 7 18, 1219690437471620674560⟩, ⟨.privateRow 7 19, 2013759732700540384560⟩, ⟨.privateRow 7 20, 2962105348145364495360⟩, ⟨.privateRow 7 21, 3963993921782767192320⟩, ⟨.privateRow 7 22, 4380721487918904256128⟩, ⟨.privateRow 8 13, 5130909292248404280⟩, ⟨.privateRow 8 14, 140814955020595095240⟩, ⟨.privateRow 8 15, 365849380747287735480⟩, ⟨.privateRow 8 16, 702592512418548159408⟩, ⟨.privateRow 8 17, 1138871829201655068520⟩, ⟨.privateRow 8 18, 1661987034914128953030⟩, ⟨.privateRow 8 19, 1524613046839525843200⟩, ⟨.privateRow 9 11, 1815015531951816480⟩, ⟨.privateRow 9 12, 103595501900634448320⟩, ⟨.privateRow 9 13, 262572246955696117440⟩, ⟨.privateRow 9 14, 489724190802999210240⟩, ⟨.privateRow 9 15, 787716740867088352320⟩, ⟨.privateRow 9 16, 290805821897168818240⟩, ⟨.privateRow 10 10, 87120745533687191040⟩, ⟨.privateRow 10 11, 231623905192927964640⟩, ⟨.privateRow 10 12, 336685381177061957040⟩, ⟨.privateRow 11 8, 86394739320906464448⟩, ⟨.privateRow 11 9, 130681118300530786560⟩, ⟨.privateRow 12 6, 65510716856385876075⟩, ⟨.hall 4 28, 1619244201470944688640⟩, ⟨.hall 3 29, 25239968990428350334176⟩, ⟨.assumptionRow 17, 468668682333717888⟩]
  caps := #[0, 24022472370614625291120, 0, 0, 832675983367711066320, 16038209292603967194, 129477460533189872256, 342069927255185679264, 29766161383181828880, 8444320437100622976, 234904894808379325200, 1817126663429869440, 468668682333717888, 3872526851430091704960, 1155714478627652165376, 285611431967219445120] }

theorem case_48_33_17_checked :
    (Witness.linear .conditional case_48_33_17).check 48 33 17 = true := by
  change case_48_33_17.check 48 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_18 : Certificate := {
  objectiveScale := 50392021680000
  eta := 4564292901127529169600
  rows := #[⟨.count 2, 481161911744478444480⟩, ⟨.count 3, 47883936785498573760⟩, ⟨.count 4, 3953266194881203200⟩, ⟨.count 5, 224617397436432000⟩, ⟨.path 5, 200290056952986000⟩, ⟨.privateRow 2 30, 13972325207533252560⟩, ⟨.privateRow 2 31, 48822837506782859520⟩, ⟨.privateRow 3 27, 5411033104243646880⟩, ⟨.privateRow 3 28, 11019729518231353920⟩, ⟨.privateRow 3 29, 15961312261832857920⟩, ⟨.privateRow 3 30, 25152656164931655360⟩, ⟨.privateRow 4 23, 190603905824629440⟩, ⟨.privateRow 4 24, 848305037651591520⟩, ⟨.privateRow 4 25, 2623980436852398624⟩, ⟨.privateRow 4 26, 4021212957605723880⟩, ⟨.privateRow 4 27, 5835185623069442640⟩, ⟨.privateRow 4 28, 8882494981623703440⟩, ⟨.privateRow 5 20, 47918378119772160⟩, ⟨.privateRow 5 21, 144878221346498640⟩, ⟨.privateRow 5 22, 489024162418746240⟩, ⟨.privateRow 5 23, 1004039766540851040⟩, ⟨.privateRow 5 24, 1557047799029346624⟩, ⟨.privateRow 5 25, 2238312365454044880⟩, ⟨.privateRow 5 26, 3568421720606783040⟩, ⟨.privateRow 5 27, 3304121916289914720⟩, ⟨.privateRow 6 17, 5921731386960480⟩, ⟨.privateRow 6 18, 24707913718007520⟩, ⟨.privateRow 6 19, 89846958974572800⟩, ⟨.privateRow 6 20, 224617397436432000⟩, ⟨.privateRow 6 21, 412333365294021600⟩, ⟨.privateRow 6 22, 652887901881895680⟩, ⟨.privateRow 6 23, 935306842925302848⟩, ⟨.privateRow 6 24, 1504375019330503320⟩, ⟨.privateRow 6 25, 1516916157354037440⟩, ⟨.privateRow 7 14, 115188408941760⟩, ⟨.privateRow 7 15, 2870111189465520⟩, ⟨.privateRow 7 16, 16471942478671680⟩, ⟨.privateRow 7 17, 49116337572766464⟩, ⟨.privateRow 7 18, 108648267056288960⟩, ⟨.privateRow 7 19, 192422237137210080⟩, ⟨.privateRow 7 20, 303982211197304640⟩, ⟨.privateRow 7 21, 438752649659163840⟩, ⟨.privateRow 7 22, 710988935352119424⟩, ⟨.privateRow 7 23, 321577240663158480⟩, ⟨.privateRow 8 13, 2015797156480800⟩, ⟨.privateRow 8 14, 10918901264271000⟩, ⟨.privateRow 8 15, 29302360483752720⟩, ⟨.privateRow 8 16, 60403361793947172⟩, ⟨.privateRow 8 17, 105258208187572440⟩, ⟨.privateRow 8 18, 164930003596813455⟩, ⟨.privateRow 8 19, 238468803611678640⟩, ⟨.privateRow 8 20, 211608306501571980⟩, ⟨.privateRow 9 11, 1604409981688800⟩, ⟨.privateRow 9 12, 8178377034864960⟩, ⟨.privateRow 9 13, 20589928098339600⟩, ⟨.privateRow 9 14, 40703395050601920⟩, ⟨.privateRow 9 15, 34441334273586240⟩, ⟨.privateRow 9 16, 180193067721226560⟩, ⟨.privateRow 9 17, 18156572959444920⟩, ⟨.privateRow 10 9, 1497449316242880⟩, ⟨.privateRow 10 10, 7380285915768480⟩, ⟨.privateRow 10 11, 17969391794914560⟩, ⟨.privateRow 10 12, 34815696602646960⟩, ⟨.privateRow 10 13, 47169653461650720⟩, ⟨.privateRow 11 7, 1684630480773240⟩, ⟨.privateRow 11 8, 8086226307711552⟩, ⟨.privateRow 11 9, 20215565769278880⟩, ⟨.privateRow 11 10, 7948000216981440⟩, ⟨.privateRow 12 5, 2906813378589120⟩, ⟨.privateRow 12 6, 10037589947940555⟩, ⟨.privateRow 13 3, 2745323746445280⟩, ⟨.hall 4 28, 557206054192307520⟩, ⟨.hall 3 29, 3419575258572240768⟩, ⟨.assumptionRow 18, 29283191429184⟩]
  caps := #[0, 0, 77631861521934720, 7463246209073424, 34393130651099880, 12872606588959104, 4125460906072800, 26047938875363328, 991458245772456, 183873509753472, 29283191429184, 49563819500546736, 0, 250325447035555584, 305512714578722112, 93664940732371008] }

theorem case_48_33_18_checked :
    (Witness.linear .conditional case_48_33_18).check 48 33 18 = true := by
  change case_48_33_18.check 48 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_19 : Certificate := {
  objectiveScale := 1853508937280000
  eta := 163195240292977919906880
  rows := #[⟨.count 2, 20416925281428958201920⟩, ⟨.count 3, 2495961029387856270240⟩, ⟨.count 4, 276730020536882552640⟩, ⟨.count 5, 25320633520198816800⟩, ⟨.count 6, 1470230333430899040⟩, ⟨.path 6, 1559052958815752400⟩, ⟨.privateRow 2 30, 1354898931719541848640⟩, ⟨.privateRow 2 31, 2943401127528659878080⟩, ⟨.privateRow 3 27, 305481191501753467200⟩, ⟨.privateRow 3 28, 681642344958814599360⟩, ⟨.privateRow 3 29, 902067989022824944320⟩, ⟨.privateRow 4 23, 5005784230490918160⟩, ⟨.privateRow 4 24, 47469381228458749560⟩, ⟨.privateRow 4 26, 534592085128068567600⟩, ⟨.privateRow 4 27, 201407942436205104600⟩, ⟨.privateRow 4 28, 518194932937165624140⟩, ⟨.privateRow 5 20, 1542834300513906400⟩, ⟨.privateRow 5 21, 7289892069928207740⟩, ⟨.privateRow 5 23, 84810509048837972400⟩, ⟨.privateRow 5 24, 76027244130971157024⟩, ⟨.privateRow 5 25, 187209329123534477760⟩, ⟨.privateRow 5 26, 179967083407004493600⟩, ⟨.privateRow 5 27, 217512409884804674640⟩, ⟨.privateRow 6 17, 311867040424736160⟩, ⟨.privateRow 6 18, 1168016320447880904⟩, ⟨.privateRow 6 19, 4773710835707733920⟩, ⟨.privateRow 6 20, 4308591671582218020⟩, ⟨.privateRow 6 22, 93209880490753386360⟩, ⟨.privateRow 6 23, 24520174783108660656⟩, ⟨.privateRow 6 24, 84967061352860707020⟩, ⟨.privateRow 6 25, 149473417232141402400⟩, ⟨.privateRow 7 15, 254113884790525760⟩, ⟨.privateRow 7 20, 47420762500501378560⟩, ⟨.privateRow 7 23, 126330902724432806400⟩, ⟨.privateRow 8 12, 3403310957015970⟩, ⟨.privateRow 8 13, 3665104107555660⟩, ⟨.privateRow 8 16, 1619976015539601720⟩, ⟨.privateRow 8 18, 7563858601967993325⟩, ⟨.privateRow 8 21, 69296856382376374752⟩, ⟨.privateRow 9 10, 3630198354150368⟩, ⟨.privateRow 9 11, 3889498236589680⟩, ⟨.privateRow 9 12, 12566071225905120⟩, ⟨.privateRow 9 19, 34713771761562894000⟩, ⟨.privateRow 10 8, 5104966435523955⟩, ⟨.privateRow 10 9, 5445297531225552⟩, ⟨.privateRow 10 11, 43981249290667920⟩, ⟨.privateRow 10 12, 20419865742095820⟩, ⟨.privateRow 10 14, 334885798170371448⟩, ⟨.privateRow 10 15, 217811901249022080⟩, ⟨.privateRow 10 16, 428817180584012220⟩, ⟨.privateRow 10 17, 431734304261454480⟩, ⟨.privateRow 10 18, 14593397383684479360⟩, ⟨.privateRow 11 19, 10985887769247551160⟩, ⟨.privateRow 12 18, 449237046326108040⟩, ⟨.privateRow 12 19, 449237046326108040⟩, ⟨.privateRow 12 20, 898474092652216080⟩, ⟨.hall 10 5, 43693136004960⟩, ⟨.hall 9 6, 8495887556520⟩, ⟨.hall 10 6, 61494043266240⟩, ⟨.hall 11 6, 6020895103080⟩, ⟨.hall 11 9, 44253579007638⟩, ⟨.hall 12 10, 30567621292560⟩, ⟨.hall 3 28, 9275970460002534288⟩, ⟨.hall 4 28, 56201103588659309280⟩, ⟨.hall 2 30, 699302674435892567040⟩]
  caps := #[0, 0, 5539934617577440080, 0, 659373905720579764, 174957917788654000, 468343362409664560, 82737401105967960, 0, 971847705805381504, 1533305420914800, 2241946825381222960, 0, 7189014865574873760, 28736802563589120000, 10209127226538240000] }

theorem case_48_33_19_checked :
    (Witness.linear .negative case_48_33_19).check 48 33 19 = true := by
  change case_48_33_19.check 48 33 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_20 : Certificate := {
  objectiveScale := 1312841661502800000
  eta := 91568259593181922142592000
  rows := #[⟨.count 2, 11473284907359996792271200⟩, ⟨.count 3, 1345852167097591438084800⟩, ⟨.count 4, 140454976940091318304800⟩, ⟨.count 5, 12387481005571147476000⟩, ⟨.count 6, 571729892564822191200⟩, ⟨.path 5, 1190227041350825853375⟩, ⟨.path 6, 640111450394380536000⟩, ⟨.hall 12 7, 54085215154910940⟩, ⟨.hall 11 9, 25286594098399920⟩, ⟨.hall 9 10, 40228672429272600⟩, ⟨.hall 13 10, 73752566120333100⟩, ⟨.hall 8 12, 36402922904942880⟩, ⟨.hall 10 12, 43412881729694400⟩, ⟨.hall 9 13, 9314506280207700⟩, ⟨.hall 7 14, 37163235630690477⟩, ⟨.hall 11 14, 49168377413555400⟩, ⟨.hall 12 14, 54085215154910940⟩, ⟨.hall 6 15, 35055536568430840⟩, ⟨.hall 5 19, 148154835278489800⟩]
  caps := #[0, 0, 3632974500515335650675, 561034876799997675075, 106661105989626602700, 0, 68381557829558344800, 68184778891906362400, 0, 28623003561355082880, 0, 312198998472011851200, 158475981341809903200, 9102262075297611105600, 0, 13123165248381988800000] }

theorem case_48_33_20_checked :
    (Witness.linear .negative case_48_33_20).check 48 33 20 = true := by
  change case_48_33_20.check 48 33 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990, 25194, 13260] }

theorem case_48_33_21_checked :
    (Witness.linear .negative case_48_33_21).check 48 33 21 = true := by
  change case_48_33_21.check 48 33 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_34_1_checked :
    (Witness.rising).check 48 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_34_2_checked :
    (Witness.rising).check 48 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_34_3_checked :
    (Witness.rising).check 48 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_34_4_checked :
    (Witness.rising).check 48 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_34_5_checked :
    (Witness.rising).check 48 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_34_6_checked :
    (Witness.rising).check 48 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_34_7_checked :
    (Witness.rising).check 48 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_34_8_checked :
    (Witness.rising).check 48 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_34_9_checked :
    (Witness.rising).check 48 34 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_48_34_10_checked :
    (Witness.linear .positive case_48_34_10).check 48 34 10 = true := by
  change case_48_34_10.check 48 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_48_34_11_checked :
    (Witness.linear .positive case_48_34_11).check 48 34 11 = true := by
  change case_48_34_11.check 48 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_48_34_12_checked :
    (Witness.linear .positive case_48_34_12).check 48 34 12 = true := by
  change case_48_34_12.check 48 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_48_34_13_checked :
    (Witness.linear .positive case_48_34_13).check 48 34 13 = true := by
  change case_48_34_13.check 48 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_48_34_14_checked :
    (Witness.linear .positive case_48_34_14).check 48 34 14 = true := by
  change case_48_34_14.check 48 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_48_34_15_checked :
    (Witness.linear .positive case_48_34_15).check 48 34 15 = true := by
  change case_48_34_15.check 48 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_48_34_16_checked :
    (Witness.linear .positive case_48_34_16).check 48 34 16 = true := by
  change case_48_34_16.check 48 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_17 : Certificate := {
  objectiveScale := 1245129514200000
  eta := 138745966672395857174400
  rows := #[⟨.count 2, 14740665437767151282400⟩, ⟨.count 3, 1454383162628361365400⟩, ⟨.count 4, 127246100352994022400⟩, ⟨.count 5, 7952881272062126400⟩, ⟨.path 5, 5809842294900543900⟩, ⟨.privateRow 2 31, 1224743715897567465600⟩, ⟨.privateRow 2 32, 1793374726850009503200⟩, ⟨.privateRow 3 27, 107894089257642848160⟩, ⟨.privateRow 3 28, 251509870228964747400⟩, ⟨.privateRow 3 29, 505449787513281811200⟩, ⟨.privateRow 3 30, 559518334494870851100⟩, ⟨.privateRow 3 31, 761819751852951191400⟩, ⟨.privateRow 4 23, 2361011627643443775⟩, ⟨.privateRow 4 24, 32805635247256271400⟩, ⟨.privateRow 4 25, 55173113824931001900⟩, ⟨.privateRow 4 26, 125456702066780043960⟩, ⟨.privateRow 4 27, 169744309650576010350⟩, ⟨.privateRow 4 28, 211745463868654115400⟩, ⟨.privateRow 4 29, 267912687852592883100⟩, ⟨.privateRow 5 20, 954345752647455168⟩, ⟨.privateRow 5 21, 6759949081252807440⟩, ⟨.privateRow 5 22, 13867836718158332910⟩, ⟨.privateRow 5 23, 30902624371441405440⟩, ⟨.privateRow 5 24, 49771781960988807720⟩, ⟨.privateRow 5 25, 67122317936204346816⟩, ⟨.privateRow 5 26, 82610554213545337980⟩, ⟨.privateRow 5 27, 109617213533256308880⟩, ⟨.privateRow 5 28, 20677491307361528640⟩, ⟨.privateRow 6 17, 128866131723228900⟩, ⟨.privateRow 6 18, 1305397178495046000⟩, ⟨.privateRow 6 19, 3269517856292207520⟩, ⟨.privateRow 6 20, 8492891728807085600⟩, ⟨.privateRow 6 21, 14828809871865839850⟩, ⟨.privateRow 6 22, 22249132130173806000⟩, ⟨.privateRow 6 23, 30081037033679431800⟩, ⟨.privateRow 6 24, 36715801872686816880⟩, ⟨.privateRow 6 25, 25570722423366420300⟩, ⟨.privateRow 7 15, 203920032616977600⟩, ⟨.privateRow 7 16, 745582619255824350⟩, ⟨.privateRow 7 17, 2364777196427564100⟩, ⟨.privateRow 7 18, 5003687800339087860⟩, ⟨.privateRow 7 19, 8100156851174388000⟩, ⟨.privateRow 7 20, 11763636881591895300⟩, ⟨.privateRow 7 21, 15716408228122773600⟩, ⟨.privateRow 7 22, 7041613626305007750⟩, ⟨.privateRow 8 12, 11045668433419620⟩, ⟨.privateRow 8 13, 142015737001109400⟩, ⟨.privateRow 8 14, 675485108043738300⟩, ⟨.privateRow 8 15, 1794921120430688250⟩, ⟨.privateRow 8 16, 3449261006254217700⟩, ⟨.privateRow 8 17, 5401331863942194180⟩, ⟨.privateRow 8 18, 6259212112271118000⟩, ⟨.privateRow 9 11, 162003137023487760⟩, ⟨.privateRow 9 12, 678519632338633800⟩, ⟨.privateRow 9 13, 1070580171239132400⟩, ⟨.privateRow 9 14, 4123716215143324800⟩, ⟨.privateRow 10 9, 223674785776747305⟩, ⟨.privateRow 10 10, 848307335686626816⟩, ⟨.privateRow 10 11, 937303864207322040⟩, ⟨.privateRow 11 7, 409339477238491800⟩, ⟨.privateRow 11 8, 248527539751941450⟩, ⟨.privateRow 12 5, 202503921279359700⟩, ⟨.hall 3 30, 48679329721735112400⟩, ⟨.assumptionRow 17, 1187278881386400⟩]
  caps := #[0, 225466848546540004800, 26549740652335583760, 0, 2505025162972277055, 689953332073023180, 573005286443068500, 464020429944730860, 19302926787304380, 1085045434636592880, 1261175712315992649, 1187278881386400, 0, 12358257149115108000, 3485289912793920000] }

theorem case_48_34_17_checked :
    (Witness.linear .conditional case_48_34_17).check 48 34 17 = true := by
  change case_48_34_17.check 48 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_18 : Certificate := {
  objectiveScale := 1854054813353600000
  eta := 217215908921810953479124800
  rows := #[⟨.count 2, 22679454204215183594419200⟩, ⟨.count 3, 2136937209582775348148400⟩, ⟨.count 4, 171814047001630178745600⟩, ⟨.count 5, 9762161761456260156000⟩, ⟨.path 4, 6894310917480804417600⟩, ⟨.path 5, 7974789601492931817600⟩, ⟨.privateRow 2 31, 2040291808144358372604000⟩, ⟨.privateRow 2 32, 3114129601904546989764000⟩, ⟨.privateRow 3 27, 142462480638851689876560⟩, ⟨.privateRow 3 28, 394635389206869316806300⟩, ⟨.privateRow 3 29, 844752397758015045499200⟩, ⟨.privateRow 3 30, 996879418540708432930200⟩, ⟨.privateRow 3 31, 1435363184326118784937200⟩, ⟨.privateRow 4 23, 366081066054609755850⟩, ⟨.privateRow 4 24, 43511349565347902409600⟩, ⟨.privateRow 4 25, 78585402179722894255800⟩, ⟨.privateRow 4 26, 196219451405270829135600⟩, ⟨.privateRow 4 27, 286275393654704829074700⟩, ⟨.privateRow 4 28, 382025930264988314104800⟩, ⟨.privateRow 4 29, 522275654237909918346000⟩, ⟨.privateRow 5 20, 351437823412425365616⟩, ⟨.privateRow 5 21, 8070053722803841728960⟩, ⟨.privateRow 5 22, 18059999258694081288600⟩, ⟨.privateRow 5 23, 43846052254312117043520⟩, ⟨.privateRow 5 24, 77836969778011247643840⟩, ⟨.privateRow 5 25, 113006784550617667565856⟩, ⟨.privateRow 5 26, 150825399214499219410200⟩, ⟨.privateRow 5 27, 220104207181633812317280⟩, ⟨.privateRow 5 28, 118903130254537248700080⟩, ⟨.privateRow 6 18, 1262178490370102323200⟩, ⟨.privateRow 6 19, 3753008854959851126640⟩, ⟨.privateRow 6 20, 10870950504732773655200⟩, ⟨.privateRow 6 21, 20907296439118823834100⟩, ⟨.privateRow 6 22, 34276034629113091214400⟩, ⟨.privateRow 6 23, 50184742684819589246400⟩, ⟨.privateRow 6 24, 66773186448360819467040⟩, ⟨.privateRow 6 25, 98977473414764859915000⟩, ⟨.privateRow 6 26, 5351110891464912974400⟩, ⟨.privateRow 7 15, 112640328016803001800⟩, ⟨.privateRow 7 16, 691486458103151761050⟩, ⟨.privateRow 7 17, 2647616598940409951400⟩, ⟨.privateRow 7 18, 6312864605741714900880⟩, ⟨.privateRow 7 19, 11208407948338669068000⟩, ⟨.privateRow 7 20, 17693918192639471532750⟩, ⟨.privateRow 7 21, 25660539487256455267200⟩, ⟨.privateRow 7 22, 34330268861121181548600⟩, ⟨.privateRow 7 23, 14187675093316431426720⟩, ⟨.privateRow 8 13, 69729726867544715400⟩, ⟨.privateRow 8 14, 613264008091483009800⟩, ⟨.privateRow 8 15, 1979549468295297198300⟩, ⟨.privateRow 8 16, 4259852404999095340800⟩, ⟨.privateRow 8 17, 7256540242682486715960⟩, ⟨.privateRow 8 18, 10991471020306307731200⟩, ⟨.privateRow 8 19, 16229593928421032509350⟩, ⟨.privateRow 9 11, 72312309344120445600⟩, ⟨.privateRow 9 12, 604324299518720866800⟩, ⟨.privateRow 9 13, 1768870336263869361600⟩, ⟨.privateRow 9 14, 1771651578930950917200⟩, ⟨.privateRow 9 15, 9604389450159997365600⟩, ⟨.privateRow 9 16, 1279927875390931887120⟩, ⟨.privateRow 10 9, 97621617614562601560⟩, ⟨.privateRow 10 10, 754940509552617452064⟩, ⟨.privateRow 10 11, 2008216133785287803520⟩, ⟨.privateRow 10 12, 2493105926771906439840⟩, ⟨.privateRow 11 7, 172273442849228120400⟩, ⟨.privateRow 11 8, 1159256709172930893525⟩, ⟨.privateRow 11 9, 520648627277667208320⟩, ⟨.privateRow 12 5, 397717701392662450800⟩, ⟨.privateRow 12 6, 210556430149056591600⟩, ⟨.hall 3 30, 122625348061647345314400⟩, ⟨.assumptionRow 18, 1259031883277848680⟩]
  caps := #[0, 0, 39381403477539101893200, 0, 2900155124850370294050, 77793785926282641332, 731949189973983486940, 467600004268589383200, 39537718095603962520, 147444365819797356640, 1571404116337488628096, 1555111467577292646450, 0, 44795535023484325560480, 15097657127991593040600] }

theorem case_48_34_18_checked :
    (Witness.linear .conditional case_48_34_18).check 48 34 18 = true := by
  change case_48_34_18.check 48 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_19 : Certificate := {
  objectiveScale := 6074143424949600000
  eta := 1145269483801116363973483200
  rows := #[⟨.count 2, 110648246269049835112166400⟩, ⟨.count 3, 9514202852715271148037600⟩, ⟨.count 4, 656017270369860682483200⟩, ⟨.count 5, 27334052932077528436800⟩, ⟨.path 4, 130192015005245245852800⟩, ⟨.path 5, 28066613888749395960000⟩, ⟨.privateRow 2 31, 9836354190843327733185600⟩, ⟨.privateRow 2 32, 15205543159644270818985600⟩, ⟨.privateRow 3 27, 771731427782322219532320⟩, ⟨.privateRow 3 28, 1852370194236325364601000⟩, ⟨.privateRow 3 29, 4023312267288173352292800⟩, ⟨.privateRow 3 30, 4828690612608314815162800⟩, ⟨.privateRow 3 31, 7087329438817244873256000⟩, ⟨.privateRow 4 23, 28310269108223154452400⟩, ⟨.privateRow 4 24, 211699450769865755954400⟩, ⟨.privateRow 4 25, 369009714583046633896800⟩, ⟨.privateRow 4 26, 907881043815432194508000⟩, ⟨.privateRow 4 27, 1347178323080963901528000⟩, ⟨.privateRow 4 28, 1839842086642456497400800⟩, ⟨.privateRow 4 29, 2590877731490491445402400⟩, ⟨.privateRow 5 20, 12261275172389062755936⟩, ⟨.privateRow 5 21, 41565115411000432130880⟩, ⟨.privateRow 5 22, 84149834383752962544720⟩, ⟨.privateRow 5 23, 200263775563588422628800⟩, ⟨.privateRow 5 24, 354561715176091368865920⟩, ⟨.privateRow 5 25, 524813816295888545986560⟩, ⟨.privateRow 5 26, 720642781230701124715920⟩, ⟨.privateRow 5 27, 1094403414537656471888640⟩, ⟨.privateRow 5 28, 725133375640971004387680⟩, ⟨.privateRow 6 16, 100124736014936001600⟩, ⟨.privateRow 6 17, 3217897765813359829200⟩, ⟨.privateRow 6 18, 9071907899535110448000⟩, ⟨.privateRow 6 19, 18786737967602491766880⟩, ⟨.privateRow 6 20, 49702660622525452942400⟩, ⟨.privateRow 6 21, 93716752909980097497600⟩, ⟨.privateRow 6 22, 154087200882414366652800⟩, ⟨.privateRow 6 23, 229808519095614776116800⟩, ⟨.privateRow 6 24, 169991776806158343516480⟩, ⟨.privateRow 6 25, 779671319348306644459200⟩, ⟨.privateRow 7 13, 43387385606472267360⟩, ⟨.privateRow 7 14, 859999964699718156600⟩, ⟨.privateRow 7 15, 2453056032365932039200⟩, ⟨.privateRow 7 16, 4962432228740265579300⟩, ⟨.privateRow 7 17, 13134544915413877300800⟩, ⟨.privateRow 7 18, 28440431265042571254480⟩, ⟨.privateRow 7 19, 49606244210066625681600⟩, ⟨.privateRow 7 20, 78504050831710758754500⟩, ⟨.privateRow 7 21, 115797833084702590707600⟩, ⟨.privateRow 7 22, 159557110567801763216400⟩, ⟨.privateRow 7 23, 138232210542220643808960⟩, ⟨.privateRow 8 10, 19141493649914235600⟩, ⟨.privateRow 8 11, 264391881039440379225⟩, ⟨.privateRow 8 12, 846054019326209213520⟩, ⟨.privateRow 8 13, 1766486413977799456800⟩, ⟨.privateRow 8 14, 4380457200653450070000⟩, ⟨.privateRow 8 15, 9762161761456260156000⟩, ⟨.privateRow 8 16, 19198918130863978306800⟩, ⟨.privateRow 8 17, 31954809499166824910640⟩, ⟨.privateRow 8 18, 48955433425969541671200⟩, ⟨.privateRow 8 19, 70897699792576089382950⟩, ⟨.privateRow 8 20, 35143782341242536561600⟩, ⟨.privateRow 9 7, 22835466108669614400⟩, ⟨.privateRow 9 8, 96416412458827260800⟩, ⟨.privateRow 9 9, 357307881465065731200⟩, ⟨.privateRow 9 10, 840630596125400180100⟩, ⟨.privateRow 9 11, 2082594509110668833280⟩, ⟨.privateRow 9 12, 4400720540085044260800⟩, ⟨.privateRow 9 13, 8944476417334282809600⟩, ⟨.privateRow 9 14, 16378738066443280928400⟩, ⟨.privateRow 9 15, 26387419064299951694400⟩, ⟨.privateRow 9 16, 22821764829004412631360⟩, ⟨.privateRow 10 5, 78097294091650081248⟩, ⟨.privateRow 10 6, 164415355982421223680⟩, ⟨.privateRow 10 7, 520648627277667208320⟩, ⟨.privateRow 10 8, 1332247958034030797760⟩, ⟨.privateRow 10 9, 2879837719629596746020⟩, ⟨.privateRow 10 11, 22090377471638165838720⟩, ⟨.privateRow 10 12, 2643293030794310442240⟩, ⟨.privateRow 11 3, 185945938313452574400⟩, ⟨.privateRow 11 4, 390486470458250406240⟩, ⟨.privateRow 11 5, 513797987445066324000⟩, ⟨.privateRow 11 6, 3254053920485420052000⟩, ⟨.privateRow 11 7, 5972146018773241507200⟩, ⟨.privateRow 12 0, 311257331524692352800⟩, ⟨.privateRow 12 2, 2045405321447978318400⟩, ⟨.privateRow 12 3, 1073837793760188617160⟩, ⟨.privateRow 13 0, 1952432352291252031200⟩, ⟨.hall 3 30, 653309057752166365149600⟩, ⟨.assumptionRow 19, 1226642664514741760⟩]
  caps := #[0, 0, 73953445037262305486400, 11744955413960871239280, 0, 757920788528899881600, 2477337548198044097200, 1542021291273526498800, 3470862286681907453545, 0, 0, 5365236182226108096480, 53319362688690965638200, 0, 128185495329565265180160] }

theorem case_48_34_19_checked :
    (Witness.linear .conditional case_48_34_19).check 48 34 19 = true := by
  change case_48_34_19.check 48 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_20 : Certificate := {
  objectiveScale := 15216036054419200000
  eta := 3322454133894023581493040000
  rows := #[⟨.count 2, 326017154185593264169776000⟩, ⟨.count 3, 27597631299636847461012000⟩, ⟨.count 4, 1913383705245426990576000⟩, ⟨.count 5, 78097294091650081248000⟩, ⟨.path 4, 377473045260965589936000⟩, ⟨.path 5, 79022035310909937246000⟩, ⟨.privateRow 6 18, 3352661615045584296000⟩, ⟨.privateRow 7 15, 375467760056010006000⟩, ⟨.privateRow 7 17, 1183292334721970928000⟩, ⟨.privateRow 8 14, 125155920018670002000⟩, ⟨.privateRow 8 15, 271171160040451671000⟩, ⟨.hall 9 7, 56863018373367024⟩, ⟨.hall 11 7, 292013633103192000⟩, ⟨.hall 12 7, 1259308792757515500⟩, ⟨.hall 10 8, 743307429717216000⟩, ⟨.hall 11 8, 657030674482182000⟩, ⟨.hall 8 9, 559604307801389760⟩, ⟨.hall 9 9, 883049226504052608⟩, ⟨.hall 7 11, 542097103504387200⟩, ⟨.hall 8 11, 253546452588636900⟩, ⟨.hall 10 11, 140792287389039000⟩, ⟨.hall 6 13, 351763446424157625⟩, ⟨.hall 5 17, 501585759936747200⟩, ⟨.hall 4 22, 11157494945392543440⟩, ⟨.hall 3 25, 232964982468143904000⟩, ⟨.hall 2 28, 11365480097472964062600⟩]
  caps := #[0, 1797547044371491082670000, 237563643115317543024000, 79286081274531508377000, 0, 16110326181525149574000, 82456790234423605000, 2437695987636367993500, 5799770089294293343000, 160800581786439364000, 0, 52000446590132590550000, 13865460694228951808000, 0, 589773557469288192000000] }

theorem case_48_34_20_checked :
    (Witness.linear .negative case_48_34_20).check 48 34 20 = true := by
  change case_48_34_20.check 48 34 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440, 48450] }

theorem case_48_34_21_checked :
    (Witness.linear .negative case_48_34_21).check 48 34 21 = true := by
  change case_48_34_21.check 48 34 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990] }

theorem case_48_34_22_checked :
    (Witness.linear .negative case_48_34_22).check 48 34 22 = true := by
  change case_48_34_22.check 48 34 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_35_1_checked :
    (Witness.rising).check 48 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_35_2_checked :
    (Witness.rising).check 48 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_35_3_checked :
    (Witness.rising).check 48 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_35_4_checked :
    (Witness.rising).check 48 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_35_5_checked :
    (Witness.rising).check 48 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_35_6_checked :
    (Witness.rising).check 48 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_35_7_checked :
    (Witness.rising).check 48 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_35_8_checked :
    (Witness.rising).check 48 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_35_9_checked :
    (Witness.rising).check 48 35 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_48_35_10_checked :
    (Witness.linear .positive case_48_35_10).check 48 35 10 = true := by
  change case_48_35_10.check 48 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_48_35_11_checked :
    (Witness.linear .positive case_48_35_11).check 48 35 11 = true := by
  change case_48_35_11.check 48 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_48_35_12_checked :
    (Witness.linear .positive case_48_35_12).check 48 35 12 = true := by
  change case_48_35_12.check 48 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_48_35_13_checked :
    (Witness.linear .positive case_48_35_13).check 48 35 13 = true := by
  change case_48_35_13.check 48 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_48_35_14_checked :
    (Witness.linear .positive case_48_35_14).check 48 35 14 = true := by
  change case_48_35_14.check 48 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_48_35_15_checked :
    (Witness.linear .positive case_48_35_15).check 48 35 15 = true := by
  change case_48_35_15.check 48 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_48_35_16_checked :
    (Witness.linear .positive case_48_35_16).check 48 35 16 = true := by
  change case_48_35_16.check 48 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_17 : Certificate := {
  objectiveScale := 348
  eta := 1105507305
  rows := #[⟨.assumptionRow 17, 601⟩]
  caps := #[0, 0, 320635640, 93961992, 27862626, 8375390, 2557854, 795912, 253253, 82797, 26640900, 18257492, 8518510, 3147837] }

theorem case_48_35_17_checked :
    (Witness.linear .conditional case_48_35_17).check 48 35 17 = true := by
  change case_48_35_17.check 48 35 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_18 : Certificate := {
  objectiveScale := 191352761600000
  eta := 59262244641259772112000
  rows := #[⟨.count 2, 4861545909865444800000⟩, ⟨.count 3, 335888626499794368000⟩, ⟨.count 4, 15910513886832364800⟩, ⟨.count 5, 491065243420752000⟩, ⟨.path 4, 14551685770461840000⟩, ⟨.privateRow 2 32, 392974961047456788000⟩, ⟨.privateRow 2 33, 542872626601641336000⟩, ⟨.privateRow 3 27, 4419587190786768000⟩, ⟨.privateRow 3 28, 45227108919051259200⟩, ⟨.privateRow 3 29, 80657466231858516000⟩, ⟨.privateRow 3 30, 163033660815689664000⟩, ⟨.privateRow 3 31, 170522405777856132000⟩, ⟨.privateRow 3 32, 214349978753158248000⟩, ⟨.privateRow 4 23, 24553262171037600⟩, ⟨.privateRow 4 24, 4115740571420177700⟩, ⟨.privateRow 4 25, 11711906055584935200⟩, ⟨.privateRow 4 26, 18746415667587207600⟩, ⟨.privateRow 4 27, 41190552618132677760⟩, ⟨.privateRow 4 28, 55300084724719434600⟩, ⟨.privateRow 4 29, 67546024232524437600⟩, ⟨.privateRow 4 30, 80988935271167523600⟩, ⟨.privateRow 5 20, 53570753827718400⟩, ⟨.privateRow 5 21, 1257127023157125120⟩, ⟨.privateRow 5 22, 2728140241226400000⟩, ⟨.privateRow 5 23, 4824716016608888400⟩, ⟨.privateRow 5 24, 10663130999993472000⟩, ⟨.privateRow 5 25, 16941750898015944000⟩, ⟨.privateRow 5 26, 22765784684986062720⟩, ⟨.privateRow 5 27, 27794292777614563200⟩, ⟨.privateRow 5 28, 29365701556560969600⟩, ⟨.privateRow 6 18, 337607354851767000⟩, ⟨.privateRow 6 19, 753338725702290000⟩, ⟨.privateRow 6 20, 1319737841693271000⟩, ⟨.privateRow 6 21, 3110079874998096000⟩, ⟨.privateRow 6 22, 5409390572056721250⟩, ⟨.privateRow 6 23, 8049962383218756000⟩, ⟨.privateRow 6 24, 10056606964220817000⟩, ⟨.privateRow 6 25, 14952936662161898400⟩, ⟨.privateRow 7 15, 86437504581714000⟩, ⟨.privateRow 7 16, 254976184083852000⟩, ⟨.privateRow 7 17, 460373665706955000⟩, ⟨.privateRow 7 18, 1033150252391712000⟩, ⟨.privateRow 7 19, 2004598475821141200⟩, ⟨.privateRow 7 20, 3221154156248028000⟩, ⟨.privateRow 7 21, 4656350790293202000⟩, ⟨.privateRow 7 22, 4569913285711488000⟩, ⟨.privateRow 8 12, 26855130499572375⟩, ⟨.privateRow 8 13, 98213048684150400⟩, ⟨.privateRow 8 14, 214841043996579000⟩, ⟨.privateRow 8 15, 467456337487062000⟩, ⟨.privateRow 8 16, 890055753700113000⟩, ⟨.privateRow 8 17, 1473195730262256000⟩, ⟨.privateRow 8 18, 2651752314472060800⟩, ⟨.privateRow 9 9, 10912560964905600⟩, ⟨.privateRow 9 10, 46217905263129600⟩, ⟨.privateRow 9 11, 116627995312428600⟩, ⟨.privateRow 9 12, 294639146052451200⟩, ⟨.privateRow 9 13, 561217421052288000⟩, ⟨.privateRow 9 14, 997240186639065600⟩, ⟨.privateRow 10 7, 23260985214667200⟩, ⟨.privateRow 10 8, 49106524342075200⟩, ⟨.privateRow 10 9, 311970860526124800⟩, ⟨.privateRow 10 10, 303846619366590300⟩, ⟨.privateRow 11 4, 35076088815768000⟩, ⟨.privateRow 11 5, 73659786513112800⟩, ⟨.privateRow 11 6, 116304926073336000⟩, ⟨.hall 3 31, 5248259789059287000⟩, ⟨.assumptionRow 18, 145887892166016⟩]
  caps := #[0, 39563861397444384000, 3907283445460755360, 0, 0, 47009045091677760, 104394323578110930, 56826431001532080, 5754652467828264, 0, 849317313934589500, 0, 17777018383347455232, 6463678156180941696] }

theorem case_48_35_18_checked :
    (Witness.linear .conditional case_48_35_18).check 48 35 18 = true := by
  change case_48_35_18.check 48 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_19 : Certificate := {
  objectiveScale := 7825765147200000
  eta := 2940340751021178862156800
  rows := #[⟨.count 2, 245862961299625139870400⟩, ⟨.count 3, 17480351256999824793600⟩, ⟨.count 4, 874017562849991239680⟩, ⟨.count 5, 10115944014467491200⟩, ⟨.path 4, 641833329804895388160⟩, ⟨.path 5, 12277507987739194200⟩, ⟨.privateRow 2 32, 20905862798898879001200⟩, ⟨.privateRow 2 33, 29793984108610378456800⟩, ⟨.privateRow 3 27, 103688426148291784800⟩, ⟨.privateRow 3 28, 2263948270437824530560⟩, ⟨.privateRow 3 29, 4165239947956989501600⟩, ⟨.privateRow 3 30, 8709827796456509923200⟩, ⟨.privateRow 3 31, 9483697513563273000000⟩, ⟨.privateRow 3 32, 12397089389729910465600⟩, ⟨.privateRow 4 24, 175827751901463081420⟩, ⟨.privateRow 4 25, 574224336306951089760⟩, ⟨.privateRow 4 26, 929402356329200754000⟩, ⟨.privateRow 4 27, 2117671719988624607808⟩, ⟨.privateRow 4 28, 2962327755336623954280⟩, ⟨.privateRow 4 29, 3776787697801437839520⟩, ⟨.privateRow 4 30, 4797992246061931076160⟩, ⟨.privateRow 5 19, 168599066907791520⟩, ⟨.privateRow 5 20, 5701713899063495040⟩, ⟨.privateRow 5 21, 56446967600728600896⟩, ⟨.privateRow 5 22, 128584888361675665920⟩, ⟨.privateRow 5 23, 231655117931305548480⟩, ⟨.privateRow 5 24, 523716872977574115840⟩, ⟨.privateRow 5 25, 865250411370786080640⟩, ⟨.privateRow 5 26, 1210271541890890647168⟩, ⟨.privateRow 5 27, 1555326392224376772000⟩, ⟨.privateRow 5 28, 2144580131067108134400⟩, ⟨.privateRow 6 17, 2334448618723267200⟩, ⟨.privateRow 6 18, 16227660189874933800⟩, ⟨.privateRow 6 19, 34945988413614969600⟩, ⟨.privateRow 6 20, 61454359887890009040⟩, ⟨.privateRow 6 21, 147243185099471260800⟩, ⟨.privateRow 6 22, 262540359500476607550⟩, ⟨.privateRow 6 23, 405360328008304468800⟩, ⟨.privateRow 6 24, 571129339150143774000⟩, ⟨.privateRow 6 25, 736440724253233359360⟩, ⟨.privateRow 6 26, 455533603901489213100⟩, ⟨.privateRow 7 14, 1011594401446749120⟩, ⟨.privateRow 7 15, 5341837783149925200⟩, ⟨.privateRow 7 16, 12255855248297152800⟩, ⟨.privateRow 7 17, 21225418244641611000⟩, ⟨.privateRow 7 18, 47689450353918172800⟩, ⟨.privateRow 7 19, 93753123991225498800⟩, ⟨.privateRow 7 20, 154388574125563377600⟩, ⟨.privateRow 7 21, 96462751852243576800⟩, ⟨.privateRow 7 22, 588995679046443926400⟩, ⟨.privateRow 8 11, 520673588979944400⟩, ⟨.privateRow 8 12, 2291893565777790975⟩, ⟨.privateRow 8 13, 5563769207957120160⟩, ⟨.privateRow 8 14, 10206264943168093800⟩, ⟨.privateRow 8 15, 21593649723190221600⟩, ⟨.privateRow 8 16, 40885273725139443600⟩, ⟨.privateRow 8 17, 73455548014144623600⟩, ⟨.privateRow 8 18, 115195312464748556040⟩, ⟨.privateRow 8 19, 109167895822795009200⟩, ⟨.privateRow 9 8, 319450863614762880⟩, ⟨.privateRow 9 9, 1348792535262332160⟩, ⟨.privateRow 9 10, 3332310969471644160⟩, ⟨.privateRow 9 11, 6701812909584712920⟩, ⟨.privateRow 9 12, 14297200873780720896⟩, ⟨.privateRow 9 14, 97579952262632568960⟩, ⟨.privateRow 9 15, 13825123486438904640⟩, ⟨.privateRow 10 5, 216770228881446240⟩, ⟨.privateRow 10 6, 910434961302074208⟩, ⟨.privateRow 10 7, 2875057772532865920⟩, ⟨.privateRow 10 8, 1517391602170123680⟩, ⟨.privateRow 10 9, 21957549066697083840⟩, ⟨.privateRow 10 10, 20769297554703567870⟩, ⟨.privateRow 11 3, 1379446911063748800⟩, ⟨.privateRow 11 4, 3612837148024104000⟩, ⟨.privateRow 11 5, 7586958010850618400⟩, ⟨.privateRow 11 6, 4791762954221443200⟩, ⟨.privateRow 12 0, 3477355754973200100⟩, ⟨.privateRow 12 1, 3628545135624208800⟩, ⟨.hall 3 31, 486513682445795904900⟩, ⟨.assumptionRow 19, 3042332864899328⟩]
  caps := #[0, 624480270984013604160, 0, 68595366197649170880, 9635528229352656904, 10908863094814992216, 1542054864857070648, 7452266464833149520, 153198779166468189, 0, 46154275231847404622, 4195817687818902600, 0, 603852687951568543488] }

theorem case_48_35_19_checked :
    (Witness.linear .conditional case_48_35_19).check 48 35 19 = true := by
  change case_48_35_19.check 48 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_20 : Certificate := {
  objectiveScale := 6527177243086500000
  eta := 3789687119681066169429864000
  rows := #[⟨.count 2, 305765514300812472286380000⟩, ⟨.count 3, 20432234300141511063216000⟩, ⟨.count 4, 886217391331439034067200⟩, ⟨.path 3, 352636750372329509486400⟩, ⟨.path 4, 883205048019982330843200⟩, ⟨.path 5, 786001805476286899500⟩, ⟨.privateRow 2 32, 29730336907108518984303000⟩, ⟨.privateRow 3 28, 2646343599114713782284000⟩, ⟨.privateRow 3 30, 4075505904579765928272000⟩, ⟨.privateRow 3 31, 46690527376628593554096000⟩, ⟨.privateRow 4 27, 6172750302121064938676400⟩, ⟨.privateRow 5 18, 420805978789857091200⟩, ⟨.privateRow 5 19, 1595556002911541470800⟩, ⟨.privateRow 5 20, 2735238862134071092800⟩, ⟨.privateRow 5 22, 87527643588290274969600⟩, ⟨.privateRow 5 23, 85476214441689721650000⟩, ⟨.privateRow 5 24, 237184284187911593332800⟩, ⟨.privateRow 5 26, 5039404079595812581374720⟩, ⟨.privateRow 5 28, 1855403694814278224616000⟩, ⟨.privateRow 5 29, 2252469202967407544920800⟩, ⟨.privateRow 6 16, 1098979899964582135500⟩, ⟨.privateRow 6 18, 3561508935070405068750⟩, ⟨.privateRow 6 19, 11500436124881889822000⟩, ⟨.privateRow 7 13, 183163316660763689250⟩, ⟨.privateRow 7 14, 781496817752591740800⟩, ⟨.privateRow 7 15, 104664752377579251000⟩, ⟨.privateRow 7 17, 976871022190739676000⟩, ⟨.privateRow 8 24, 1123584838836011391089250⟩, ⟨.hall 7 7, 685807943309391875⟩, ⟨.hall 11 7, 651992482392751500⟩, ⟨.hall 8 9, 661804285344564096⟩, ⟨.hall 9 9, 480595969119266784⟩, ⟨.hall 10 9, 331365591051374880⟩, ⟨.hall 6 11, 310533787532311200⟩, ⟨.hall 5 15, 181513120098184875⟩, ⟨.hall 6 23, 3548463114795421900⟩, ⟨.hall 3 24, 6545106896882701455⟩, ⟨.hall 4 26, 68819241459488520000⟩, ⟨.hall 2 31, 28848222374070281056875⟩]
  caps := #[0, 845230276980517658630400, 0, 66228021149530236796800, 14571071742997490406840, 786001805476286899500, 19261750401567785543250, 623072724596814977100, 3583060223843244894750, 3523255397498614377600, 0, 61283385570830623200, 215491336439625420174000, 974024551276826049000000] }

theorem case_48_35_20_checked :
    (Witness.linear .negative case_48_35_20).check 48 35 20 = true := by
  change case_48_35_20.check 48 35 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876, 177650] }

theorem case_48_35_21_checked :
    (Witness.linear .negative case_48_35_21).check 48 35 21 = true := by
  change case_48_35_21.check 48 35 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226] }

theorem case_48_35_22_checked :
    (Witness.linear .negative case_48_35_22).check 48 35 22 = true := by
  change case_48_35_22.check 48 35 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_36_1_checked :
    (Witness.rising).check 48 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_36_2_checked :
    (Witness.rising).check 48 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_36_3_checked :
    (Witness.rising).check 48 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_36_4_checked :
    (Witness.rising).check 48 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_36_5_checked :
    (Witness.rising).check 48 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_36_6_checked :
    (Witness.rising).check 48 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_36_7_checked :
    (Witness.rising).check 48 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_36_8_checked :
    (Witness.rising).check 48 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_48_36_9_checked :
    (Witness.linear .positive case_48_36_9).check 48 36 9 = true := by
  change case_48_36_9.check 48 36 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_48_36_10_checked :
    (Witness.linear .positive case_48_36_10).check 48 36 10 = true := by
  change case_48_36_10.check 48 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_48_36_11_checked :
    (Witness.linear .positive case_48_36_11).check 48 36 11 = true := by
  change case_48_36_11.check 48 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_48_36_12_checked :
    (Witness.linear .positive case_48_36_12).check 48 36 12 = true := by
  change case_48_36_12.check 48 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_48_36_13_checked :
    (Witness.linear .positive case_48_36_13).check 48 36 13 = true := by
  change case_48_36_13.check 48 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_48_36_14_checked :
    (Witness.linear .positive case_48_36_14).check 48 36 14 = true := by
  change case_48_36_14.check 48 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_48_36_15_checked :
    (Witness.linear .positive case_48_36_15).check 48 36 15 = true := by
  change case_48_36_15.check 48 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_48_36_16_checked :
    (Witness.linear .positive case_48_36_16).check 48 36 16 = true := by
  change case_48_36_16.check 48 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_48_36_17_checked :
    (Witness.linear .positive case_48_36_17).check 48 36 17 = true := by
  change case_48_36_17.check 48 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_18 : Certificate := {
  objectiveScale := 935
  eta := 6516266505
  rows := #[⟨.assumptionRow 18, 1421⟩]
  caps := #[0, 0, 1873110915, 542948465, 158861736, 46973890, 14367040, 4560114, 1473472, 493350, 175468150, 130402525, 66897248] }

theorem case_48_36_18_checked :
    (Witness.linear .conditional case_48_36_18).check 48 36 18 = true := by
  change case_48_36_18.check 48 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_19 : Certificate := {
  objectiveScale := 435
  eta := 1724401770
  rows := #[⟨.assumptionRow 19, 466⟩]
  caps := #[0, 0, 536854500, 173696575, 55814077, 17871590, 5717100, 1830900, 603772, 254451990, 223405325, 138201250, 70811917] }

theorem case_48_36_19_checked :
    (Witness.linear .conditional case_48_36_19).check 48 36 19 = true := by
  change case_48_36_19.check 48 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_20 : Certificate := {
  objectiveScale := 645
  eta := 911365455
  rows := #[⟨.assumptionRow 20, 506⟩]
  caps := #[0, 0, 306173010, 99048235, 38306983, 13632861, 4612440, 1767456, 688275, 474732765, 450588515, 304162925, 171941583] }

theorem case_48_36_20_checked :
    (Witness.linear .conditional case_48_36_20).check 48 36 20 = true := by
  change case_48_36_20.check 48 36 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_21 : Certificate := {
  objectiveScale := 21
  eta := 141680
  rows := #[⟨.assumptionRow 21, 8⟩]
  caps := #[0, 0, 67298, 30877, 17157, 7467, 4029, 2176, 910, 21395520, 21246940, 15155160, 9152528] }

theorem case_48_36_21_checked :
    (Witness.linear .conditional case_48_36_21).check 48 36 21 = true := by
  change case_48_36_21.check 48 36 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888] }

theorem case_48_36_22_checked :
    (Witness.linear .negative case_48_36_22).check 48 36 22 = true := by
  change case_48_36_22.check 48 36 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012] }

theorem case_48_36_23_checked :
    (Witness.linear .negative case_48_36_23).check 48 36 23 = true := by
  change case_48_36_23.check 48 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_37_1_checked :
    (Witness.rising).check 48 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_37_2_checked :
    (Witness.rising).check 48 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_37_3_checked :
    (Witness.rising).check 48 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_37_4_checked :
    (Witness.rising).check 48 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_37_5_checked :
    (Witness.rising).check 48 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_37_6_checked :
    (Witness.rising).check 48 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_37_7_checked :
    (Witness.rising).check 48 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_37_8_checked :
    (Witness.rising).check 48 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_48_37_9_checked :
    (Witness.linear .positive case_48_37_9).check 48 37 9 = true := by
  change case_48_37_9.check 48 37 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_48_37_10_checked :
    (Witness.linear .positive case_48_37_10).check 48 37 10 = true := by
  change case_48_37_10.check 48 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_48_37_11_checked :
    (Witness.linear .positive case_48_37_11).check 48 37 11 = true := by
  change case_48_37_11.check 48 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_48_37_12_checked :
    (Witness.linear .positive case_48_37_12).check 48 37 12 = true := by
  change case_48_37_12.check 48 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_48_37_13_checked :
    (Witness.linear .positive case_48_37_13).check 48 37 13 = true := by
  change case_48_37_13.check 48 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_48_37_14_checked :
    (Witness.linear .positive case_48_37_14).check 48 37 14 = true := by
  change case_48_37_14.check 48 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_48_37_15_checked :
    (Witness.linear .positive case_48_37_15).check 48 37 15 = true := by
  change case_48_37_15.check 48 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_48_37_16_checked :
    (Witness.linear .positive case_48_37_16).check 48 37 16 = true := by
  change case_48_37_16.check 48 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_48_37_17_checked :
    (Witness.linear .positive case_48_37_17).check 48 37 17 = true := by
  change case_48_37_17.check 48 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_48_37_18_checked :
    (Witness.linear .positive case_48_37_18).check 48 37 18 = true := by
  change case_48_37_18.check 48 37 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_19 : Certificate := {
  objectiveScale := 411
  eta := 3137217825
  rows := #[⟨.assumptionRow 19, 488⟩]
  caps := #[0, 0, 934126830, 279306365, 83925413, 25361314, 8291410, 2736456, 910455, 398779290, 337254060, 200711225] }

theorem case_48_37_19_checked :
    (Witness.linear .conditional case_48_37_19).check 48 37 19 = true := by
  change case_48_37_19.check 48 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_20 : Certificate := {
  objectiveScale := 8
  eta := 26403195
  rows := #[⟨.assumptionRow 20, 7⟩]
  caps := #[0, 0, 8727810, 2812095, 889295, 326876, 114342, 38760, 6653325, 13123110, 10566660, 6561555] }

theorem case_48_37_20_checked :
    (Witness.linear .conditional case_48_37_20).check 48 37 20 = true := by
  change case_48_37_20.check 48 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_21 : Certificate := {
  objectiveScale := 95
  eta := 7696260
  rows := #[⟨.assumptionRow 21, 48⟩]
  caps := #[0, 0, 2795650, 1403644, 528770, 263340, 103683, 51204, 154547235, 237454875, 191989395, 124385495] }

theorem case_48_37_21_checked :
    (Witness.linear .conditional case_48_37_21).check 48 37 21 = true := by
  change case_48_37_21.check 48 37 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540] }

theorem case_48_37_22_checked :
    (Witness.linear .negative case_48_37_22).check 48 37 22 = true := by
  change case_48_37_22.check 48 37 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900] }

theorem case_48_37_23_checked :
    (Witness.linear .negative case_48_37_23).check 48 37 23 = true := by
  change case_48_37_23.check 48 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_37_24_checked :
    (Witness.linear .negative case_48_37_24).check 48 37 24 = true := by
  change case_48_37_24.check 48 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_38_1_checked :
    (Witness.rising).check 48 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_38_2_checked :
    (Witness.rising).check 48 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_38_3_checked :
    (Witness.rising).check 48 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_38_4_checked :
    (Witness.rising).check 48 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_38_5_checked :
    (Witness.rising).check 48 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_38_6_checked :
    (Witness.rising).check 48 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_38_7_checked :
    (Witness.rising).check 48 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_38_8_checked :
    (Witness.rising).check 48 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_48_38_9_checked :
    (Witness.linear .positive case_48_38_9).check 48 38 9 = true := by
  change case_48_38_9.check 48 38 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_48_38_10_checked :
    (Witness.linear .positive case_48_38_10).check 48 38 10 = true := by
  change case_48_38_10.check 48 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_48_38_11_checked :
    (Witness.linear .positive case_48_38_11).check 48 38 11 = true := by
  change case_48_38_11.check 48 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_48_38_12_checked :
    (Witness.linear .positive case_48_38_12).check 48 38 12 = true := by
  change case_48_38_12.check 48 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_48_38_13_checked :
    (Witness.linear .positive case_48_38_13).check 48 38 13 = true := by
  change case_48_38_13.check 48 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_48_38_14_checked :
    (Witness.linear .positive case_48_38_14).check 48 38 14 = true := by
  change case_48_38_14.check 48 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_48_38_15_checked :
    (Witness.linear .positive case_48_38_15).check 48 38 15 = true := by
  change case_48_38_15.check 48 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_48_38_16_checked :
    (Witness.linear .positive case_48_38_16).check 48 38 16 = true := by
  change case_48_38_16.check 48 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_48_38_17_checked :
    (Witness.linear .positive case_48_38_17).check 48 38 17 = true := by
  change case_48_38_17.check 48 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_48_38_18_checked :
    (Witness.linear .positive case_48_38_18).check 48 38 18 = true := by
  change case_48_38_18.check 48 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_19 : Certificate := {
  objectiveScale := 915
  eta := 10296895875
  rows := #[⟨.assumptionRow 19, 1186⟩]
  caps := #[0, 0, 3109764105, 943841340, 288133765, 88583396, 27464690, 8600844, 2731365, 1451265270, 1182461280] }

theorem case_48_38_19_checked :
    (Witness.linear .conditional case_48_38_19).check 48 38 19 = true := by
  change case_48_38_19.check 48 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_20 : Certificate := {
  objectiveScale := 598
  eta := 2539258995
  rows := #[⟨.assumptionRow 20, 541⟩]
  caps := #[0, 0, 800635290, 249026635, 88232485, 30236030, 10095042, 3310104, 2653976325, 2463691230, 1630970250] }

theorem case_48_38_20_checked :
    (Witness.linear .conditional case_48_38_20).check 48 38 20 = true := by
  change case_48_38_20.check 48 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_21 : Certificate := {
  objectiveScale := 5
  eta := 1776060
  rows := #[⟨.assumptionRow 21, 3⟩]
  caps := #[0, 0, 740025, 284625, 110561, 46398, 16473, 7752, 28514250, 27943965, 19684665] }

theorem case_48_38_21_checked :
    (Witness.linear .conditional case_48_38_21).check 48 38 21 = true := by
  change case_48_38_21.check 48 38 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405] }

theorem case_48_38_22_checked :
    (Witness.linear .negative case_48_38_22).check 48 38 22 = true := by
  change case_48_38_22.check 48 38 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440] }

theorem case_48_38_23_checked :
    (Witness.linear .negative case_48_38_23).check 48 38 23 = true := by
  change case_48_38_23.check 48 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_38_24_checked :
    (Witness.linear .negative case_48_38_24).check 48 38 24 = true := by
  change case_48_38_24.check 48 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_39_1_checked :
    (Witness.rising).check 48 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_39_2_checked :
    (Witness.rising).check 48 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_39_3_checked :
    (Witness.rising).check 48 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_39_4_checked :
    (Witness.rising).check 48 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_39_5_checked :
    (Witness.rising).check 48 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_39_6_checked :
    (Witness.rising).check 48 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_39_7_checked :
    (Witness.rising).check 48 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_39_8_checked :
    (Witness.rising).check 48 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_48_39_9_checked :
    (Witness.linear .positive case_48_39_9).check 48 39 9 = true := by
  change case_48_39_9.check 48 39 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_48_39_10_checked :
    (Witness.linear .positive case_48_39_10).check 48 39 10 = true := by
  change case_48_39_10.check 48 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_48_39_11_checked :
    (Witness.linear .positive case_48_39_11).check 48 39 11 = true := by
  change case_48_39_11.check 48 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_48_39_12_checked :
    (Witness.linear .positive case_48_39_12).check 48 39 12 = true := by
  change case_48_39_12.check 48 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_48_39_13_checked :
    (Witness.linear .positive case_48_39_13).check 48 39 13 = true := by
  change case_48_39_13.check 48 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_48_39_14_checked :
    (Witness.linear .positive case_48_39_14).check 48 39 14 = true := by
  change case_48_39_14.check 48 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_48_39_15_checked :
    (Witness.linear .positive case_48_39_15).check 48 39 15 = true := by
  change case_48_39_15.check 48 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_48_39_16_checked :
    (Witness.linear .positive case_48_39_16).check 48 39 16 = true := by
  change case_48_39_16.check 48 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_48_39_17_checked :
    (Witness.linear .positive case_48_39_17).check 48 39 17 = true := by
  change case_48_39_17.check 48 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_48_39_18_checked :
    (Witness.linear .positive case_48_39_18).check 48 39 18 = true := by
  change case_48_39_18.check 48 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_48_39_19_checked :
    (Witness.linear .positive case_48_39_19).check 48 39 19 = true := by
  change case_48_39_19.check 48 39 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_20 : Certificate := {
  objectiveScale := 935
  eta := 9357376350
  rows := #[⟨.assumptionRow 20, 954⟩]
  caps := #[0, 0, 2882500530, 884190840, 270489890, 88828553, 29951790, 9980700, 7047341910, 6343139985] }

theorem case_48_39_20_checked :
    (Witness.linear .conditional case_48_39_20).check 48 39 20 = true := by
  change case_48_39_20.check 48 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_21 : Certificate := {
  objectiveScale := 32
  eta := 10607025
  rows := #[⟨.assumptionRow 21, 19⟩]
  caps := #[0, 0, 4242810, 1701425, 629717, 277761, 100776, 660009840, 648223950, 459079425] }

theorem case_48_39_21_checked :
    (Witness.linear .conditional case_48_39_21).check 48 39 21 = true := by
  change case_48_39_21.check 48 39 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825] }

theorem case_48_39_22_checked :
    (Witness.linear .negative case_48_39_22).check 48 39 22 = true := by
  change case_48_39_22.check 48 39 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845] }

theorem case_48_39_23_checked :
    (Witness.linear .negative case_48_39_23).check 48 39 23 = true := by
  change case_48_39_23.check 48 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_39_24_checked :
    (Witness.linear .negative case_48_39_24).check 48 39 24 = true := by
  change case_48_39_24.check 48 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_39_25_checked :
    (Witness.linear .negative case_48_39_25).check 48 39 25 = true := by
  change case_48_39_25.check 48 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_40_1_checked :
    (Witness.rising).check 48 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_40_2_checked :
    (Witness.rising).check 48 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_40_3_checked :
    (Witness.rising).check 48 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_40_4_checked :
    (Witness.rising).check 48 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_40_5_checked :
    (Witness.rising).check 48 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_40_6_checked :
    (Witness.rising).check 48 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_40_7_checked :
    (Witness.rising).check 48 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_40_8_checked :
    (Witness.rising).check 48 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_48_40_9_checked :
    (Witness.linear .positive case_48_40_9).check 48 40 9 = true := by
  change case_48_40_9.check 48 40 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_48_40_10_checked :
    (Witness.linear .positive case_48_40_10).check 48 40 10 = true := by
  change case_48_40_10.check 48 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_48_40_11_checked :
    (Witness.linear .positive case_48_40_11).check 48 40 11 = true := by
  change case_48_40_11.check 48 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_48_40_12_checked :
    (Witness.linear .positive case_48_40_12).check 48 40 12 = true := by
  change case_48_40_12.check 48 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_48_40_13_checked :
    (Witness.linear .positive case_48_40_13).check 48 40 13 = true := by
  change case_48_40_13.check 48 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_48_40_14_checked :
    (Witness.linear .positive case_48_40_14).check 48 40 14 = true := by
  change case_48_40_14.check 48 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_48_40_15_checked :
    (Witness.linear .positive case_48_40_15).check 48 40 15 = true := by
  change case_48_40_15.check 48 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_48_40_16_checked :
    (Witness.linear .positive case_48_40_16).check 48 40 16 = true := by
  change case_48_40_16.check 48 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_48_40_17_checked :
    (Witness.linear .positive case_48_40_17).check 48 40 17 = true := by
  change case_48_40_17.check 48 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_48_40_18_checked :
    (Witness.linear .positive case_48_40_18).check 48 40 18 = true := by
  change case_48_40_18.check 48 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_48_40_19_checked :
    (Witness.linear .positive case_48_40_19).check 48 40 19 = true := by
  change case_48_40_19.check 48 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_20 : Certificate := {
  objectiveScale := 19
  eta := 2319959400
  rows := #[⟨.assumptionRow 20, 32⟩]
  caps := #[0, 0, 660009840, 189144525, 54649035, 15935205, 4695128, 1399882, 423130] }

theorem case_48_40_20_checked :
    (Witness.linear .conditional case_48_40_20).check 48 40 20 = true := by
  change case_48_40_20.check 48 40 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_21 : Certificate := {
  objectiveScale := 4
  eta := 10795395
  rows := #[⟨.assumptionRow 21, 3⟩]
  caps := #[0, 0, 3641820, 1381380, 480700, 158631, 63954, 136468200, 131505720] }

theorem case_48_40_21_checked :
    (Witness.linear .conditional case_48_40_21).check 48 40 21 = true := by
  change case_48_40_21.check 48 40 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 129644790, 129644790, 94287120] }

theorem case_48_40_22_checked :
    (Witness.linear .negative case_48_40_22).check 48 40 22 = true := by
  change case_48_40_22.check 48 40 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 35357670] }

theorem case_48_40_23_checked :
    (Witness.linear .negative case_48_40_23).check 48 40 23 = true := by
  change case_48_40_23.check 48 40 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_40_24_checked :
    (Witness.linear .negative case_48_40_24).check 48 40 24 = true := by
  change case_48_40_24.check 48 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_40_25_checked :
    (Witness.linear .negative case_48_40_25).check 48 40 25 = true := by
  change case_48_40_25.check 48 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_40_26_checked :
    (Witness.linear .negative case_48_40_26).check 48 40 26 = true := by
  change case_48_40_26.check 48 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_41_1_checked :
    (Witness.rising).check 48 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_41_2_checked :
    (Witness.rising).check 48 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_41_3_checked :
    (Witness.rising).check 48 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_41_4_checked :
    (Witness.rising).check 48 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_41_5_checked :
    (Witness.rising).check 48 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_41_6_checked :
    (Witness.rising).check 48 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_41_7_checked :
    (Witness.rising).check 48 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_41_8_checked :
    (Witness.rising).check 48 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_48_41_9_checked :
    (Witness.linear .positive case_48_41_9).check 48 41 9 = true := by
  change case_48_41_9.check 48 41 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_48_41_10_checked :
    (Witness.linear .positive case_48_41_10).check 48 41 10 = true := by
  change case_48_41_10.check 48 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_48_41_11_checked :
    (Witness.linear .positive case_48_41_11).check 48 41 11 = true := by
  change case_48_41_11.check 48 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_48_41_12_checked :
    (Witness.linear .positive case_48_41_12).check 48 41 12 = true := by
  change case_48_41_12.check 48 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_48_41_13_checked :
    (Witness.linear .positive case_48_41_13).check 48 41 13 = true := by
  change case_48_41_13.check 48 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_48_41_14_checked :
    (Witness.linear .positive case_48_41_14).check 48 41 14 = true := by
  change case_48_41_14.check 48 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_48_41_15_checked :
    (Witness.linear .positive case_48_41_15).check 48 41 15 = true := by
  change case_48_41_15.check 48 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_48_41_16_checked :
    (Witness.linear .positive case_48_41_16).check 48 41 16 = true := by
  change case_48_41_16.check 48 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_48_41_17_checked :
    (Witness.linear .positive case_48_41_17).check 48 41 17 = true := by
  change case_48_41_17.check 48 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_48_41_18_checked :
    (Witness.linear .positive case_48_41_18).check 48 41 18 = true := by
  change case_48_41_18.check 48 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_48_41_19_checked :
    (Witness.linear .positive case_48_41_19).check 48 41 19 = true := by
  change case_48_41_19.check 48 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_48_41_20_checked :
    (Witness.linear .positive case_48_41_20).check 48 41 20 = true := by
  change case_48_41_20.check 48 41 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_21 : Certificate := {
  objectiveScale := 8
  eta := 76918440
  rows := #[⟨.assumptionRow 21, 7⟩]
  caps := #[0, 0, 26403195, 8727810, 2812095, 889295, 326876, 463991880] }

theorem case_48_41_21_checked :
    (Witness.linear .conditional case_48_41_21).check 48 41 21 = true := by
  change case_48_41_21.check 48 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 477638700, 477638700, 347993910] }

theorem case_48_41_22_checked :
    (Witness.linear .negative case_48_41_22).check 48 41 22 = true := by
  change case_48_41_22.check 48 41 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 129644790] }

theorem case_48_41_23_checked :
    (Witness.linear .negative case_48_41_23).check 48 41 23 = true := by
  change case_48_41_23.check 48 41 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_41_24_checked :
    (Witness.linear .negative case_48_41_24).check 48 41 24 = true := by
  change case_48_41_24.check 48 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_41_25_checked :
    (Witness.linear .negative case_48_41_25).check 48 41 25 = true := by
  change case_48_41_25.check 48 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_48_41_26_checked :
    (Witness.linear .negative case_48_41_26).check 48 41 26 = true := by
  change case_48_41_26.check 48 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_42_1_checked :
    (Witness.rising).check 48 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_42_2_checked :
    (Witness.rising).check 48 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_42_3_checked :
    (Witness.rising).check 48 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_42_4_checked :
    (Witness.rising).check 48 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_42_5_checked :
    (Witness.rising).check 48 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_42_6_checked :
    (Witness.rising).check 48 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_42_7_checked :
    (Witness.rising).check 48 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_42_8_checked :
    (Witness.rising).check 48 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_48_42_9_checked :
    (Witness.linear .positive case_48_42_9).check 48 42 9 = true := by
  change case_48_42_9.check 48 42 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_48_42_10_checked :
    (Witness.linear .positive case_48_42_10).check 48 42 10 = true := by
  change case_48_42_10.check 48 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_48_42_11_checked :
    (Witness.linear .positive case_48_42_11).check 48 42 11 = true := by
  change case_48_42_11.check 48 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_48_42_12_checked :
    (Witness.linear .positive case_48_42_12).check 48 42 12 = true := by
  change case_48_42_12.check 48 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_48_42_13_checked :
    (Witness.linear .positive case_48_42_13).check 48 42 13 = true := by
  change case_48_42_13.check 48 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_48_42_14_checked :
    (Witness.linear .positive case_48_42_14).check 48 42 14 = true := by
  change case_48_42_14.check 48 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_48_42_15_checked :
    (Witness.linear .positive case_48_42_15).check 48 42 15 = true := by
  change case_48_42_15.check 48 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_48_42_16_checked :
    (Witness.linear .positive case_48_42_16).check 48 42 16 = true := by
  change case_48_42_16.check 48 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_48_42_17_checked :
    (Witness.linear .positive case_48_42_17).check 48 42 17 = true := by
  change case_48_42_17.check 48 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_48_42_18_checked :
    (Witness.linear .positive case_48_42_18).check 48 42 18 = true := by
  change case_48_42_18.check 48 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_48_42_19_checked :
    (Witness.linear .positive case_48_42_19).check 48 42 19 = true := by
  change case_48_42_19.check 48 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_48_42_20_checked :
    (Witness.linear .positive case_48_42_20).check 48 42 20 = true := by
  change case_48_42_20.check 48 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_48_42_21_checked :
    (Witness.linear .positive case_48_42_21).check 48 42 21 = true := by
  change case_48_42_21.check 48 42 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 1767263190, 1767263190, 1289624490] }

theorem case_48_42_22_checked :
    (Witness.linear .negative case_48_42_22).check 48 42 22 = true := by
  change case_48_42_22.check 48 42 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 477638700] }

theorem case_48_42_23_checked :
    (Witness.linear .negative case_48_42_23).check 48 42 23 = true := by
  change case_48_42_23.check 48 42 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_48_42_24_checked :
    (Witness.linear .negative case_48_42_24).check 48 42 24 = true := by
  change case_48_42_24.check 48 42 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_48_42_25_checked :
    (Witness.linear .negative case_48_42_25).check 48 42 25 = true := by
  change case_48_42_25.check 48 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_48_42_26_checked :
    (Witness.linear .negative case_48_42_26).check 48 42 26 = true := by
  change case_48_42_26.check 48 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_48_42_27_checked :
    (Witness.linear .negative case_48_42_27).check 48 42 27 = true := by
  change case_48_42_27.check 48 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_43_1_checked :
    (Witness.rising).check 48 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_43_2_checked :
    (Witness.rising).check 48 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_43_3_checked :
    (Witness.rising).check 48 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_43_4_checked :
    (Witness.rising).check 48 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_43_5_checked :
    (Witness.rising).check 48 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_43_6_checked :
    (Witness.rising).check 48 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_43_7_checked :
    (Witness.rising).check 48 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_43_8_checked :
    (Witness.rising).check 48 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_48_43_9_checked :
    (Witness.linear .positive case_48_43_9).check 48 43 9 = true := by
  change case_48_43_9.check 48 43 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_48_43_10_checked :
    (Witness.linear .positive case_48_43_10).check 48 43 10 = true := by
  change case_48_43_10.check 48 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_48_43_11_checked :
    (Witness.linear .positive case_48_43_11).check 48 43 11 = true := by
  change case_48_43_11.check 48 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_48_43_12_checked :
    (Witness.linear .positive case_48_43_12).check 48 43 12 = true := by
  change case_48_43_12.check 48 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_48_43_13_checked :
    (Witness.linear .positive case_48_43_13).check 48 43 13 = true := by
  change case_48_43_13.check 48 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_48_43_14_checked :
    (Witness.linear .positive case_48_43_14).check 48 43 14 = true := by
  change case_48_43_14.check 48 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_48_43_15_checked :
    (Witness.linear .positive case_48_43_15).check 48 43 15 = true := by
  change case_48_43_15.check 48 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_48_43_16_checked :
    (Witness.linear .positive case_48_43_16).check 48 43 16 = true := by
  change case_48_43_16.check 48 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_48_43_17_checked :
    (Witness.linear .positive case_48_43_17).check 48 43 17 = true := by
  change case_48_43_17.check 48 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_48_43_18_checked :
    (Witness.linear .positive case_48_43_18).check 48 43 18 = true := by
  change case_48_43_18.check 48 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_48_43_19_checked :
    (Witness.linear .positive case_48_43_19).check 48 43 19 = true := by
  change case_48_43_19.check 48 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_48_43_20_checked :
    (Witness.linear .positive case_48_43_20).check 48 43 20 = true := by
  change case_48_43_20.check 48 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845] }

theorem case_48_43_21_checked :
    (Witness.linear .positive case_48_43_21).check 48 43 21 = true := by
  change case_48_43_21.check 48 43 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_22 : Certificate := {
  objectiveScale := 15
  eta := 96768360
  rows := #[⟨.assumptionRow 22, 11⟩]
  caps := #[0, 0, 34337160, 11396385, 4242810, 1562275] }

theorem case_48_43_22_checked :
    (Witness.linear .conditional case_48_43_22).check 48 43 22 = true := by
  change case_48_43_22.check 48 43 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 1767263190] }

theorem case_48_43_23_checked :
    (Witness.linear .negative case_48_43_23).check 48 43 23 = true := by
  change case_48_43_23.check 48 43 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_48_43_24_checked :
    (Witness.linear .negative case_48_43_24).check 48 43 24 = true := by
  change case_48_43_24.check 48 43 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_48_43_25_checked :
    (Witness.linear .negative case_48_43_25).check 48 43 25 = true := by
  change case_48_43_25.check 48 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_48_43_26_checked :
    (Witness.linear .negative case_48_43_26).check 48 43 26 = true := by
  change case_48_43_26.check 48 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_48_43_27_checked :
    (Witness.linear .negative case_48_43_27).check 48 43 27 = true := by
  change case_48_43_27.check 48 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_48_43_28_checked :
    (Witness.linear .negative case_48_43_28).check 48 43 28 = true := by
  change case_48_43_28.check 48 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_44_1_checked :
    (Witness.rising).check 48 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_44_2_checked :
    (Witness.rising).check 48 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_44_3_checked :
    (Witness.rising).check 48 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_44_4_checked :
    (Witness.rising).check 48 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_44_5_checked :
    (Witness.rising).check 48 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_44_6_checked :
    (Witness.rising).check 48 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_44_7_checked :
    (Witness.rising).check 48 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_44_8_checked :
    (Witness.rising).check 48 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_48_44_9_checked :
    (Witness.linear .positive case_48_44_9).check 48 44 9 = true := by
  change case_48_44_9.check 48 44 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_48_44_10_checked :
    (Witness.linear .positive case_48_44_10).check 48 44 10 = true := by
  change case_48_44_10.check 48 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_48_44_11_checked :
    (Witness.linear .positive case_48_44_11).check 48 44 11 = true := by
  change case_48_44_11.check 48 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_48_44_12_checked :
    (Witness.linear .positive case_48_44_12).check 48 44 12 = true := by
  change case_48_44_12.check 48 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_48_44_13_checked :
    (Witness.linear .positive case_48_44_13).check 48 44 13 = true := by
  change case_48_44_13.check 48 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_48_44_14_checked :
    (Witness.linear .positive case_48_44_14).check 48 44 14 = true := by
  change case_48_44_14.check 48 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_48_44_15_checked :
    (Witness.linear .positive case_48_44_15).check 48 44 15 = true := by
  change case_48_44_15.check 48 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_48_44_16_checked :
    (Witness.linear .positive case_48_44_16).check 48 44 16 = true := by
  change case_48_44_16.check 48 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_48_44_17_checked :
    (Witness.linear .positive case_48_44_17).check 48 44 17 = true := by
  change case_48_44_17.check 48 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_48_44_18_checked :
    (Witness.linear .positive case_48_44_18).check 48 44 18 = true := by
  change case_48_44_18.check 48 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_48_44_19_checked :
    (Witness.linear .positive case_48_44_19).check 48 44 19 = true := by
  change case_48_44_19.check 48 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_48_44_20_checked :
    (Witness.linear .positive case_48_44_20).check 48 44 20 = true := by
  change case_48_44_20.check 48 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_48_44_21_checked :
    (Witness.linear .positive case_48_44_21).check 48 44 21 = true := by
  change case_48_44_21.check 48 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790] }

theorem case_48_44_22_checked :
    (Witness.linear .positive case_48_44_22).check 48 44 22 = true := by
  change case_48_44_22.check 48 44 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 6564120420] }

theorem case_48_44_23_checked :
    (Witness.linear .negative case_48_44_23).check 48 44 23 = true := by
  change case_48_44_23.check 48 44 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_48_44_24_checked :
    (Witness.linear .negative case_48_44_24).check 48 44 24 = true := by
  change case_48_44_24.check 48 44 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_48_44_25_checked :
    (Witness.linear .negative case_48_44_25).check 48 44 25 = true := by
  change case_48_44_25.check 48 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_48_44_26_checked :
    (Witness.linear .negative case_48_44_26).check 48 44 26 = true := by
  change case_48_44_26.check 48 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_48_44_27_checked :
    (Witness.linear .negative case_48_44_27).check 48 44 27 = true := by
  change case_48_44_27.check 48 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_48_44_28_checked :
    (Witness.linear .negative case_48_44_28).check 48 44 28 = true := by
  change case_48_44_28.check 48 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_45_1_checked :
    (Witness.rising).check 48 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_45_2_checked :
    (Witness.rising).check 48 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_45_3_checked :
    (Witness.rising).check 48 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_45_4_checked :
    (Witness.rising).check 48 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_45_5_checked :
    (Witness.rising).check 48 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_45_6_checked :
    (Witness.rising).check 48 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_45_7_checked :
    (Witness.rising).check 48 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_45_8_checked :
    (Witness.rising).check 48 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_48_45_9_checked :
    (Witness.linear .positive case_48_45_9).check 48 45 9 = true := by
  change case_48_45_9.check 48 45 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_48_45_10_checked :
    (Witness.linear .positive case_48_45_10).check 48 45 10 = true := by
  change case_48_45_10.check 48 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_48_45_11_checked :
    (Witness.linear .positive case_48_45_11).check 48 45 11 = true := by
  change case_48_45_11.check 48 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_48_45_12_checked :
    (Witness.linear .positive case_48_45_12).check 48 45 12 = true := by
  change case_48_45_12.check 48 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_48_45_13_checked :
    (Witness.linear .positive case_48_45_13).check 48 45 13 = true := by
  change case_48_45_13.check 48 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_48_45_14_checked :
    (Witness.linear .positive case_48_45_14).check 48 45 14 = true := by
  change case_48_45_14.check 48 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_48_45_15_checked :
    (Witness.linear .positive case_48_45_15).check 48 45 15 = true := by
  change case_48_45_15.check 48 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_48_45_16_checked :
    (Witness.linear .positive case_48_45_16).check 48 45 16 = true := by
  change case_48_45_16.check 48 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_48_45_17_checked :
    (Witness.linear .positive case_48_45_17).check 48 45 17 = true := by
  change case_48_45_17.check 48 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_48_45_18_checked :
    (Witness.linear .positive case_48_45_18).check 48 45 18 = true := by
  change case_48_45_18.check 48 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_48_45_19_checked :
    (Witness.linear .positive case_48_45_19).check 48 45 19 = true := by
  change case_48_45_19.check 48 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_48_45_20_checked :
    (Witness.linear .positive case_48_45_20).check 48 45 20 = true := by
  change case_48_45_20.check 48 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_48_45_21_checked :
    (Witness.linear .positive case_48_45_21).check 48 45 21 = true := by
  change case_48_45_21.check 48 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700] }

theorem case_48_45_22_checked :
    (Witness.linear .positive case_48_45_22).check 48 45 22 = true := by
  change case_48_45_22.check 48 45 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 24466267020] }

theorem case_48_45_23_checked :
    (Witness.linear .negative case_48_45_23).check 48 45 23 = true := by
  change case_48_45_23.check 48 45 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_48_45_24_checked :
    (Witness.linear .negative case_48_45_24).check 48 45 24 = true := by
  change case_48_45_24.check 48 45 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_48_45_25_checked :
    (Witness.linear .negative case_48_45_25).check 48 45 25 = true := by
  change case_48_45_25.check 48 45 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_48_45_26_checked :
    (Witness.linear .negative case_48_45_26).check 48 45 26 = true := by
  change case_48_45_26.check 48 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_48_45_27_checked :
    (Witness.linear .negative case_48_45_27).check 48 45 27 = true := by
  change case_48_45_27.check 48 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_48_45_28_checked :
    (Witness.linear .negative case_48_45_28).check 48 45 28 = true := by
  change case_48_45_28.check 48 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_48_45_29_checked :
    (Witness.linear .negative case_48_45_29).check 48 45 29 = true := by
  change case_48_45_29.check 48 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_46_1_checked :
    (Witness.rising).check 48 46 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_46_2_checked :
    (Witness.rising).check 48 46 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_46_3_checked :
    (Witness.rising).check 48 46 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_46_4_checked :
    (Witness.rising).check 48 46 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_46_5_checked :
    (Witness.rising).check 48 46 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_46_6_checked :
    (Witness.rising).check 48 46 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_46_7_checked :
    (Witness.rising).check 48 46 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_46_8_checked :
    (Witness.rising).check 48 46 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_48_46_9_checked :
    (Witness.linear .positive case_48_46_9).check 48 46 9 = true := by
  change case_48_46_9.check 48 46 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_48_46_10_checked :
    (Witness.linear .positive case_48_46_10).check 48 46 10 = true := by
  change case_48_46_10.check 48 46 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_48_46_11_checked :
    (Witness.linear .positive case_48_46_11).check 48 46 11 = true := by
  change case_48_46_11.check 48 46 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_48_46_12_checked :
    (Witness.linear .positive case_48_46_12).check 48 46 12 = true := by
  change case_48_46_12.check 48 46 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_48_46_13_checked :
    (Witness.linear .positive case_48_46_13).check 48 46 13 = true := by
  change case_48_46_13.check 48 46 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_48_46_14_checked :
    (Witness.linear .positive case_48_46_14).check 48 46 14 = true := by
  change case_48_46_14.check 48 46 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_48_46_15_checked :
    (Witness.linear .positive case_48_46_15).check 48 46 15 = true := by
  change case_48_46_15.check 48 46 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_48_46_16_checked :
    (Witness.linear .positive case_48_46_16).check 48 46 16 = true := by
  change case_48_46_16.check 48 46 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_48_46_17_checked :
    (Witness.linear .positive case_48_46_17).check 48 46 17 = true := by
  change case_48_46_17.check 48 46 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_48_46_18_checked :
    (Witness.linear .positive case_48_46_18).check 48 46 18 = true := by
  change case_48_46_18.check 48 46 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_48_46_19_checked :
    (Witness.linear .positive case_48_46_19).check 48 46 19 = true := by
  change case_48_46_19.check 48 46 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_48_46_20_checked :
    (Witness.linear .positive case_48_46_20).check 48 46 20 = true := by
  change case_48_46_20.check 48 46 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_48_46_21_checked :
    (Witness.linear .positive case_48_46_21).check 48 46 21 = true := by
  change case_48_46_21.check 48 46 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_48_46_22_checked :
    (Witness.linear .positive case_48_46_22).check 48 46 22 = true := by
  change case_48_46_22.check 48 46 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420] }

theorem case_48_46_23_checked :
    (Witness.linear .positive case_48_46_23).check 48 46 23 = true := by
  change case_48_46_23.check 48 46 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_48_46_24_checked :
    (Witness.linear .negative case_48_46_24).check 48 46 24 = true := by
  change case_48_46_24.check 48 46 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_48_46_25_checked :
    (Witness.linear .negative case_48_46_25).check 48 46 25 = true := by
  change case_48_46_25.check 48 46 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_48_46_26_checked :
    (Witness.linear .negative case_48_46_26).check 48 46 26 = true := by
  change case_48_46_26.check 48 46 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_48_46_27_checked :
    (Witness.linear .negative case_48_46_27).check 48 46 27 = true := by
  change case_48_46_27.check 48 46 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_48_46_28_checked :
    (Witness.linear .negative case_48_46_28).check 48 46 28 = true := by
  change case_48_46_28.check 48 46 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_48_46_29_checked :
    (Witness.linear .negative case_48_46_29).check 48 46 29 = true := by
  change case_48_46_29.check 48 46 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_46_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_48_46_30_checked :
    (Witness.linear .negative case_48_46_30).check 48 46 30 = true := by
  change case_48_46_30.check 48 46 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_47_1_checked :
    (Witness.rising).check 48 47 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_47_2_checked :
    (Witness.rising).check 48 47 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_47_3_checked :
    (Witness.rising).check 48 47 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_47_4_checked :
    (Witness.rising).check 48 47 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_47_5_checked :
    (Witness.rising).check 48 47 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_47_6_checked :
    (Witness.rising).check 48 47 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_47_7_checked :
    (Witness.rising).check 48 47 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_48_47_8_checked :
    (Witness.rising).check 48 47 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_9_checked :
    (Witness.linear .positive case_48_47_9).check 48 47 9 = true := by
  change case_48_47_9.check 48 47 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_10_checked :
    (Witness.linear .positive case_48_47_10).check 48 47 10 = true := by
  change case_48_47_10.check 48 47 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_11_checked :
    (Witness.linear .positive case_48_47_11).check 48 47 11 = true := by
  change case_48_47_11.check 48 47 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_12_checked :
    (Witness.linear .positive case_48_47_12).check 48 47 12 = true := by
  change case_48_47_12.check 48 47 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_13_checked :
    (Witness.linear .positive case_48_47_13).check 48 47 13 = true := by
  change case_48_47_13.check 48 47 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_14_checked :
    (Witness.linear .positive case_48_47_14).check 48 47 14 = true := by
  change case_48_47_14.check 48 47 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_15_checked :
    (Witness.linear .positive case_48_47_15).check 48 47 15 = true := by
  change case_48_47_15.check 48 47 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_16_checked :
    (Witness.linear .positive case_48_47_16).check 48 47 16 = true := by
  change case_48_47_16.check 48 47 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_17_checked :
    (Witness.linear .positive case_48_47_17).check 48 47 17 = true := by
  change case_48_47_17.check 48 47 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_18_checked :
    (Witness.linear .positive case_48_47_18).check 48 47 18 = true := by
  change case_48_47_18.check 48 47 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_19_checked :
    (Witness.linear .positive case_48_47_19).check 48 47 19 = true := by
  change case_48_47_19.check 48 47 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_20_checked :
    (Witness.linear .positive case_48_47_20).check 48 47 20 = true := by
  change case_48_47_20.check 48 47 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_21_checked :
    (Witness.linear .positive case_48_47_21).check 48 47 21 = true := by
  change case_48_47_21.check 48 47 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_22_checked :
    (Witness.linear .positive case_48_47_22).check 48 47 22 = true := by
  change case_48_47_22.check 48 47 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_23_checked :
    (Witness.linear .positive case_48_47_23).check 48 47 23 = true := by
  change case_48_47_23.check 48 47 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_24_checked :
    (Witness.linear .negative case_48_47_24).check 48 47 24 = true := by
  change case_48_47_24.check 48 47 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_25_checked :
    (Witness.linear .negative case_48_47_25).check 48 47 25 = true := by
  change case_48_47_25.check 48 47 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_26_checked :
    (Witness.linear .negative case_48_47_26).check 48 47 26 = true := by
  change case_48_47_26.check 48 47 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_27_checked :
    (Witness.linear .negative case_48_47_27).check 48 47 27 = true := by
  change case_48_47_27.check 48 47 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_28_checked :
    (Witness.linear .negative case_48_47_28).check 48 47 28 = true := by
  change case_48_47_28.check 48 47 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_29_checked :
    (Witness.linear .negative case_48_47_29).check 48 47 29 = true := by
  change case_48_47_29.check 48 47 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_48_47_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_48_47_30_checked :
    (Witness.linear .negative case_48_47_30).check 48 47 30 = true := by
  change case_48_47_30.check 48 47 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_48 (a k : ℕ) (h : Domain 48 a k) :
    ∃ w : Witness, w.check 48 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 24 ≤ a := by omega
  have haHi : a ≤ 47 := by omega
  interval_cases a

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_24_1_checked⟩

    · exact ⟨Witness.rising, case_48_24_2_checked⟩

    · exact ⟨Witness.rising, case_48_24_3_checked⟩

    · exact ⟨Witness.rising, case_48_24_4_checked⟩

    · exact ⟨Witness.rising, case_48_24_5_checked⟩

    · exact ⟨Witness.rising, case_48_24_6_checked⟩

    · exact ⟨Witness.rising, case_48_24_7_checked⟩

    · exact ⟨Witness.rising, case_48_24_8_checked⟩

    · exact ⟨Witness.rising, case_48_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_24_10, case_48_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_24_11, case_48_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_24_12, case_48_24_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_24_13, case_48_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_48_24_14, case_48_24_14_checked⟩

    · exact ⟨Witness.linear .conditional case_48_24_15, case_48_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_25_1_checked⟩

    · exact ⟨Witness.rising, case_48_25_2_checked⟩

    · exact ⟨Witness.rising, case_48_25_3_checked⟩

    · exact ⟨Witness.rising, case_48_25_4_checked⟩

    · exact ⟨Witness.rising, case_48_25_5_checked⟩

    · exact ⟨Witness.rising, case_48_25_6_checked⟩

    · exact ⟨Witness.rising, case_48_25_7_checked⟩

    · exact ⟨Witness.rising, case_48_25_8_checked⟩

    · exact ⟨Witness.rising, case_48_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_25_10, case_48_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_25_11, case_48_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_25_12, case_48_25_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_25_13, case_48_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_48_25_14, case_48_25_14_checked⟩

    · exact ⟨Witness.linear .conditional case_48_25_15, case_48_25_15_checked⟩

    · exact ⟨Witness.linear .conditional case_48_25_16, case_48_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_26_1_checked⟩

    · exact ⟨Witness.rising, case_48_26_2_checked⟩

    · exact ⟨Witness.rising, case_48_26_3_checked⟩

    · exact ⟨Witness.rising, case_48_26_4_checked⟩

    · exact ⟨Witness.rising, case_48_26_5_checked⟩

    · exact ⟨Witness.rising, case_48_26_6_checked⟩

    · exact ⟨Witness.rising, case_48_26_7_checked⟩

    · exact ⟨Witness.rising, case_48_26_8_checked⟩

    · exact ⟨Witness.rising, case_48_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_26_10, case_48_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_26_11, case_48_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_26_12, case_48_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_26_13, case_48_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_48_26_14, case_48_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_48_26_15, case_48_26_15_checked⟩

    · exact ⟨Witness.linear .conditional case_48_26_16, case_48_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_27_1_checked⟩

    · exact ⟨Witness.rising, case_48_27_2_checked⟩

    · exact ⟨Witness.rising, case_48_27_3_checked⟩

    · exact ⟨Witness.rising, case_48_27_4_checked⟩

    · exact ⟨Witness.rising, case_48_27_5_checked⟩

    · exact ⟨Witness.rising, case_48_27_6_checked⟩

    · exact ⟨Witness.rising, case_48_27_7_checked⟩

    · exact ⟨Witness.rising, case_48_27_8_checked⟩

    · exact ⟨Witness.rising, case_48_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_27_10, case_48_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_27_11, case_48_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_27_12, case_48_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_27_13, case_48_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_48_27_14, case_48_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_48_27_15, case_48_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_48_27_16, case_48_27_16_checked⟩

    · exact ⟨Witness.linear .conditional case_48_27_17, case_48_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_28_1_checked⟩

    · exact ⟨Witness.rising, case_48_28_2_checked⟩

    · exact ⟨Witness.rising, case_48_28_3_checked⟩

    · exact ⟨Witness.rising, case_48_28_4_checked⟩

    · exact ⟨Witness.rising, case_48_28_5_checked⟩

    · exact ⟨Witness.rising, case_48_28_6_checked⟩

    · exact ⟨Witness.rising, case_48_28_7_checked⟩

    · exact ⟨Witness.rising, case_48_28_8_checked⟩

    · exact ⟨Witness.rising, case_48_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_28_10, case_48_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_28_11, case_48_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_28_12, case_48_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_28_13, case_48_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_28_14, case_48_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_48_28_15, case_48_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_48_28_16, case_48_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_48_28_17, case_48_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_48_28_18, case_48_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_29_1_checked⟩

    · exact ⟨Witness.rising, case_48_29_2_checked⟩

    · exact ⟨Witness.rising, case_48_29_3_checked⟩

    · exact ⟨Witness.rising, case_48_29_4_checked⟩

    · exact ⟨Witness.rising, case_48_29_5_checked⟩

    · exact ⟨Witness.rising, case_48_29_6_checked⟩

    · exact ⟨Witness.rising, case_48_29_7_checked⟩

    · exact ⟨Witness.rising, case_48_29_8_checked⟩

    · exact ⟨Witness.rising, case_48_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_29_10, case_48_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_29_11, case_48_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_29_12, case_48_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_29_13, case_48_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_29_14, case_48_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_48_29_15, case_48_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_48_29_16, case_48_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_48_29_17, case_48_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_48_29_18, case_48_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_30_1_checked⟩

    · exact ⟨Witness.rising, case_48_30_2_checked⟩

    · exact ⟨Witness.rising, case_48_30_3_checked⟩

    · exact ⟨Witness.rising, case_48_30_4_checked⟩

    · exact ⟨Witness.rising, case_48_30_5_checked⟩

    · exact ⟨Witness.rising, case_48_30_6_checked⟩

    · exact ⟨Witness.rising, case_48_30_7_checked⟩

    · exact ⟨Witness.rising, case_48_30_8_checked⟩

    · exact ⟨Witness.rising, case_48_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_30_10, case_48_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_30_11, case_48_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_30_12, case_48_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_30_13, case_48_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_30_14, case_48_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_48_30_15, case_48_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_48_30_16, case_48_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_48_30_17, case_48_30_17_checked⟩

    · exact ⟨Witness.linear .conditional case_48_30_18, case_48_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_48_30_19, case_48_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_31_1_checked⟩

    · exact ⟨Witness.rising, case_48_31_2_checked⟩

    · exact ⟨Witness.rising, case_48_31_3_checked⟩

    · exact ⟨Witness.rising, case_48_31_4_checked⟩

    · exact ⟨Witness.rising, case_48_31_5_checked⟩

    · exact ⟨Witness.rising, case_48_31_6_checked⟩

    · exact ⟨Witness.rising, case_48_31_7_checked⟩

    · exact ⟨Witness.rising, case_48_31_8_checked⟩

    · exact ⟨Witness.rising, case_48_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_31_10, case_48_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_31_11, case_48_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_31_12, case_48_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_31_13, case_48_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_31_14, case_48_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_31_15, case_48_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_48_31_16, case_48_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_48_31_17, case_48_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_48_31_18, case_48_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_48_31_19, case_48_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_48_31_20, case_48_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_32_1_checked⟩

    · exact ⟨Witness.rising, case_48_32_2_checked⟩

    · exact ⟨Witness.rising, case_48_32_3_checked⟩

    · exact ⟨Witness.rising, case_48_32_4_checked⟩

    · exact ⟨Witness.rising, case_48_32_5_checked⟩

    · exact ⟨Witness.rising, case_48_32_6_checked⟩

    · exact ⟨Witness.rising, case_48_32_7_checked⟩

    · exact ⟨Witness.rising, case_48_32_8_checked⟩

    · exact ⟨Witness.rising, case_48_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_32_10, case_48_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_32_11, case_48_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_32_12, case_48_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_32_13, case_48_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_32_14, case_48_32_14_checked⟩

    · exact ⟨Witness.linear .conditional case_48_32_15, case_48_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_48_32_16, case_48_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_48_32_17, case_48_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_48_32_18, case_48_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_48_32_19, case_48_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_48_32_20, case_48_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_33_1_checked⟩

    · exact ⟨Witness.rising, case_48_33_2_checked⟩

    · exact ⟨Witness.rising, case_48_33_3_checked⟩

    · exact ⟨Witness.rising, case_48_33_4_checked⟩

    · exact ⟨Witness.rising, case_48_33_5_checked⟩

    · exact ⟨Witness.rising, case_48_33_6_checked⟩

    · exact ⟨Witness.rising, case_48_33_7_checked⟩

    · exact ⟨Witness.rising, case_48_33_8_checked⟩

    · exact ⟨Witness.rising, case_48_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_33_10, case_48_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_33_11, case_48_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_33_12, case_48_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_33_13, case_48_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_33_14, case_48_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_33_15, case_48_33_15_checked⟩

    · exact ⟨Witness.linear .conditional case_48_33_16, case_48_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_48_33_17, case_48_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_48_33_18, case_48_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_48_33_19, case_48_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_48_33_20, case_48_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_48_33_21, case_48_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_34_1_checked⟩

    · exact ⟨Witness.rising, case_48_34_2_checked⟩

    · exact ⟨Witness.rising, case_48_34_3_checked⟩

    · exact ⟨Witness.rising, case_48_34_4_checked⟩

    · exact ⟨Witness.rising, case_48_34_5_checked⟩

    · exact ⟨Witness.rising, case_48_34_6_checked⟩

    · exact ⟨Witness.rising, case_48_34_7_checked⟩

    · exact ⟨Witness.rising, case_48_34_8_checked⟩

    · exact ⟨Witness.rising, case_48_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_34_10, case_48_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_34_11, case_48_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_34_12, case_48_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_34_13, case_48_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_34_14, case_48_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_34_15, case_48_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_34_16, case_48_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_48_34_17, case_48_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_48_34_18, case_48_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_48_34_19, case_48_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_48_34_20, case_48_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_48_34_21, case_48_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_48_34_22, case_48_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_35_1_checked⟩

    · exact ⟨Witness.rising, case_48_35_2_checked⟩

    · exact ⟨Witness.rising, case_48_35_3_checked⟩

    · exact ⟨Witness.rising, case_48_35_4_checked⟩

    · exact ⟨Witness.rising, case_48_35_5_checked⟩

    · exact ⟨Witness.rising, case_48_35_6_checked⟩

    · exact ⟨Witness.rising, case_48_35_7_checked⟩

    · exact ⟨Witness.rising, case_48_35_8_checked⟩

    · exact ⟨Witness.rising, case_48_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_35_10, case_48_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_35_11, case_48_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_35_12, case_48_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_35_13, case_48_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_35_14, case_48_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_35_15, case_48_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_35_16, case_48_35_16_checked⟩

    · exact ⟨Witness.linear .conditional case_48_35_17, case_48_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_48_35_18, case_48_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_48_35_19, case_48_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_48_35_20, case_48_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_48_35_21, case_48_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_48_35_22, case_48_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_36_1_checked⟩

    · exact ⟨Witness.rising, case_48_36_2_checked⟩

    · exact ⟨Witness.rising, case_48_36_3_checked⟩

    · exact ⟨Witness.rising, case_48_36_4_checked⟩

    · exact ⟨Witness.rising, case_48_36_5_checked⟩

    · exact ⟨Witness.rising, case_48_36_6_checked⟩

    · exact ⟨Witness.rising, case_48_36_7_checked⟩

    · exact ⟨Witness.rising, case_48_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_36_9, case_48_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_36_10, case_48_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_36_11, case_48_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_36_12, case_48_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_36_13, case_48_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_36_14, case_48_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_36_15, case_48_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_36_16, case_48_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_36_17, case_48_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_48_36_18, case_48_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_48_36_19, case_48_36_19_checked⟩

    · exact ⟨Witness.linear .conditional case_48_36_20, case_48_36_20_checked⟩

    · exact ⟨Witness.linear .conditional case_48_36_21, case_48_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_48_36_22, case_48_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_48_36_23, case_48_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_37_1_checked⟩

    · exact ⟨Witness.rising, case_48_37_2_checked⟩

    · exact ⟨Witness.rising, case_48_37_3_checked⟩

    · exact ⟨Witness.rising, case_48_37_4_checked⟩

    · exact ⟨Witness.rising, case_48_37_5_checked⟩

    · exact ⟨Witness.rising, case_48_37_6_checked⟩

    · exact ⟨Witness.rising, case_48_37_7_checked⟩

    · exact ⟨Witness.rising, case_48_37_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_37_9, case_48_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_37_10, case_48_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_37_11, case_48_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_37_12, case_48_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_37_13, case_48_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_37_14, case_48_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_37_15, case_48_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_37_16, case_48_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_37_17, case_48_37_17_checked⟩

    · exact ⟨Witness.linear .positive case_48_37_18, case_48_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_48_37_19, case_48_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_48_37_20, case_48_37_20_checked⟩

    · exact ⟨Witness.linear .conditional case_48_37_21, case_48_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_48_37_22, case_48_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_48_37_23, case_48_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_48_37_24, case_48_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_38_1_checked⟩

    · exact ⟨Witness.rising, case_48_38_2_checked⟩

    · exact ⟨Witness.rising, case_48_38_3_checked⟩

    · exact ⟨Witness.rising, case_48_38_4_checked⟩

    · exact ⟨Witness.rising, case_48_38_5_checked⟩

    · exact ⟨Witness.rising, case_48_38_6_checked⟩

    · exact ⟨Witness.rising, case_48_38_7_checked⟩

    · exact ⟨Witness.rising, case_48_38_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_38_9, case_48_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_38_10, case_48_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_38_11, case_48_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_38_12, case_48_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_38_13, case_48_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_38_14, case_48_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_38_15, case_48_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_38_16, case_48_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_38_17, case_48_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_48_38_18, case_48_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_48_38_19, case_48_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_48_38_20, case_48_38_20_checked⟩

    · exact ⟨Witness.linear .conditional case_48_38_21, case_48_38_21_checked⟩

    · exact ⟨Witness.linear .negative case_48_38_22, case_48_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_48_38_23, case_48_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_48_38_24, case_48_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_39_1_checked⟩

    · exact ⟨Witness.rising, case_48_39_2_checked⟩

    · exact ⟨Witness.rising, case_48_39_3_checked⟩

    · exact ⟨Witness.rising, case_48_39_4_checked⟩

    · exact ⟨Witness.rising, case_48_39_5_checked⟩

    · exact ⟨Witness.rising, case_48_39_6_checked⟩

    · exact ⟨Witness.rising, case_48_39_7_checked⟩

    · exact ⟨Witness.rising, case_48_39_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_39_9, case_48_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_39_10, case_48_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_39_11, case_48_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_39_12, case_48_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_39_13, case_48_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_39_14, case_48_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_39_15, case_48_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_39_16, case_48_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_39_17, case_48_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_48_39_18, case_48_39_18_checked⟩

    · exact ⟨Witness.linear .positive case_48_39_19, case_48_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_48_39_20, case_48_39_20_checked⟩

    · exact ⟨Witness.linear .conditional case_48_39_21, case_48_39_21_checked⟩

    · exact ⟨Witness.linear .negative case_48_39_22, case_48_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_48_39_23, case_48_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_48_39_24, case_48_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_48_39_25, case_48_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_40_1_checked⟩

    · exact ⟨Witness.rising, case_48_40_2_checked⟩

    · exact ⟨Witness.rising, case_48_40_3_checked⟩

    · exact ⟨Witness.rising, case_48_40_4_checked⟩

    · exact ⟨Witness.rising, case_48_40_5_checked⟩

    · exact ⟨Witness.rising, case_48_40_6_checked⟩

    · exact ⟨Witness.rising, case_48_40_7_checked⟩

    · exact ⟨Witness.rising, case_48_40_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_40_9, case_48_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_40_10, case_48_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_40_11, case_48_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_40_12, case_48_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_40_13, case_48_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_40_14, case_48_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_40_15, case_48_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_40_16, case_48_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_40_17, case_48_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_48_40_18, case_48_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_48_40_19, case_48_40_19_checked⟩

    · exact ⟨Witness.linear .conditional case_48_40_20, case_48_40_20_checked⟩

    · exact ⟨Witness.linear .conditional case_48_40_21, case_48_40_21_checked⟩

    · exact ⟨Witness.linear .negative case_48_40_22, case_48_40_22_checked⟩

    · exact ⟨Witness.linear .negative case_48_40_23, case_48_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_48_40_24, case_48_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_48_40_25, case_48_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_48_40_26, case_48_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_41_1_checked⟩

    · exact ⟨Witness.rising, case_48_41_2_checked⟩

    · exact ⟨Witness.rising, case_48_41_3_checked⟩

    · exact ⟨Witness.rising, case_48_41_4_checked⟩

    · exact ⟨Witness.rising, case_48_41_5_checked⟩

    · exact ⟨Witness.rising, case_48_41_6_checked⟩

    · exact ⟨Witness.rising, case_48_41_7_checked⟩

    · exact ⟨Witness.rising, case_48_41_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_9, case_48_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_10, case_48_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_11, case_48_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_12, case_48_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_13, case_48_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_14, case_48_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_15, case_48_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_16, case_48_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_17, case_48_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_18, case_48_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_19, case_48_41_19_checked⟩

    · exact ⟨Witness.linear .positive case_48_41_20, case_48_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_48_41_21, case_48_41_21_checked⟩

    · exact ⟨Witness.linear .negative case_48_41_22, case_48_41_22_checked⟩

    · exact ⟨Witness.linear .negative case_48_41_23, case_48_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_48_41_24, case_48_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_48_41_25, case_48_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_48_41_26, case_48_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_42_1_checked⟩

    · exact ⟨Witness.rising, case_48_42_2_checked⟩

    · exact ⟨Witness.rising, case_48_42_3_checked⟩

    · exact ⟨Witness.rising, case_48_42_4_checked⟩

    · exact ⟨Witness.rising, case_48_42_5_checked⟩

    · exact ⟨Witness.rising, case_48_42_6_checked⟩

    · exact ⟨Witness.rising, case_48_42_7_checked⟩

    · exact ⟨Witness.rising, case_48_42_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_9, case_48_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_10, case_48_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_11, case_48_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_12, case_48_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_13, case_48_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_14, case_48_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_15, case_48_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_16, case_48_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_17, case_48_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_18, case_48_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_19, case_48_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_20, case_48_42_20_checked⟩

    · exact ⟨Witness.linear .positive case_48_42_21, case_48_42_21_checked⟩

    · exact ⟨Witness.linear .negative case_48_42_22, case_48_42_22_checked⟩

    · exact ⟨Witness.linear .negative case_48_42_23, case_48_42_23_checked⟩

    · exact ⟨Witness.linear .negative case_48_42_24, case_48_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_48_42_25, case_48_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_48_42_26, case_48_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_48_42_27, case_48_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_43_1_checked⟩

    · exact ⟨Witness.rising, case_48_43_2_checked⟩

    · exact ⟨Witness.rising, case_48_43_3_checked⟩

    · exact ⟨Witness.rising, case_48_43_4_checked⟩

    · exact ⟨Witness.rising, case_48_43_5_checked⟩

    · exact ⟨Witness.rising, case_48_43_6_checked⟩

    · exact ⟨Witness.rising, case_48_43_7_checked⟩

    · exact ⟨Witness.rising, case_48_43_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_9, case_48_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_10, case_48_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_11, case_48_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_12, case_48_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_13, case_48_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_14, case_48_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_15, case_48_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_16, case_48_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_17, case_48_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_18, case_48_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_19, case_48_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_20, case_48_43_20_checked⟩

    · exact ⟨Witness.linear .positive case_48_43_21, case_48_43_21_checked⟩

    · exact ⟨Witness.linear .conditional case_48_43_22, case_48_43_22_checked⟩

    · exact ⟨Witness.linear .negative case_48_43_23, case_48_43_23_checked⟩

    · exact ⟨Witness.linear .negative case_48_43_24, case_48_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_48_43_25, case_48_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_48_43_26, case_48_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_48_43_27, case_48_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_48_43_28, case_48_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_44_1_checked⟩

    · exact ⟨Witness.rising, case_48_44_2_checked⟩

    · exact ⟨Witness.rising, case_48_44_3_checked⟩

    · exact ⟨Witness.rising, case_48_44_4_checked⟩

    · exact ⟨Witness.rising, case_48_44_5_checked⟩

    · exact ⟨Witness.rising, case_48_44_6_checked⟩

    · exact ⟨Witness.rising, case_48_44_7_checked⟩

    · exact ⟨Witness.rising, case_48_44_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_9, case_48_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_10, case_48_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_11, case_48_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_12, case_48_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_13, case_48_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_14, case_48_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_15, case_48_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_16, case_48_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_17, case_48_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_18, case_48_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_19, case_48_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_20, case_48_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_21, case_48_44_21_checked⟩

    · exact ⟨Witness.linear .positive case_48_44_22, case_48_44_22_checked⟩

    · exact ⟨Witness.linear .negative case_48_44_23, case_48_44_23_checked⟩

    · exact ⟨Witness.linear .negative case_48_44_24, case_48_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_48_44_25, case_48_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_48_44_26, case_48_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_48_44_27, case_48_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_48_44_28, case_48_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_45_1_checked⟩

    · exact ⟨Witness.rising, case_48_45_2_checked⟩

    · exact ⟨Witness.rising, case_48_45_3_checked⟩

    · exact ⟨Witness.rising, case_48_45_4_checked⟩

    · exact ⟨Witness.rising, case_48_45_5_checked⟩

    · exact ⟨Witness.rising, case_48_45_6_checked⟩

    · exact ⟨Witness.rising, case_48_45_7_checked⟩

    · exact ⟨Witness.rising, case_48_45_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_9, case_48_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_10, case_48_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_11, case_48_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_12, case_48_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_13, case_48_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_14, case_48_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_15, case_48_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_16, case_48_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_17, case_48_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_18, case_48_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_19, case_48_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_20, case_48_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_21, case_48_45_21_checked⟩

    · exact ⟨Witness.linear .positive case_48_45_22, case_48_45_22_checked⟩

    · exact ⟨Witness.linear .negative case_48_45_23, case_48_45_23_checked⟩

    · exact ⟨Witness.linear .negative case_48_45_24, case_48_45_24_checked⟩

    · exact ⟨Witness.linear .negative case_48_45_25, case_48_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_48_45_26, case_48_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_48_45_27, case_48_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_48_45_28, case_48_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_48_45_29, case_48_45_29_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_46_1_checked⟩

    · exact ⟨Witness.rising, case_48_46_2_checked⟩

    · exact ⟨Witness.rising, case_48_46_3_checked⟩

    · exact ⟨Witness.rising, case_48_46_4_checked⟩

    · exact ⟨Witness.rising, case_48_46_5_checked⟩

    · exact ⟨Witness.rising, case_48_46_6_checked⟩

    · exact ⟨Witness.rising, case_48_46_7_checked⟩

    · exact ⟨Witness.rising, case_48_46_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_9, case_48_46_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_10, case_48_46_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_11, case_48_46_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_12, case_48_46_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_13, case_48_46_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_14, case_48_46_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_15, case_48_46_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_16, case_48_46_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_17, case_48_46_17_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_18, case_48_46_18_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_19, case_48_46_19_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_20, case_48_46_20_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_21, case_48_46_21_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_22, case_48_46_22_checked⟩

    · exact ⟨Witness.linear .positive case_48_46_23, case_48_46_23_checked⟩

    · exact ⟨Witness.linear .negative case_48_46_24, case_48_46_24_checked⟩

    · exact ⟨Witness.linear .negative case_48_46_25, case_48_46_25_checked⟩

    · exact ⟨Witness.linear .negative case_48_46_26, case_48_46_26_checked⟩

    · exact ⟨Witness.linear .negative case_48_46_27, case_48_46_27_checked⟩

    · exact ⟨Witness.linear .negative case_48_46_28, case_48_46_28_checked⟩

    · exact ⟨Witness.linear .negative case_48_46_29, case_48_46_29_checked⟩

    · exact ⟨Witness.linear .negative case_48_46_30, case_48_46_30_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_48_47_1_checked⟩

    · exact ⟨Witness.rising, case_48_47_2_checked⟩

    · exact ⟨Witness.rising, case_48_47_3_checked⟩

    · exact ⟨Witness.rising, case_48_47_4_checked⟩

    · exact ⟨Witness.rising, case_48_47_5_checked⟩

    · exact ⟨Witness.rising, case_48_47_6_checked⟩

    · exact ⟨Witness.rising, case_48_47_7_checked⟩

    · exact ⟨Witness.rising, case_48_47_8_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_9, case_48_47_9_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_10, case_48_47_10_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_11, case_48_47_11_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_12, case_48_47_12_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_13, case_48_47_13_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_14, case_48_47_14_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_15, case_48_47_15_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_16, case_48_47_16_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_17, case_48_47_17_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_18, case_48_47_18_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_19, case_48_47_19_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_20, case_48_47_20_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_21, case_48_47_21_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_22, case_48_47_22_checked⟩

    · exact ⟨Witness.linear .positive case_48_47_23, case_48_47_23_checked⟩

    · exact ⟨Witness.linear .negative case_48_47_24, case_48_47_24_checked⟩

    · exact ⟨Witness.linear .negative case_48_47_25, case_48_47_25_checked⟩

    · exact ⟨Witness.linear .negative case_48_47_26, case_48_47_26_checked⟩

    · exact ⟨Witness.linear .negative case_48_47_27, case_48_47_27_checked⟩

    · exact ⟨Witness.linear .negative case_48_47_28, case_48_47_28_checked⟩

    · exact ⟨Witness.linear .negative case_48_47_29, case_48_47_29_checked⟩

    · exact ⟨Witness.linear .negative case_48_47_30, case_48_47_30_checked⟩


#print axioms coverage_48
end ForestUnimodality.FiniteRows.FiniteData
