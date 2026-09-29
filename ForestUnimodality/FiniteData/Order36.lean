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

theorem case_36_18_1_checked :
    (Witness.rising).check 36 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_18_2_checked :
    (Witness.rising).check 36 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_18_3_checked :
    (Witness.rising).check 36 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_18_4_checked :
    (Witness.rising).check 36 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_18_5_checked :
    (Witness.rising).check 36 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_18_6_checked :
    (Witness.rising).check 36 18 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_18_7_checked :
    (Witness.rising).check 36 18 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_18_8_checked :
    (Witness.rising).check 36 18 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_18_9 : Certificate := {
  objectiveScale := 20143200000
  eta := 411332201280
  rows := #[⟨.count 2, 6145787007360⟩, ⟨.count 3, 3565887244920⟩, ⟨.count 4, 713782349280⟩, ⟨.count 5, 171964512720⟩, ⟨.count 6, 52247432160⟩, ⟨.count 7, 21636818280⟩, ⟨.count 8, 20135142720⟩, ⟨.path 9, 1586964960⟩, ⟨.path 10, 5523936880⟩, ⟨.privateRow 4 14, 26615613024⟩, ⟨.privateRow 8 2, 291404960⟩, ⟨.privateRow 10 0, 612890432⟩, ⟨.hall 8 1, 768933088⟩, ⟨.hall 8 2, 57340976⟩, ⟨.hall 1 3, 4666373712⟩, ⟨.hall 7 3, 139416123⟩, ⟨.hall 0 4, 81056639664⟩, ⟨.hall 1 4, 2393012160⟩, ⟨.hall 6 4, 7050120⟩, ⟨.hall 6 5, 88845900⟩, ⟨.hall 5 8, 151476864⟩, ⟨.hall 4 12, 6248420640⟩]
  caps := #[0, 147172262160, 33794560800, 0, 145165440, 0, 0, 93346680, 88795280, 0, 7922992, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_36_18_9_checked :
    (Witness.linear .positive case_36_18_9).check 36 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_18_10 : Certificate := {
  objectiveScale := 12096000
  eta := 0
  rows := #[⟨.count 2, 2098736640⟩, ⟨.count 3, 4563238680⟩, ⟨.count 4, 998917920⟩, ⟨.count 5, 245765520⟩, ⟨.count 6, 75841920⟩, ⟨.count 7, 26583480⟩, ⟨.count 8, 12136320⟩, ⟨.count 9, 12065760⟩, ⟨.path 11, 2352000⟩, ⟨.path 12, 1343880⟩, ⟨.privateRow 10 3, 416304⟩, ⟨.privateRow 11 0, 293265⟩, ⟨.privateRow 12 0, 190080⟩, ⟨.hall 9 2, 150192⟩, ⟨.hall 8 3, 115920⟩, ⟨.hall 0 4, 71062992⟩, ⟨.hall 1 4, 5011776⟩, ⟨.hall 8 4, 54208⟩, ⟨.hall 7 5, 96600⟩, ⟨.hall 0 6, 3908520⟩, ⟨.hall 7 6, 59472⟩, ⟨.hall 6 7, 192696⟩, ⟨.hall 5 10, 1374240⟩, ⟨.hall 4 13, 71351280⟩]
  caps := #[0, 0, 29789760, 1081080, 0, 185520, 93960, 0, 0, 30240, 0, 5880, 13320, 0, 0, 0, 0, 0, 0] }

theorem case_36_18_10_checked :
    (Witness.linear .positive case_36_18_10).check 36 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_18_11 : Certificate := {
  objectiveScale := 3675000
  eta := 0
  rows := #[⟨.count 2, 2310628320⟩, ⟨.count 3, 641350710⟩, ⟨.count 4, 188684496⟩, ⟨.count 5, 63963900⟩, ⟨.count 6, 23617440⟩, ⟨.count 7, 9847530⟩, ⟨.count 8, 5397840⟩, ⟨.count 9, 4159512⟩, ⟨.count 10, 4163040⟩, ⟨.count 12, 2411640⟩, ⟨.path 10, 741020⟩, ⟨.privateRow 3 15, 30270240⟩, ⟨.privateRow 12 0, 183150⟩, ⟨.hall 10 1, 265860⟩, ⟨.hall 9 2, 86436⟩, ⟨.hall 10 2, 30660⟩, ⟨.hall 0 3, 5423418⟩, ⟨.hall 9 3, 74844⟩, ⟨.hall 0 4, 2090088⟩, ⟨.hall 8 4, 122976⟩, ⟨.hall 7 6, 156891⟩, ⟨.hall 6 7, 170646⟩, ⟨.hall 8 8, 78792⟩, ⟨.hall 5 10, 1226610⟩, ⟨.hall 4 12, 7248780⟩, ⟨.hall 3 14, 77189112⟩, ⟨.assumptionRow 11, 3428880⟩]
  caps := #[0, 33477080, 3783780, 0, 0, 41860, 0, 7070, 7980, 10388, 6860, 41790, 0, 0, 0, 0, 0, 0, 0] }

theorem case_36_18_11_checked :
    (Witness.linear .conditional case_36_18_11).check 36 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_19_1_checked :
    (Witness.rising).check 36 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_19_2_checked :
    (Witness.rising).check 36 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_19_3_checked :
    (Witness.rising).check 36 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_19_4_checked :
    (Witness.rising).check 36 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_19_5_checked :
    (Witness.rising).check 36 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_19_6_checked :
    (Witness.rising).check 36 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_19_7_checked :
    (Witness.rising).check 36 19 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_19_8_checked :
    (Witness.rising).check 36 19 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_19_9 : Certificate := {
  objectiveScale := 4356000000
  eta := 22220374176000
  rows := #[⟨.count 2, 5087960677800⟩, ⟨.count 3, 833264031600⟩, ⟨.count 4, 168095687760⟩, ⟨.count 5, 39956716800⟩, ⟨.count 6, 11792781000⟩, ⟨.count 7, 4855851000⟩, ⟨.count 8, 4379094720⟩, ⟨.path 9, 490089600⟩, ⟨.path 10, 1084406400⟩, ⟨.privateRow 6 7, 482281800⟩, ⟨.privateRow 6 8, 1021270250⟩, ⟨.privateRow 7 4, 130330200⟩, ⟨.privateRow 7 5, 89864775⟩, ⟨.privateRow 7 6, 1434232800⟩, ⟨.privateRow 8 2, 268396128⟩, ⟨.privateRow 8 3, 223663440⟩, ⟨.privateRow 9 0, 171939040⟩, ⟨.privateRow 10 0, 108594486⟩, ⟨.hall 10 6, 34684650⟩, ⟨.hall 5 8, 11288200⟩, ⟨.hall 4 11, 90378288⟩, ⟨.hall 6 12, 608315400⟩, ⟨.hall 3 15, 22409752365⟩]
  caps := #[0, 0, 0, 0, 180235440, 0, 158951650, 0, 0, 19259840, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_36_19_9_checked :
    (Witness.linear .positive case_36_19_9).check 36 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_19_10 : Certificate := {
  objectiveScale := 264000000
  eta := 2020034016000
  rows := #[⟨.count 2, 550699749600⟩, ⟨.count 3, 113266193040⟩, ⟨.count 4, 24872527680⟩, ⟨.count 5, 6342336000⟩, ⟨.count 6, 1770568800⟩, ⟨.count 7, 605404800⟩, ⟨.count 8, 262342080⟩, ⟨.count 9, 262342080⟩, ⟨.path 11, 75424800⟩, ⟨.privateRow 10 0, 4540536⟩, ⟨.privateRow 10 4, 10370360⟩, ⟨.privateRow 11 0, 8408400⟩, ⟨.privateRow 12 0, 14039025⟩, ⟨.privateRow 13 5, 118918800⟩, ⟨.hall 8 3, 1268904⟩, ⟨.hall 8 5, 109200⟩, ⟨.hall 7 7, 968240⟩, ⟨.hall 5 10, 11008800⟩]
  caps := #[0, 0, 0, 0, 17656320, 0, 1980000, 0, 2381760, 1657920, 2475264, 950400, 0, 0, 0, 0, 0, 0] }

theorem case_36_19_10_checked :
    (Witness.linear .positive case_36_19_10).check 36 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_19_11 : Certificate := {
  objectiveScale := 2548000000
  eta := 11514193891200
  rows := #[⟨.count 2, 2770332364800⟩, ⟨.count 3, 781320299760⟩, ⟨.count 4, 231273282240⟩, ⟨.count 5, 73253980800⟩, ⟨.count 6, 25567542000⟩, ⟨.count 7, 10216206000⟩, ⟨.count 8, 5085400320⟩, ⟨.count 9, 3511347840⟩, ⟨.count 10, 3556753200⟩, ⟨.count 12, 2616213600⟩, ⟨.path 10, 566200800⟩, ⟨.privateRow 3 16, 93065852880⟩, ⟨.privateRow 7 7, 1385584200⟩, ⟨.privateRow 8 5, 698377680⟩, ⟨.privateRow 8 6, 1957475520⟩, ⟨.privateRow 9 3, 377537160⟩, ⟨.privateRow 9 4, 1136815680⟩, ⟨.privateRow 9 5, 1066185120⟩, ⟨.privateRow 10 1, 248047800⟩, ⟨.privateRow 10 2, 459729270⟩, ⟨.privateRow 11 0, 166966800⟩, ⟨.hall 7 6, 16407300⟩, ⟨.hall 7 7, 39538590⟩, ⟨.hall 6 8, 121875600⟩, ⟨.hall 5 10, 383308200⟩, ⟨.hall 8 10, 154103040⟩, ⟨.hall 4 12, 1604611008⟩, ⟨.hall 3 14, 9441855423⟩, ⟨.assumptionRow 11, 2955298500⟩]
  caps := #[0, 0, 1620876400, 647329540, 267567300, 0, 0, 86753700, 0, 12734660, 0, 20656300, 0, 0, 0, 0, 0, 0] }

theorem case_36_19_11_checked :
    (Witness.linear .conditional case_36_19_11).check 36 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_19_12 : Certificate := {
  objectiveScale := 73513440000
  eta := 229591294732800
  rows := #[⟨.count 2, 65492388561600⟩, ⟨.count 3, 19390162231440⟩, ⟨.count 4, 6013105338240⟩, ⟨.count 5, 1965014251200⟩, ⟨.count 6, 679264185600⟩, ⟨.count 7, 289459170000⟩, ⟨.count 8, 69984794880⟩, ⟨.count 9, 53517784320⟩, ⟨.count 10, 34735100400⟩, ⟨.count 11, 34367533200⟩, ⟨.count 13, 73586953440⟩, ⟨.path 9, 17902272960⟩, ⟨.privateRow 7 7, 14427012600⟩, ⟨.privateRow 8 3, 2144142000⟩, ⟨.privateRow 8 5, 643242600⟩, ⟨.privateRow 8 6, 42132390300⟩, ⟨.privateRow 9 4, 16842745920⟩, ⟨.privateRow 9 5, 52278946720⟩, ⟨.privateRow 9 6, 26896117248⟩, ⟨.privateRow 10 2, 4776076305⟩, ⟨.privateRow 10 3, 28339431120⟩, ⟨.privateRow 10 4, 29246096880⟩, ⟨.privateRow 11 1, 15966200250⟩, ⟨.privateRow 11 2, 2572970400⟩, ⟨.privateRow 12 0, 4759229475⟩, ⟨.hall 7 7, 2996276010⟩, ⟨.hall 8 7, 152039160⟩, ⟨.hall 7 8, 2149339920⟩, ⟨.hall 8 8, 6763533504⟩, ⟨.hall 6 9, 11997534780⟩, ⟨.hall 5 10, 14310885600⟩, ⟨.hall 4 12, 58399776864⟩, ⟨.hall 3 14, 372380645637⟩, ⟨.hall 2 16, 3852493444800⟩, ⟨.assumptionRow 12, 35311203200⟩]
  caps := #[0, 432623235200, 0, 0, 0, 747015360, 591572800, 177772400, 1874446860, 0, 1332639945, 943670000, 1234931425, 0, 0, 0, 0, 0] }

theorem case_36_19_12_checked :
    (Witness.linear .conditional case_36_19_12).check 36 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_20_1_checked :
    (Witness.rising).check 36 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_20_2_checked :
    (Witness.rising).check 36 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_20_3_checked :
    (Witness.rising).check 36 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_20_4_checked :
    (Witness.rising).check 36 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_20_5_checked :
    (Witness.rising).check 36 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_20_6_checked :
    (Witness.rising).check 36 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_20_7_checked :
    (Witness.rising).check 36 20 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_20_8 : Certificate := {
  objectiveScale := 146649360000
  eta := 582212990759400
  rows := #[⟨.count 2, 93602473604640⟩, ⟨.count 3, 13391799581160⟩, ⟨.count 4, 2439072155520⟩, ⟨.count 5, 569732763600⟩, ⟨.count 6, 193177202400⟩, ⟨.count 7, 146982654000⟩, ⟨.path 8, 46026908928⟩, ⟨.path 9, 22153923990⟩, ⟨.privateRow 4 13, 114331507290⟩, ⟨.privateRow 4 14, 20017637640⟩, ⟨.privateRow 5 9, 31896235800⟩, ⟨.privateRow 5 11, 116718225624⟩, ⟨.privateRow 5 12, 2309727420⟩, ⟨.privateRow 6 5, 4689446580⟩, ⟨.privateRow 6 6, 12287438800⟩, ⟨.privateRow 6 7, 20035135575⟩, ⟨.privateRow 6 8, 9098926200⟩, ⟨.privateRow 7 2, 3254615910⟩, ⟨.privateRow 7 3, 7979058360⟩, ⟨.privateRow 7 4, 209975220⟩, ⟨.privateRow 8 0, 3542658840⟩, ⟨.privateRow 9 0, 1850892680⟩, ⟨.hall 3 14, 3002645646⟩]
  caps := #[0, 951263156844, 0, 10236650424, 5554498950, 4524171366, 0, 260398944, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_36_20_8_checked :
    (Witness.linear .positive case_36_20_8).check 36 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_20_9 : Certificate := {
  objectiveScale := 4443120000
  eta := 28588531411440
  rows := #[⟨.count 2, 5305619343024⟩, ⟨.count 3, 890402136624⟩, ⟨.count 4, 180005009184⟩, ⟨.count 5, 42454011600⟩, ⟨.count 6, 12350257920⟩, ⟨.count 7, 5043021984⟩, ⟨.count 8, 4482686208⟩, ⟨.path 9, 592490052⟩, ⟨.path 10, 1036680876⟩, ⟨.privateRow 5 11, 4717112400⟩, ⟨.privateRow 6 9, 1107806700⟩, ⟨.privateRow 6 11, 8137018890⟩, ⟨.privateRow 7 7, 2297295000⟩, ⟨.privateRow 8 5, 377726349⟩, ⟨.privateRow 9 0, 121739618⟩, ⟨.privateRow 10 0, 93562560⟩, ⟨.hall 7 3, 8816472⟩, ⟨.hall 8 3, 1819272⟩, ⟨.hall 4 11, 24622290⟩, ⟨.hall 3 15, 3273537267⟩]
  caps := #[0, 19592381952, 0, 0, 394427880, 245963718, 0, 0, 15341667, 0, 7492716, 0, 0, 0, 0, 0, 0] }

theorem case_36_20_9_checked :
    (Witness.linear .positive case_36_20_9).check 36 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_20_10 : Certificate := {
  objectiveScale := 60500000
  eta := 581661580500
  rows := #[⟨.count 2, 125891405640⟩, ⟨.count 3, 25971865920⟩, ⟨.count 4, 5708102400⟩, ⟨.count 5, 1456755300⟩, ⟨.count 6, 405405000⟩, ⟨.count 7, 139999860⟩, ⟨.count 8, 60540480⟩, ⟨.count 9, 60540480⟩, ⟨.path 11, 17285400⟩, ⟨.privateRow 10 0, 1277640⟩, ⟨.privateRow 11 0, 1711710⟩, ⟨.hall 9 3, 108108⟩, ⟨.hall 8 4, 196196⟩, ⟨.hall 7 6, 174825⟩, ⟨.hall 6 7, 180675⟩]
  caps := #[0, 0, 165668360, 0, 0, 0, 2002000, 0, 1354760, 0, 165760, 168300, 0, 0, 0, 0, 0] }

theorem case_36_20_10_checked :
    (Witness.linear .positive case_36_20_10).check 36 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_20_11 : Certificate := {
  objectiveScale := 216000000
  eta := 2077749273600
  rows := #[⟨.count 2, 471822230880⟩, ⟨.count 3, 121202040960⟩, ⟨.count 4, 31489698240⟩, ⟨.count 5, 9711702000⟩, ⟨.count 6, 3221618400⟩, ⟨.count 7, 1210809600⟩, ⟨.count 8, 551591040⟩, ⟨.count 9, 348107760⟩, ⟨.count 10, 324324000⟩, ⟨.path 10, 61716600⟩, ⟨.privateRow 5 12, 1520178660⟩, ⟨.privateRow 6 9, 117717600⟩, ⟨.privateRow 6 10, 645765120⟩, ⟨.privateRow 6 11, 1430629200⟩, ⟨.privateRow 7 7, 98223840⟩, ⟨.privateRow 7 8, 327206880⟩, ⟨.privateRow 7 9, 666810144⟩, ⟨.privateRow 7 10, 847026180⟩, ⟨.privateRow 8 5, 62432370⟩, ⟨.privateRow 8 6, 182822640⟩, ⟨.privateRow 8 7, 349509160⟩, ⟨.privateRow 8 8, 215255040⟩, ⟨.privateRow 9 3, 38678640⟩, ⟨.privateRow 9 4, 112252140⟩, ⟨.privateRow 9 5, 109068960⟩, ⟨.privateRow 10 1, 27459432⟩, ⟨.privateRow 10 2, 45165120⟩, ⟨.privateRow 11 0, 25225200⟩, ⟨.privateRow 12 0, 23783760⟩, ⟨.hall 5 12, 64236480⟩, ⟨.hall 5 13, 45302400⟩, ⟨.hall 6 13, 727412400⟩, ⟨.hall 4 14, 1039746708⟩, ⟨.hall 3 15, 1410674265⟩, ⟨.hall 2 17, 13547053520⟩, ⟨.assumptionRow 11, 292505400⟩]
  caps := #[0, 0, 266460480, 0, 0, 34002540, 34354320, 13220064, 2991360, 6114240, 21172968, 0, 1946160, 0, 0, 0, 0] }

theorem case_36_20_11_checked :
    (Witness.linear .conditional case_36_20_11).check 36 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_20_12 : Certificate := {
  objectiveScale := 6406936200000
  eta := 36356784143179500
  rows := #[⟨.count 2, 9354502298461320⟩, ⟨.count 3, 2481806732244840⟩, ⟨.count 4, 732534670707840⟩, ⟨.count 5, 225317759366700⟩, ⟨.count 6, 72640927359000⟩, ⟨.count 7, 24187465542240⟩, ⟨.count 8, 10749984685440⟩, ⟨.count 9, 7970869326420⟩, ⟨.count 11, 4319190275400⟩, ⟨.count 13, 5614947358020⟩, ⟨.path 8, 1035500514048⟩, ⟨.path 9, 873330780960⟩, ⟨.privateRow 2 18, 602671016427480⟩, ⟨.privateRow 5 11, 3685709035008⟩, ⟨.privateRow 5 12, 53701932424140⟩, ⟨.privateRow 6 9, 2214130368450⟩, ⟨.privateRow 6 10, 21766101296940⟩, ⟨.privateRow 6 11, 55511411380425⟩, ⟨.privateRow 7 7, 757260632700⟩, ⟨.privateRow 7 8, 9135741855240⟩, ⟨.privateRow 7 9, 24925654425672⟩, ⟨.privateRow 7 10, 38941426869345⟩, ⟨.privateRow 7 11, 10601648857800⟩, ⟨.privateRow 8 6, 3882908429400⟩, ⟨.privateRow 8 7, 11885044621450⟩, ⟨.privateRow 8 8, 20278380202080⟩, ⟨.privateRow 8 9, 14361307665705⟩, ⟨.privateRow 9 4, 1244493965715⟩, ⟨.privateRow 9 5, 6046866385560⟩, ⟨.privateRow 9 6, 11202990668870⟩, ⟨.privateRow 10 0, 210605145660⟩, ⟨.privateRow 10 2, 104707643040⟩, ⟨.privateRow 10 3, 2935086118965⟩, ⟨.privateRow 10 4, 3096354587040⟩, ⟨.privateRow 11 1, 1541529189200⟩, ⟨.privateRow 11 2, 212687399925⟩, ⟨.privateRow 12 0, 415922026520⟩, ⟨.hall 5 13, 26028263302470⟩, ⟨.hall 6 13, 88767774166500⟩, ⟨.hall 4 14, 50016223389132⟩, ⟨.hall 3 15, 72003442591080⟩, ⟨.hall 2 17, 1055402142294500⟩, ⟨.assumptionRow 12, 4196412457200⟩]
  caps := #[0, 0, 9529737327864, 2418347335404, 371615474736, 919683940032, 0, 167936509026, 0, 47345950980, 76167357345, 27563627450, 307704370360, 791988841980, 0, 0, 0] }

theorem case_36_20_12_checked :
    (Witness.linear .conditional case_36_20_12).check 36 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_21_1_checked :
    (Witness.rising).check 36 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_21_2_checked :
    (Witness.rising).check 36 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_21_3_checked :
    (Witness.rising).check 36 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_21_4_checked :
    (Witness.rising).check 36 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_21_5_checked :
    (Witness.rising).check 36 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_21_6_checked :
    (Witness.rising).check 36 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_21_7_checked :
    (Witness.rising).check 36 21 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_36_21_8_checked :
    (Witness.linear .positive case_36_21_8).check 36 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_21_9 : Certificate := {
  objectiveScale := 1061775000
  eta := 15416466745680
  rows := #[⟨.count 2, 2817329074560⟩, ⟨.count 3, 531281630880⟩, ⟨.count 4, 105124219200⟩, ⟨.count 5, 22237815600⟩, ⟨.count 6, 5292967680⟩, ⟨.count 7, 1629547920⟩, ⟨.count 8, 1029188160⟩, ⟨.path 9, 530887500⟩, ⟨.privateRow 3 18, 58222644480⟩, ⟨.privateRow 5 12, 2639132496⟩, ⟨.privateRow 5 13, 4079995920⟩, ⟨.privateRow 5 14, 5182697520⟩, ⟨.privateRow 7 12, 620780160⟩, ⟨.privateRow 9 11, 2591348760⟩, ⟨.hall 9 3, 1837836⟩, ⟨.hall 7 4, 7347060⟩, ⟨.hall 6 7, 604044⟩, ⟨.hall 8 7, 1232840⟩, ⟨.hall 4 13, 38606139⟩]
  caps := #[0, 16432879320, 0, 136756620, 19027008, 59459400, 15907320, 0, 78069420, 0, 0, 0, 0, 0, 0, 0] }

theorem case_36_21_9_checked :
    (Witness.linear .positive case_36_21_9).check 36 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_21_10 : Certificate := {
  objectiveScale := 108900000
  eta := 1526929283880
  rows := #[⟨.count 2, 353042169480⟩, ⟨.count 3, 77832354600⟩, ⟨.count 4, 19137998880⟩, ⟨.count 5, 4563959400⟩, ⟨.count 6, 1268106840⟩, ⟨.count 7, 357357000⟩, ⟨.count 8, 142942800⟩, ⟨.count 9, 110270160⟩, ⟨.path 10, 36301815⟩, ⟨.privateRow 9 11, 396155760⟩, ⟨.privateRow 10 8, 16846830⟩, ⟨.privateRow 10 9, 87807720⟩, ⟨.privateRow 11 6, 13477464⟩, ⟨.privateRow 11 8, 55135080⟩, ⟨.hall 10 9, 33136740⟩, ⟨.hall 7 11, 15459290⟩, ⟨.hall 9 11, 237387150⟩, ⟨.hall 4 13, 25610013⟩]
  caps := #[0, 0, 0, 42824925, 67387320, 10297980, 2456685, 8348340, 2259015, 2061015, 0, 0, 0, 0, 0, 0] }

theorem case_36_21_10_checked :
    (Witness.linear .positive case_36_21_10).check 36 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_21_11 : Certificate := {
  objectiveScale := 40698000000
  eta := 659927798449920
  rows := #[⟨.count 2, 147804652195200⟩, ⟨.count 3, 35491553697600⟩, ⟨.count 4, 9034213668480⟩, ⟨.count 5, 2528127201600⟩, ⟨.count 6, 796150555200⟩, ⟨.count 7, 280282242240⟩, ⟨.count 8, 117327450240⟩, ⟨.count 9, 92185853760⟩, ⟨.path 9, 17777707200⟩, ⟨.privateRow 4 14, 395630955720⟩, ⟨.privateRow 4 15, 1510823714400⟩, ⟨.privateRow 5 12, 364273797888⟩, ⟨.privateRow 5 13, 667649062080⟩, ⟨.privateRow 5 14, 1122991309440⟩, ⟨.privateRow 6 9, 21549939840⟩, ⟨.privateRow 6 10, 196476920640⟩, ⟨.privateRow 6 11, 338294148192⟩, ⟨.privateRow 6 12, 512260028280⟩, ⟨.privateRow 6 13, 461860439040⟩, ⟨.privateRow 7 7, 26654748120⟩, ⟨.privateRow 7 8, 98171948160⟩, ⟨.privateRow 7 9, 167145058080⟩, ⟨.privateRow 7 10, 278606135808⟩, ⟨.privateRow 8 5, 21003062080⟩, ⟨.privateRow 8 6, 56728636965⟩, ⟨.privateRow 8 7, 93699005400⟩, ⟨.privateRow 8 8, 24171627480⟩, ⟨.privateRow 9 3, 15084957888⟩, ⟨.privateRow 9 4, 38281443200⟩, ⟨.privateRow 9 5, 4073869800⟩, ⟨.privateRow 10 0, 3026303280⟩, ⟨.privateRow 10 1, 8888443200⟩, ⟨.privateRow 10 2, 2933186256⟩, ⟨.privateRow 11 0, 4317243840⟩, ⟨.privateRow 12 0, 3841077240⟩, ⟨.hall 4 15, 70721010360⟩, ⟨.hall 4 16, 719411172480⟩, ⟨.hall 3 17, 5223865046400⟩, ⟨.hall 2 18, 7779192220800⟩, ⟨.assumptionRow 11, 53326124280⟩]
  caps := #[0, 300786127200, 117526986720, 85445371440, 25923114360, 14000418432, 6382233000, 6750397368, 1959919920, 1755837424, 0, 0, 2287227600, 0, 0, 0] }

theorem case_36_21_11_checked :
    (Witness.linear .conditional case_36_21_11).check 36 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_21_12 : Certificate := {
  objectiveScale := 82534440270240000
  eta := 1476778422950370540000
  rows := #[⟨.count 2, 315046063562745715200⟩, ⟨.count 3, 76208257957966374240⟩, ⟨.count 4, 18435387785402427840⟩, ⟨.count 5, 4543933609078063200⟩, ⟨.count 6, 1239254620657653600⟩, ⟨.count 7, 339647562698764320⟩, ⟨.count 8, 128515293994127040⟩, ⟨.count 9, 59012124793221600⟩, ⟨.count 10, 78682833057628800⟩, ⟨.path 7, 43852822636998375⟩, ⟨.path 8, 26092314776848320⟩, ⟨.privateRow 2 19, 12095518511783987280⟩, ⟨.privateRow 4 14, 1141392847042227780⟩, ⟨.privateRow 4 15, 4064296172564267640⟩, ⟨.privateRow 5 12, 796270270543203456⟩, ⟨.privateRow 5 13, 1743808287639698280⟩, ⟨.privateRow 5 14, 3311235891175212000⟩, ⟨.privateRow 6 10, 398331842354245800⟩, ⟨.privateRow 6 11, 817908049634051376⟩, ⟨.privateRow 6 12, 1490547918735455580⟩, ⟨.privateRow 6 13, 1726432495339471920⟩, ⟨.privateRow 7 7, 5901212479322160⟩, ⟨.privateRow 7 8, 169730111310027840⟩, ⟨.privateRow 7 9, 399971068042946400⟩, ⟨.privateRow 7 10, 743290496284400064⟩, ⟨.privateRow 7 11, 844856919956289240⟩, ⟨.privateRow 8 5, 382485994030140⟩, ⟨.privateRow 8 6, 75732226817967720⟩, ⟨.privateRow 8 7, 121138778394974340⟩, ⟨.privateRow 8 8, 560724467248185240⟩, ⟨.privateRow 8 9, 87665789831708088⟩, ⟨.privateRow 9 4, 28704663171023840⟩, ⟨.privateRow 9 5, 106385747196668940⟩, ⟨.privateRow 9 6, 165795969657146400⟩, ⟨.privateRow 10 2, 8064990388406952⟩, ⟨.privateRow 10 3, 57700744242261120⟩, ⟨.privateRow 10 4, 29751946249915890⟩, ⟨.privateRow 11 0, 5722387858736640⟩, ⟨.privateRow 11 1, 19277294099119056⟩, ⟨.privateRow 12 0, 5409444772711980⟩, ⟨.hall 5 15, 1327772807847486000⟩, ⟨.hall 4 16, 7008094804365214560⟩, ⟨.hall 3 17, 16718790644195159520⟩, ⟨.hall 2 18, 26056441347294758400⟩, ⟨.assumptionRow 12, 62559959413171500⟩]
  caps := #[0, 106414482194977320, 0, 0, 11265880673068560, 16462712559036744, 0, 8841632830220619, 2154779739211120, 8651669062243240, 6000826963481658, 0, 8086082523142680, 82534440270240000, 0, 0] }

theorem case_36_21_12_checked :
    (Witness.linear .conditional case_36_21_12).check 36 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_21_13 : Certificate := {
  objectiveScale := 8658619200000
  eta := 525604528423054080
  rows := #[⟨.count 2, 70927058396113920⟩, ⟨.count 3, 8537516288421120⟩, ⟨.count 4, 749348076597120⟩, ⟨.count 11, 496758837294720⟩, ⟨.count 12, 239959777337280⟩, ⟨.count 13, 54727668515520⟩, ⟨.path 4, 750396464737920⟩, ⟨.privateRow 2 19, 6403137216315840⟩, ⟨.privateRow 3 15, 225225405044640⟩, ⟨.privateRow 3 16, 1275575658477120⟩, ⟨.privateRow 4 12, 48588346726920⟩, ⟨.privateRow 4 13, 235960447714992⟩, ⟨.privateRow 4 14, 519123509524620⟩, ⟨.privateRow 4 15, 828633032267040⟩, ⟨.privateRow 5 8, 807945378240⟩, ⟨.privateRow 5 9, 5501470174200⟩, ⟨.privateRow 5 10, 34498660173120⟩, ⟨.privateRow 5 11, 101928687981120⟩, ⟨.privateRow 5 12, 198550450530432⟩, ⟨.privateRow 5 13, 328174655608800⟩, ⟨.privateRow 5 14, 563605686483840⟩, ⟨.privateRow 6 5, 86979765600⟩, ⟨.privateRow 6 6, 229626581184⟩, ⟨.privateRow 6 7, 3061687749120⟩, ⟨.privateRow 6 8, 15547633101000⟩, ⟨.privateRow 6 9, 41141429128800⟩, ⟨.privateRow 6 10, 81804469546800⟩, ⟨.privateRow 6 11, 137469779935488⟩, ⟨.privateRow 6 12, 245556925253640⟩, ⟨.privateRow 6 13, 283397472277920⟩, ⟨.privateRow 7 5, 1760470455744⟩, ⟨.privateRow 7 6, 6250945821120⟩, ⟨.privateRow 7 7, 17413349073120⟩, ⟨.privateRow 7 8, 36284644693440⟩, ⟨.privateRow 7 9, 63296141868960⟩, ⟨.privateRow 7 10, 116777873564352⟩, ⟨.privateRow 7 11, 138126767098320⟩, ⟨.privateRow 8 3, 882844620840⟩, ⟨.privateRow 8 4, 2790600813000⟩, ⟨.privateRow 8 5, 7776474265560⟩, ⟨.privateRow 8 6, 17566832117835⟩, ⟨.privateRow 8 7, 15228707293800⟩, ⟨.privateRow 8 8, 97001284259880⟩, ⟨.privateRow 8 9, 9889889281272⟩, ⟨.privateRow 9 1, 499650431280⟩, ⟨.privateRow 9 2, 1577233082880⟩, ⟨.privateRow 9 3, 3814352654112⟩, ⟨.privateRow 9 4, 9298459089920⟩, ⟨.privateRow 9 5, 18768783753720⟩, ⟨.privateRow 9 6, 21413589912000⟩, ⟨.privateRow 10 0, 1801930810680⟩, ⟨.privateRow 10 1, 2244077952480⟩, ⟨.privateRow 10 2, 5377089109392⟩, ⟨.privateRow 10 3, 7292770124640⟩, ⟨.privateRow 11 0, 1391676249600⟩, ⟨.hall 5 15, 194823802473300⟩, ⟨.hall 4 16, 1140613761006720⟩, ⟨.hall 3 17, 2991077575405920⟩, ⟨.hall 2 18, 5562059363340480⟩]
  caps := #[0, 167429279888640, 0, 14298597593280, 2056917304728, 61852277760, 0, 244742056416, 0, 1885708657216, 0, 0, 0, 5882665884480, 8658619200000, 0] }

theorem case_36_21_13_checked :
    (Witness.linear .negative case_36_21_13).check 36 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_22_1_checked :
    (Witness.rising).check 36 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_22_2_checked :
    (Witness.rising).check 36 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_22_3_checked :
    (Witness.rising).check 36 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_22_4_checked :
    (Witness.rising).check 36 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_22_5_checked :
    (Witness.rising).check 36 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_22_6_checked :
    (Witness.rising).check 36 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_22_7_checked :
    (Witness.rising).check 36 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_36_22_8_checked :
    (Witness.linear .positive case_36_22_8).check 36 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_36_22_9_checked :
    (Witness.linear .positive case_36_22_9).check 36 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_22_10 : Certificate := {
  objectiveScale := 4890600000
  eta := 102764180478960
  rows := #[⟨.count 2, 23768585961120⟩, ⟨.count 3, 5243070432600⟩, ⟨.count 4, 1290601952640⟩, ⟨.count 5, 307984556880⟩, ⟨.count 6, 86366039760⟩, ⟨.count 7, 24239525310⟩, ⟨.count 8, 9777287520⟩, ⟨.count 9, 7332965640⟩, ⟨.path 9, 2445267825⟩, ⟨.hall 9 6, 7407036⟩, ⟨.hall 7 8, 80211236⟩, ⟨.hall 6 9, 17479791⟩, ⟨.hall 6 12, 477896265⟩]
  caps := #[0, 0, 8885499480, 2001445875, 490964760, 119189070, 0, 213281640, 3848130, 2902185, 0, 0, 0, 0, 0] }

theorem case_36_22_10_checked :
    (Witness.linear .positive case_36_22_10).check 36 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_22_11 : Certificate := {
  objectiveScale := 2468812500
  eta := 67161235541400
  rows := #[⟨.count 2, 13943110381200⟩, ⟨.count 3, 3053656405800⟩, ⟨.count 4, 775199224800⟩, ⟨.count 5, 195545750400⟩, ⟨.count 6, 59362102800⟩, ⟨.count 7, 20369349000⟩, ⟨.count 8, 8147739600⟩, ⟨.count 9, 5237832600⟩, ⟨.path 8, 476501025⟩, ⟨.path 9, 1030275675⟩, ⟨.privateRow 2 20, 384107724000⟩, ⟨.privateRow 3 17, 89625135600⟩, ⟨.privateRow 3 18, 377705928600⟩, ⟨.privateRow 4 15, 116323532325⟩, ⟨.privateRow 4 16, 167610643200⟩, ⟨.privateRow 4 17, 233956522800⟩, ⟨.privateRow 5 12, 16644668040⟩, ⟨.privateRow 5 13, 55730538864⟩, ⟨.privateRow 5 14, 81535594140⟩, ⟨.privateRow 5 15, 106735388760⟩, ⟨.privateRow 5 16, 61806424680⟩, ⟨.privateRow 6 10, 15214656600⟩, ⟨.privateRow 6 11, 27191464300⟩, ⟨.privateRow 6 12, 38759961240⟩, ⟨.privateRow 6 13, 44327583300⟩, ⟨.privateRow 7 7, 1196295100⟩, ⟨.privateRow 7 8, 8875216350⟩, ⟨.privateRow 7 9, 15775852950⟩, ⟨.privateRow 7 10, 18962893950⟩, ⟨.privateRow 8 5, 1469503035⟩, ⟨.privateRow 8 6, 5367161800⟩, ⟨.privateRow 8 7, 7711253550⟩, ⟨.privateRow 9 3, 1393228200⟩, ⟨.privateRow 9 4, 2793510720⟩, ⟨.privateRow 10 1, 1163962800⟩, ⟨.privateRow 11 0, 145495350⟩, ⟨.privateRow 12 0, 290990700⟩, ⟨.hall 10 4, 7054320⟩, ⟨.hall 3 18, 128372844600⟩, ⟨.hall 2 19, 355299644700⟩, ⟨.assumptionRow 11, 3450544020⟩]
  caps := #[0, 139438586430, 0, 5121436320, 0, 2260334076, 448308630, 0, 1270679410, 0, 0, 2826603780, 0, 0, 0] }

theorem case_36_22_11_checked :
    (Witness.linear .conditional case_36_22_11).check 36 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_22_12 : Certificate := {
  objectiveScale := 1054335954000000
  eta := 29727087835109464800
  rows := #[⟨.count 2, 6292900296888004800⟩, ⟨.count 3, 1361272549990953600⟩, ⟨.count 4, 309380124997944000⟩, ⟨.count 5, 69474835087257600⟩, ⟨.count 6, 16645012572988800⟩, ⟨.count 7, 4116022130820600⟩, ⟨.count 8, 1447392397651200⟩, ⟨.count 9, 1085544298238400⟩, ⟨.path 7, 1522820678979600⟩, ⟨.privateRow 2 20, 698547755916410400⟩, ⟨.privateRow 3 17, 125048672355406800⟩, ⟨.privateRow 3 18, 251755815166455600⟩, ⟨.privateRow 4 14, 10801165767472080⟩, ⟨.privateRow 4 15, 74631170503890000⟩, ⟨.privateRow 4 16, 112625220942234000⟩, ⟨.privateRow 4 17, 160389170064723600⟩, ⟨.privateRow 5 12, 11669601206062800⟩, ⟨.privateRow 5 13, 32392641859433856⟩, ⟨.privateRow 5 14, 51156275054484600⟩, ⟨.privateRow 5 15, 75553883157392640⟩, ⟨.privateRow 5 16, 56176917433837200⟩, ⟨.privateRow 6 10, 7288654573886400⟩, ⟨.privateRow 6 11, 15097106814389600⟩, ⟨.privateRow 6 12, 15089065745513760⟩, ⟨.privateRow 6 13, 53689211750374200⟩, ⟨.privateRow 6 14, 6452957772861600⟩, ⟨.privateRow 7 7, 95487692900600⟩, ⟨.privateRow 7 8, 3669365883107925⟩, ⟨.privateRow 7 9, 8025273919119600⟩, ⟨.privateRow 7 10, 12227450359324200⟩, ⟨.privateRow 7 11, 13913059422422160⟩, ⟨.privateRow 8 5, 9046202485320⟩, ⟨.privateRow 8 6, 1844420173395800⟩, ⟨.privateRow 8 7, 4630524897173175⟩, ⟨.privateRow 8 8, 7178807829421800⟩, ⟨.privateRow 9 4, 856373835276960⟩, ⟨.privateRow 9 5, 2955092811871200⟩, ⟨.privateRow 9 6, 806619721607700⟩, ⟨.privateRow 10 2, 375006212118720⟩, ⟨.privateRow 10 3, 1009556197361712⟩, ⟨.privateRow 11 1, 370071919854000⟩, ⟨.privateRow 12 0, 90462024853200⟩, ⟨.hall 4 17, 11277599098365600⟩, ⟨.hall 3 18, 105269229973908000⟩, ⟨.hall 2 19, 275239756818346320⟩, ⟨.assumptionRow 12, 890523931876425⟩]
  caps := #[0, 8180924108884800, 3777554732938350, 0, 646355771151090, 124052785702650, 363215989364800, 0, 146824085747885, 0, 817367684342538, 520452012022425, 0, 1054335954000000, 0] }

theorem case_36_22_12_checked :
    (Witness.linear .conditional case_36_22_12).check 36 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_22_13 : Certificate := {
  objectiveScale := 42000695169741000000
  eta := 1535186527865644557103200
  rows := #[⟨.count 2, 306162555414800908824000⟩, ⟨.count 3, 60809244877317599863200⟩, ⟨.count 4, 12236241217667367700800⟩, ⟨.count 5, 2295898509394610920800⟩, ⟨.count 6, 410439956986746086400⟩, ⟨.count 7, 67337805443138029800⟩, ⟨.count 8, 17101664874447753600⟩, ⟨.path 6, 94226330631391358400⟩, ⟨.path 7, 38821685849734788000⟩, ⟨.privateRow 2 20, 35695450009191073701600⟩, ⟨.privateRow 3 17, 5886535563658870520400⟩, ⟨.privateRow 3 18, 12533382644860897419600⟩, ⟨.privateRow 4 14, 448918702954253532000⟩, ⟨.privateRow 4 15, 3355667304583045151700⟩, ⟨.privateRow 4 16, 5496047549025646813200⟩, ⟨.privateRow 4 17, 8474943799343514893400⟩, ⟨.privateRow 5 12, 448491161332392338160⟩, ⟨.privateRow 5 13, 1382156555152867445952⟩, ⟨.privateRow 5 14, 2413258684595508629880⟩, ⟨.privateRow 5 15, 4004354830351941505440⟩, ⟨.privateRow 5 16, 3545175128473019321280⟩, ⟨.privateRow 6 10, 252249556898104365600⟩, ⟨.privateRow 6 11, 601646071208002220400⟩, ⟨.privateRow 6 12, 1072274387627874150720⟩, ⟨.privateRow 6 13, 1895078238899741695800⟩, ⟨.privateRow 6 14, 1927262622100959343200⟩, ⟨.privateRow 7 7, 1425138739537312800⟩, ⟨.privateRow 7 8, 111428035197573644550⟩, ⟨.privateRow 7 9, 291644463483885798000⟩, ⟨.privateRow 7 10, 521422636328214320700⟩, ⟨.privateRow 7 11, 966244065406298078400⟩, ⟨.privateRow 7 12, 550459838146287069000⟩, ⟨.privateRow 8 6, 44654347172169134400⟩, ⟨.privateRow 8 7, 148971533867259728625⟩, ⟨.privateRow 8 8, 292255237229401789200⟩, ⟨.privateRow 8 9, 485081598470012844300⟩, ⟨.privateRow 9 4, 14678929017234321840⟩, ⟨.privateRow 9 5, 78224281925714724800⟩, ⟨.privateRow 9 6, 184021039742755515300⟩, ⟨.privateRow 9 7, 96298660543021279200⟩, ⟨.privateRow 10 2, 3031658773197556320⟩, ⟨.privateRow 10 3, 38735270940624161904⟩, ⟨.privateRow 10 4, 89498712842943243840⟩, ⟨.privateRow 11 1, 14575282563449790000⟩, ⟨.privateRow 11 2, 27576434610047002680⟩, ⟨.privateRow 12 0, 10688540546529846000⟩, ⟨.hall 4 17, 1389510271048879980000⟩, ⟨.hall 3 18, 6293300162843651958000⟩, ⟨.hall 2 19, 14645010715233333795360⟩, ⟨.assumptionRow 13, 14383436963896690200⟩]
  caps := #[0, 0, 218414293719161117760, 0, 44569269753475767300, 2238169075705858680, 8807827770644502600, 0, 7412256521506711875, 183872795415828120, 601049771898568776, 0, 47259992135753422200, 321622124394031309800, 42000695169741000000] }

theorem case_36_22_13_checked :
    (Witness.linear .conditional case_36_22_13).check 36 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_22_14 : Certificate := {
  objectiveScale := 2728869528000000
  eta := 105713560395350107200
  rows := #[⟨.count 2, 23392394082739281600⟩, ⟨.count 3, 4970435955559074000⟩, ⟨.count 4, 1051892424993009600⟩, ⟨.count 5, 221451036840633600⟩, ⟨.count 6, 41250683333059200⟩, ⟨.count 7, 5699107565751600⟩, ⟨.path 7, 5458036320336600⟩, ⟨.privateRow 7 8, 882004742318700⟩, ⟨.privateRow 7 9, 7967119760285400⟩, ⟨.privateRow 8 6, 527695144977000⟩, ⟨.privateRow 8 7, 2900438671855725⟩, ⟨.privateRow 9 5, 683490854446400⟩, ⟨.privateRow 10 3, 32566328947152⟩, ⟨.privateRow 12 3, 746311705038900⟩, ⟨.hall 10 4, 157897352471040⟩, ⟨.hall 8 5, 175501750514400⟩, ⟨.hall 9 5, 141449711588640⟩, ⟨.hall 11 6, 71077305241800⟩, ⟨.hall 7 7, 113488722088560⟩, ⟨.hall 6 9, 58493052533700⟩, ⟨.hall 5 11, 301252576947300⟩, ⟨.hall 6 12, 901687688385660⟩, ⟨.hall 4 13, 808608872574360⟩, ⟨.hall 3 16, 21743934010999200⟩, ⟨.hall 2 18, 186750756338786640⟩]
  caps := #[0, 68944475616508800, 0, 0, 1516610969042400, 444027752968800, 0, 0, 149018448293715, 0, 0, 0, 5508734805304500, 73679477256000000, 19102086696000000] }

theorem case_36_22_14_checked :
    (Witness.linear .negative case_36_22_14).check 36 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_23_1_checked :
    (Witness.rising).check 36 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_23_2_checked :
    (Witness.rising).check 36 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_23_3_checked :
    (Witness.rising).check 36 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_23_4_checked :
    (Witness.rising).check 36 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_23_5_checked :
    (Witness.rising).check 36 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_23_6_checked :
    (Witness.rising).check 36 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_23_7_checked :
    (Witness.rising).check 36 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_36_23_8_checked :
    (Witness.linear .positive case_36_23_8).check 36 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_36_23_9_checked :
    (Witness.linear .positive case_36_23_9).check 36 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_36_23_10_checked :
    (Witness.linear .positive case_36_23_10).check 36 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_23_11 : Certificate := {
  objectiveScale := 202777435000
  eta := 38412483967006380
  rows := #[⟨.count 2, 5014458856822800⟩, ⟨.count 3, 697937220197280⟩, ⟨.count 4, 111292691869296⟩, ⟨.count 5, 21221064127620⟩, ⟨.count 6, 4126318024815⟩, ⟨.count 7, 982456672575⟩, ⟨.count 8, 523976892040⟩, ⟨.path 3, 115727752675080⟩, ⟨.path 6, 1279545691710⟩]
  caps := #[0, 8015647270660, 0, 0, 0, 91045059480, 0, 31430502425, 0, 202777435000, 202777435000, 0, 0, 0] }

theorem case_36_23_11_checked :
    (Witness.linear .positive case_36_23_11).check 36 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_23_12 : Certificate := {
  objectiveScale := 177046408000000
  eta := 13638165108113145600
  rows := #[⟨.count 2, 2395045866378765600⟩, ⟨.count 3, 407889907374549600⟩, ⟨.count 4, 77964970640356800⟩, ⟨.count 5, 13733666914968000⟩, ⟨.count 6, 2376980812206000⟩, ⟨.count 7, 475396162441200⟩, ⟨.count 8, 211287183307200⟩, ⟨.path 6, 1182151880395200⟩, ⟨.privateRow 2 21, 214403669260981200⟩, ⟨.privateRow 3 7, 339568687458000⟩, ⟨.privateRow 3 17, 4833194318152200⟩, ⟨.privateRow 3 18, 57892688226172800⟩, ⟨.privateRow 3 19, 77648039865396000⟩, ⟨.privateRow 4 15, 13938615482775984⟩, ⟨.privateRow 4 16, 27454128380979300⟩, ⟨.privateRow 4 17, 34862385245688000⟩, ⟨.privateRow 4 18, 42120099992290320⟩, ⟨.privateRow 5 12, 1859327213103360⟩, ⟨.privateRow 5 13, 7965526810681440⟩, ⟨.privateRow 5 14, 12280011093814464⟩, ⟨.privateRow 5 15, 15772588233882480⟩, ⟨.privateRow 5 16, 19748308733112960⟩, ⟨.privateRow 6 9, 52821795826800⟩, ⟨.privateRow 6 10, 1627571583913275⟩, ⟨.privateRow 6 11, 4014456482836800⟩, ⟨.privateRow 6 12, 6232971907562400⟩, ⟨.privateRow 6 13, 7770086166122280⟩, ⟨.privateRow 6 14, 3222129545434800⟩, ⟨.privateRow 7 7, 56594781243000⟩, ⟨.privateRow 7 8, 1058951240146800⟩, ⟨.privateRow 7 9, 2294918379403650⟩, ⟨.privateRow 7 10, 3596194099555200⟩, ⟨.privateRow 7 11, 1388458633161600⟩, ⟨.privateRow 8 5, 19207925755200⟩, ⟨.privateRow 8 6, 697247704913760⟩, ⟨.privateRow 8 7, 1578784786378800⟩, ⟨.privateRow 8 8, 600847927529850⟩, ⟨.privateRow 9 4, 484039729031040⟩, ⟨.privateRow 9 5, 439477341278976⟩, ⟨.privateRow 10 2, 253544619968640⟩, ⟨.privateRow 11 0, 48758580763200⟩, ⟨.hall 3 19, 12455379455959440⟩, ⟨.hall 2 20, 61424202575736000⟩, ⟨.assumptionRow 12, 163967710294080⟩]
  caps := #[0, 18610583310038720, 2052380145020920, 0, 67701223068160, 6528846324000, 161462058778735, 32404776006460, 26737836554240, 163967710294080, 0, 1271969977259520, 1606496369705920, 177046408000000] }

theorem case_36_23_12_checked :
    (Witness.linear .conditional case_36_23_12).check 36 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_23_13 : Certificate := {
  objectiveScale := 19572734538000000
  eta := 1960845133373057131200
  rows := #[⟨.count 2, 310686971804998588800⟩, ⟨.count 3, 48532944015115560000⟩, ⟨.count 4, 7468363620208370880⟩, ⟨.count 5, 977003055990561600⟩, ⟨.count 6, 104678898856131600⟩, ⟨.count 7, 28548790597126800⟩, ⟨.count 8, 12688351376500800⟩, ⟨.path 5, 328103350722576000⟩, ⟨.path 6, 59116604667120000⟩, ⟨.privateRow 2 21, 30042843971709769200⟩, ⟨.privateRow 3 17, 623315261370601800⟩, ⟨.privateRow 3 18, 7409997203876467200⟩, ⟨.privateRow 3 19, 10705796473922550000⟩, ⟨.privateRow 4 15, 1556480063355353136⟩, ⟨.privateRow 4 16, 3418717674005934300⟩, ⟨.privateRow 4 17, 4786680556784926800⟩, ⟨.privateRow 4 18, 6423477884353530000⟩, ⟨.privateRow 5 12, 165673616544596160⟩, ⟨.privateRow 5 13, 844198311583186560⟩, ⟨.privateRow 5 14, 1478954236444933248⟩, ⟨.privateRow 5 15, 2144331382628635200⟩, ⟨.privateRow 5 16, 3116259098068596480⟩, ⟨.privateRow 5 17, 1383030300038587200⟩, ⟨.privateRow 6 8, 951626353237560⟩, ⟨.privateRow 6 10, 129064324157844075⟩, ⟨.privateRow 6 11, 401495689984989600⟩, ⟨.privateRow 6 12, 719006578001712000⟩, ⟨.privateRow 6 13, 1036321098675702840⟩, ⟨.privateRow 6 14, 1479382468303890150⟩, ⟨.privateRow 7 8, 73562227623284400⟩, ⟨.privateRow 7 9, 210717263931174000⟩, ⟨.privateRow 7 10, 392303108885688000⟩, ⟨.privateRow 7 11, 585929940350554800⟩, ⟨.privateRow 7 12, 266999165394081120⟩, ⟨.privateRow 8 6, 38699471698327440⟩, ⟨.privateRow 8 7, 128293330584619200⟩, ⟨.privateRow 8 8, 251586217137179925⟩, ⟨.privateRow 8 9, 165175145597662200⟩, ⟨.privateRow 9 4, 21454848691174080⟩, ⟨.privateRow 9 5, 90087294773155680⟩, ⟨.privateRow 9 6, 99251104100628480⟩, ⟨.privateRow 10 2, 13798582121944620⟩, ⟨.privateRow 10 3, 56059443354358080⟩, ⟨.privateRow 11 0, 13176364890981600⟩, ⟨.privateRow 11 1, 6344175688250400⟩, ⟨.privateRow 12 0, 8723241571344300⟩, ⟨.hall 3 19, 2543697242203997880⟩, ⟨.hall 2 20, 9211743099339580800⟩, ⟨.assumptionRow 13, 9609294431105600⟩]
  caps := #[0, 652770386427420800, 0, 13344505746182000, 7594066983473828, 0, 8666351736167125, 55071530463040, 0, 15254167727344000, 0, 178211052817459200, 0, 166545316410894400] }

theorem case_36_23_13_checked :
    (Witness.linear .conditional case_36_23_13).check 36 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_23_14 : Certificate := {
  objectiveScale := 4817991855600000
  eta := 765976573266617512800
  rows := #[⟨.count 2, 108005218930485676800⟩, ⟨.count 3, 16103675250124862400⟩, ⟨.count 4, 2476243530923722560⟩, ⟨.count 5, 373144903897365600⟩, ⟨.count 6, 40461495603328800⟩, ⟨.path 3, 1631559629498198400⟩, ⟨.path 6, 41446008096807600⟩, ⟨.privateRow 4 15, 351610396792927272⟩, ⟨.privateRow 4 16, 865876005911236320⟩, ⟨.privateRow 5 13, 273040166626907680⟩, ⟨.privateRow 5 14, 398320945606103520⟩, ⟨.privateRow 5 15, 672784757448683880⟩, ⟨.privateRow 5 16, 600028994058253760⟩, ⟨.privateRow 5 17, 439681585556172960⟩, ⟨.privateRow 6 10, 15875517372139425⟩, ⟨.privateRow 6 11, 113436693030761100⟩, ⟨.privateRow 6 14, 1802362941302448525⟩, ⟨.privateRow 6 17, 368649182163662400⟩, ⟨.privateRow 7 7, 578021365761840⟩, ⟨.privateRow 7 8, 10971701850109000⟩, ⟨.privateRow 7 9, 49252237207623450⟩, ⟨.privateRow 7 10, 75418025818449600⟩, ⟨.privateRow 7 11, 41264303055775800⟩, ⟨.privateRow 7 12, 34006923685654920⟩, ⟨.privateRow 7 14, 2568983847830400⟩, ⟨.privateRow 8 5, 51087746973900⟩, ⟨.privateRow 9 4, 163480790316480⟩, ⟨.privateRow 9 5, 269743304022192⟩, ⟨.hall 9 4, 489095001798480⟩, ⟨.hall 10 4, 348968610098640⟩, ⟨.hall 11 5, 374643477808600⟩, ⟨.hall 7 6, 328561581499725⟩, ⟨.hall 8 6, 249892065198048⟩, ⟨.hall 6 9, 172383994314000⟩, ⟨.hall 4 13, 221157297581220⟩, ⟨.hall 3 16, 6053565866968620⟩]
  caps := #[0, 0, 26992588135550400, 2522171037672000, 0, 0, 4797847892602050, 0, 6012063003792300, 0, 7399747205650800, 18248947151727600, 0, 168629714946000000] }

theorem case_36_23_14_checked :
    (Witness.linear .negative case_36_23_14).check 36 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_24_1_checked :
    (Witness.rising).check 36 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_24_2_checked :
    (Witness.rising).check 36 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_24_3_checked :
    (Witness.rising).check 36 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_24_4_checked :
    (Witness.rising).check 36 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_24_5_checked :
    (Witness.rising).check 36 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_24_6_checked :
    (Witness.rising).check 36 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_24_7_checked :
    (Witness.rising).check 36 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_36_24_8_checked :
    (Witness.linear .positive case_36_24_8).check 36 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_36_24_9_checked :
    (Witness.linear .positive case_36_24_9).check 36 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_36_24_10_checked :
    (Witness.linear .positive case_36_24_10).check 36 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_36_24_11_checked :
    (Witness.linear .positive case_36_24_11).check 36 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_24_12 : Certificate := {
  objectiveScale := 4403931840000
  eta := 909257038677187200
  rows := #[⟨.count 2, 128150320887388800⟩, ⟨.count 3, 17974330721867520⟩, ⟨.count 4, 2440958493093120⟩, ⟨.count 5, 288939215565000⟩, ⟨.count 6, 39625949563200⟩, ⟨.count 7, 11557568622600⟩, ⟨.path 5, 195203545336800⟩, ⟨.privateRow 2 22, 9014903525628000⟩, ⟨.privateRow 3 18, 1300226470042500⟩, ⟨.privateRow 3 19, 2778439496873040⟩, ⟨.privateRow 3 20, 3189888939837600⟩, ⟨.privateRow 4 15, 374465223372240⟩, ⟨.privateRow 4 16, 968986553318784⟩, ⟨.privateRow 4 17, 1271332548486000⟩, ⟨.privateRow 4 18, 1377662179813920⟩, ⟨.privateRow 4 19, 1167314430882600⟩, ⟨.privateRow 5 12, 66167080364385⟩, ⟨.privateRow 5 13, 285967269347760⟩, ⟨.privateRow 5 14, 479253845550480⟩, ⟨.privateRow 5 15, 596370540926160⟩, ⟨.privateRow 5 16, 611395380135540⟩, ⟨.privateRow 6 9, 3632378709960⟩, ⟨.privateRow 6 10, 64208714570000⟩, ⟨.privateRow 6 11, 175427380878750⟩, ⟨.privateRow 6 12, 261106703371800⟩, ⟨.privateRow 6 13, 260045294008500⟩, ⟨.privateRow 7 7, 3001965876000⟩, ⟨.privateRow 7 8, 53164815663960⟩, ⟨.privateRow 7 9, 119061302159800⟩, ⟨.privateRow 7 10, 95556326290425⟩, ⟨.privateRow 8 5, 2118887580810⟩, ⟨.privateRow 8 6, 47491100158320⟩, ⟨.privateRow 8 7, 40220338806648⟩, ⟨.privateRow 9 3, 1422469984320⟩, ⟨.privateRow 9 4, 25811903257140⟩, ⟨.privateRow 10 1, 990648739080⟩, ⟨.privateRow 10 2, 6401114929440⟩, ⟨.hall 2 21, 1708418780031600⟩, ⟨.assumptionRow 12, 4415969253696⟩]
  caps := #[0, 170189767491744, 105580365194304, 24509106854232, 3622647980952, 0, 6776895330634, 1751103984714, 4415969253696, 16999910891040, 0, 233263938555648, 44027280986304] }

theorem case_36_24_12_checked :
    (Witness.linear .conditional case_36_24_12).check 36 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_24_13 : Certificate := {
  objectiveScale := 3440571750000
  eta := 977908996295431200
  rows := #[⟨.count 2, 119690180655645600⟩, ⟨.count 3, 13522355288442000⟩, ⟨.count 4, 1285201630833120⟩, ⟨.count 5, 86681764669500⟩, ⟨.count 6, 19812974781600⟩, ⟨.count 7, 5778784311300⟩, ⟨.path 4, 661274220406800⟩, ⟨.path 5, 47648563162200⟩, ⟨.privateRow 2 22, 9118921643231400⟩, ⟨.privateRow 3 18, 1159802011277910⟩, ⟨.privateRow 3 19, 2549599638145560⟩, ⟨.privateRow 3 20, 3200290751597940⟩, ⟨.privateRow 4 15, 276611142367560⟩, ⟨.privateRow 4 16, 798859143194112⟩, ⟨.privateRow 4 17, 1160379889709040⟩, ⟨.privateRow 4 18, 1419269426855280⟩, ⟨.privateRow 4 19, 1642330501271460⟩, ⟨.privateRow 5 12, 33805888221105⟩, ⟨.privateRow 5 13, 196643774707380⟩, ⟨.privateRow 5 14, 384289156701450⟩, ⟨.privateRow 5 15, 542743422517296⟩, ⟨.privateRow 5 16, 667738527170715⟩, ⟨.privateRow 5 17, 485032629861780⟩, ⟨.privateRow 6 10, 29077375026700⟩, ⟨.privateRow 6 11, 115782071379975⟩, ⟨.privateRow 6 12, 202729188390300⟩, ⟨.privateRow 6 13, 292103787925950⟩, ⟨.privateRow 6 14, 277216538819220⟩, ⟨.privateRow 7 8, 20968731643860⟩, ⟨.privateRow 7 9, 73840021755500⟩, ⟨.privateRow 7 10, 130229032158225⟩, ⟨.privateRow 7 11, 127840861090800⟩, ⟨.privateRow 8 6, 16390733682960⟩, ⟨.privateRow 8 7, 56747661936966⟩, ⟨.privateRow 8 8, 57274173396440⟩, ⟨.privateRow 9 4, 15602717640510⟩, ⟨.privateRow 9 5, 29629403196120⟩, ⟨.privateRow 10 2, 14402508591240⟩, ⟨.privateRow 11 0, 4953243695400⟩, ⟨.hall 3 20, 62410870562040⟩, ⟨.hall 2 21, 1922759143578000⟩, ⟨.assumptionRow 13, 2113446890016⟩]
  caps := #[0, 0, 12075899059224, 0, 3813871777716, 1693468877100, 0, 4657828434402, 2113446890016, 17570236745880, 10660487706792, 0, 162542958709824] }

theorem case_36_24_13_checked :
    (Witness.linear .conditional case_36_24_13).check 36 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_24_14 : Certificate := {
  objectiveScale := 60836779495800000
  eta := 19053605581803699706800
  rows := #[⟨.count 2, 2729947868505942084000⟩, ⟨.count 3, 378020292184818443160⟩, ⟨.count 4, 47048883206856410880⟩, ⟨.count 5, 4371095568204565200⟩, ⟨.count 6, 85151212367621400⟩, ⟨.path 5, 3863364831412386300⟩, ⟨.path 6, 60806019604730400⟩, ⟨.privateRow 2 22, 243787921008500068200⟩, ⟨.privateRow 3 18, 16600228851067791930⟩, ⟨.privateRow 3 19, 64731951641865788280⟩, ⟨.privateRow 3 20, 87918626769569095500⟩, ⟨.privateRow 4 15, 3920740267238034240⟩, ⟨.privateRow 4 17, 63231871117322857950⟩, ⟨.privateRow 4 18, 22146884212236463680⟩, ⟨.privateRow 4 19, 52234592040044554140⟩, ⟨.privateRow 5 12, 596058486573349800⟩, ⟨.privateRow 5 13, 3556482303220987140⟩, ⟨.privateRow 5 14, 4341292643875897710⟩, ⟨.privateRow 5 15, 15509441820638561796⟩, ⟨.privateRow 5 16, 26673617274157403550⟩, ⟨.privateRow 5 17, 19173214651442751900⟩, ⟨.privateRow 6 10, 696978441972012200⟩, ⟨.privateRow 6 13, 18747458589604644900⟩, ⟨.privateRow 6 15, 13429055783810291625⟩, ⟨.privateRow 7 7, 10321359074863200⟩, ⟨.privateRow 7 8, 22706989964699040⟩, ⟨.privateRow 7 11, 7979885044737091200⟩, ⟨.privateRow 7 14, 9895280470554003525⟩, ⟨.privateRow 8 5, 9934308109555830⟩, ⟨.privateRow 8 6, 32512281085819080⟩, ⟨.privateRow 8 7, 69540156766890810⟩, ⟨.privateRow 8 8, 169987049874621980⟩, ⟨.privateRow 8 10, 5713646349867395940⟩, ⟨.privateRow 11 8, 99343081095558300⟩, ⟨.hall 8 4, 12488844480584472⟩, ⟨.hall 9 5, 3493383071492160⟩, ⟨.hall 10 6, 1389413721616200⟩, ⟨.hall 3 20, 8702453903970907080⟩, ⟨.hall 2 21, 58847228765332534800⟩]
  caps := #[0, 520002820006431300, 1192098756367827000, 0, 85781131721034750, 0, 0, 0, 98706029202882920, 0, 497022969196353600, 0, 9368864042353200000] }

theorem case_36_24_14_checked :
    (Witness.linear .negative case_36_24_14).check 36 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_24_15 : Certificate := {
  objectiveScale := 382
  eta := 62492
  rows := #[⟨.assumptionRow 15, 159⟩]
  caps := #[0, 0, 32260, 13993, 8242, 3858, 2127, 1237, 572, 227942, 223223, 150293, 80564] }

theorem case_36_24_15_checked :
    (Witness.linear .conditional case_36_24_15).check 36 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_25_1_checked :
    (Witness.rising).check 36 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_25_2_checked :
    (Witness.rising).check 36 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_25_3_checked :
    (Witness.rising).check 36 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_25_4_checked :
    (Witness.rising).check 36 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_25_5_checked :
    (Witness.rising).check 36 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_25_6_checked :
    (Witness.rising).check 36 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_25_7_checked :
    (Witness.rising).check 36 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_36_25_8_checked :
    (Witness.linear .positive case_36_25_8).check 36 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_36_25_9_checked :
    (Witness.linear .positive case_36_25_9).check 36 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_36_25_10_checked :
    (Witness.linear .positive case_36_25_10).check 36 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_36_25_11_checked :
    (Witness.linear .positive case_36_25_11).check 36 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_25_12 : Certificate := {
  objectiveScale := 3
  eta := 43758
  rows := #[⟨.assumptionRow 12, 7⟩]
  caps := #[0, 0, 13104, 4004, 1287, 429, 150, 56, 23, 700, 420, 140] }

theorem case_36_25_12_checked :
    (Witness.linear .conditional case_36_25_12).check 36 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_25_13 : Certificate := {
  objectiveScale := 52051157096400000
  eta := 16853815300447888963200
  rows := #[⟨.count 2, 1984637727645334201440⟩, ⟨.count 3, 208071793832689987200⟩, ⟨.count 4, 16829336265879337200⟩, ⟨.count 5, 655688425943350800⟩, ⟨.path 4, 14530259624251250880⟩, ⟨.path 5, 6811382269692000⟩, ⟨.privateRow 2 22, 189559523940222716280⟩, ⟨.privateRow 2 23, 220311311116965868800⟩, ⟨.privateRow 3 18, 19624026045788996832⟩, ⟨.privateRow 3 19, 46714157634986281440⟩, ⟨.privateRow 3 20, 89280478856967958560⟩, ⟨.privateRow 3 21, 73131115773548392560⟩, ⟨.privateRow 4 15, 6961225455431907660⟩, ⟨.privateRow 4 16, 11755036391773294620⟩, ⟨.privateRow 4 17, 27676608459068837268⟩, ⟨.privateRow 4 18, 33926411972352209310⟩, ⟨.privateRow 4 19, 35392604147031090960⟩, ⟨.privateRow 4 20, 8452916624453030730⟩, ⟨.privateRow 5 12, 1447371488378655840⟩, ⟨.privateRow 5 13, 3491540868148343010⟩, ⟨.privateRow 5 14, 8230450908507965280⟩, ⟨.privateRow 5 15, 13390614743154208560⟩, ⟨.privateRow 5 16, 16444665722659238064⟩, ⟨.privateRow 5 17, 6917512893702350940⟩, ⟨.privateRow 6 9, 175512558459583800⟩, ⟨.privateRow 6 10, 877893948068597460⟩, ⟨.privateRow 6 11, 2845363971840590200⟩, ⟨.privateRow 6 12, 5259167583087292875⟩, ⟨.privateRow 6 13, 7805814594563700000⟩, ⟨.privateRow 6 14, 2094560249541259500⟩, ⟨.privateRow 7 6, 6725009496854880⟩, ⟨.privateRow 7 7, 123852258233744040⟩, ⟨.privateRow 7 8, 917963796320691120⟩, ⟨.privateRow 7 9, 2461017225374043336⟩, ⟨.privateRow 7 10, 3463006279241549040⟩, ⟨.privateRow 8 5, 170647115982692580⟩, ⟨.privateRow 8 6, 1153829493986424255⟩, ⟨.privateRow 8 7, 1147454745400863900⟩, ⟨.privateRow 9 3, 335129639926601520⟩, ⟨.privateRow 9 4, 486442353605836320⟩, ⟨.privateRow 10 0, 57372737270043195⟩, ⟨.privateRow 10 1, 183592759264138224⟩, ⟨.hall 2 22, 25383694541737371840⟩, ⟨.assumptionRow 13, 37443260113080822⟩]
  caps := #[0, 7919233565069368080, 1492444152031328496, 1094980283530705572, 63678283859843730, 92952882884366076, 37443260113080822, 356997719053655064, 367892676873395289, 224036855335755000, 0, 11326834858609976706] }

theorem case_36_25_13_checked :
    (Witness.linear .conditional case_36_25_13).check 36 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_25_14 : Certificate := {
  objectiveScale := 29420219228400000
  eta := 12058984404332812346400
  rows := #[⟨.count 2, 1437531305038202293920⟩, ⟨.count 3, 151362030415545069120⟩, ⟨.count 4, 12239517284275881600⟩, ⟨.count 5, 291417078197044800⟩, ⟨.path 4, 9439191928962956160⟩, ⟨.path 5, 260648894853547200⟩, ⟨.privateRow 2 22, 147639177241577821800⟩, ⟨.privateRow 2 23, 179308928214641665440⟩, ⟨.privateRow 3 18, 12552304948207376352⟩, ⟨.privateRow 3 19, 34389643702902928440⟩, ⟨.privateRow 3 20, 69719916974875207040⟩, ⟨.privateRow 3 21, 61197586421379408000⟩, ⟨.privateRow 4 15, 4509679285099268280⟩, ⟨.privateRow 4 16, 7887688916533345920⟩, ⟨.privateRow 4 17, 20174804323581411504⟩, ⟨.privateRow 4 18, 26563577356029999285⟩, ⟨.privateRow 4 19, 29995317011256657060⟩, ⟨.privateRow 4 20, 15477889565740541940⟩, ⟨.privateRow 5 11, 58283415639408960⟩, ⟨.privateRow 5 12, 973009244424577360⟩, ⟨.privateRow 5 13, 2205663010603882830⟩, ⟨.privateRow 5 14, 5439091609491986160⟩, ⟨.privateRow 5 15, 9626477483109046560⟩, ⟨.privateRow 5 16, 12688299584699330592⟩, ⟨.privateRow 5 17, 12130235879951989800⟩, ⟨.privateRow 6 8, 18213567387315300⟩, ⟨.privateRow 6 9, 197589609838147800⟩, ⟨.privateRow 6 10, 574334491613342460⟩, ⟨.privateRow 6 11, 1752549928601672200⟩, ⟨.privateRow 6 12, 3404419304145684825⟩, ⟨.privateRow 6 13, 5446723961540004000⟩, ⟨.privateRow 6 14, 5800009348005072200⟩, ⟨.privateRow 7 6, 63887590220121360⟩, ⟨.privateRow 7 7, 150565490401806480⟩, ⟨.privateRow 7 8, 593431141055800320⟩, ⟨.privateRow 7 9, 1489141269586898928⟩, ⟨.privateRow 7 10, 2627610655076687280⟩, ⟨.privateRow 7 11, 1701147193975249020⟩, ⟨.privateRow 8 3, 15299396605344852⟩, ⟨.privateRow 8 4, 80139696504187320⟩, ⟨.privateRow 8 5, 225568026873674100⟩, ⟨.privateRow 8 6, 743720668315374750⟩, ⟨.privateRow 8 7, 1374627604086287460⟩, ⟨.privateRow 9 0, 3999842249763360⟩, ⟨.privateRow 9 1, 29748826732614990⟩, ⟨.privateRow 9 3, 820824770255009520⟩, ⟨.privateRow 10 0, 286863686350215975⟩, ⟨.privateRow 11 0, 203991954737931360⟩, ⟨.hall 2 22, 23654197534176649440⟩, ⟨.assumptionRow 14, 5647550544959400⟩]
  caps := #[0, 277263820689332400, 1130096864102005800, 72270773321226480, 108649012803698367, 1524458965404700, 920096211300, 87534175776625368, 0, 396136714083910800, 2794510782392504175, 0] }

theorem case_36_25_14_checked :
    (Witness.linear .conditional case_36_25_14).check 36 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_25_15 : Certificate := {
  objectiveScale := 587
  eta := 86972
  rows := #[⟨.assumptionRow 15, 239⟩]
  caps := #[0, 0, 42860, 20048, 11557, 5108, 3082, 1768, 1163786, 1144624, 783692, 435344] }

theorem case_36_25_15_checked :
    (Witness.linear .conditional case_36_25_15).check 36 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1430, 1430, 1001] }

theorem case_36_25_16_checked :
    (Witness.linear .negative case_36_25_16).check 36 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_26_1_checked :
    (Witness.rising).check 36 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_26_2_checked :
    (Witness.rising).check 36 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_26_3_checked :
    (Witness.rising).check 36 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_26_4_checked :
    (Witness.rising).check 36 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_26_5_checked :
    (Witness.rising).check 36 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_26_6_checked :
    (Witness.rising).check 36 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_26_7_checked :
    (Witness.rising).check 36 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_36_26_8_checked :
    (Witness.linear .positive case_36_26_8).check 36 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_36_26_9_checked :
    (Witness.linear .positive case_36_26_9).check 36 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_36_26_10_checked :
    (Witness.linear .positive case_36_26_10).check 36 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_36_26_11_checked :
    (Witness.linear .positive case_36_26_11).check 36 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_36_26_12_checked :
    (Witness.linear .positive case_36_26_12).check 36 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_26_13 : Certificate := {
  objectiveScale := 353
  eta := 5118258
  rows := #[⟨.assumptionRow 13, 529⟩]
  caps := #[0, 0, 1632306, 530608, 176176, 60038, 21135, 7752, 614856, 444924, 212020] }

theorem case_36_26_13_checked :
    (Witness.linear .conditional case_36_26_13).check 36 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_26_14 : Certificate := {
  objectiveScale := 620
  eta := 8478750
  rows := #[⟨.assumptionRow 14, 671⟩]
  caps := #[0, 0, 2699940, 908752, 327782, 117832, 42515, 15504, 1513884, 1281392, 734300] }

theorem case_36_26_14_checked :
    (Witness.linear .conditional case_36_26_14).check 36 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_26_15 : Certificate := {
  objectiveScale := 560
  eta := 1441872
  rows := #[⟨.assumptionRow 15, 373⟩]
  caps := #[0, 0, 644028, 244804, 101374, 43537, 16390, 8398, 1737060, 1652196, 1087996] }

theorem case_36_26_15_checked :
    (Witness.linear .conditional case_36_26_15).check 36 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_26_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 4862, 4862, 3432] }

theorem case_36_26_16_checked :
    (Witness.linear .negative case_36_26_16).check 36 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_27_1_checked :
    (Witness.rising).check 36 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_27_2_checked :
    (Witness.rising).check 36 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_27_3_checked :
    (Witness.rising).check 36 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_27_4_checked :
    (Witness.rising).check 36 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_27_5_checked :
    (Witness.rising).check 36 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_27_6_checked :
    (Witness.rising).check 36 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_27_7_checked :
    (Witness.rising).check 36 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_36_27_8_checked :
    (Witness.linear .positive case_36_27_8).check 36 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_36_27_9_checked :
    (Witness.linear .positive case_36_27_9).check 36 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_36_27_10_checked :
    (Witness.linear .positive case_36_27_10).check 36 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_36_27_11_checked :
    (Witness.linear .positive case_36_27_11).check 36 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_36_27_12_checked :
    (Witness.linear .positive case_36_27_12).check 36 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_27_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_36_27_13_checked :
    (Witness.linear .positive case_36_27_13).check 36 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_27_14 : Certificate := {
  objectiveScale := 853
  eta := 9767520
  rows := #[⟨.assumptionRow 14, 884⟩]
  caps := #[0, 0, 3195252, 1044316, 372554, 139711, 52030, 7064010, 6131832, 3657516] }

theorem case_36_27_14_checked :
    (Witness.linear .conditional case_36_27_14).check 36 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_27_15 : Certificate := {
  objectiveScale := 825
  eta := 1914744
  rows := #[⟨.assumptionRow 15, 536⟩]
  caps := #[0, 0, 813756, 326228, 127218, 58344, 22660, 8672550, 8319834, 5581644] }

theorem case_36_27_15_checked :
    (Witness.linear .conditional case_36_27_15).check 36 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_27_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934] }

theorem case_36_27_16_checked :
    (Witness.linear .negative case_36_27_16).check 36 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 4862] }

theorem case_36_27_17_checked :
    (Witness.linear .negative case_36_27_17).check 36 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_28_1_checked :
    (Witness.rising).check 36 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_28_2_checked :
    (Witness.rising).check 36 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_28_3_checked :
    (Witness.rising).check 36 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_28_4_checked :
    (Witness.rising).check 36 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_28_5_checked :
    (Witness.rising).check 36 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_28_6_checked :
    (Witness.rising).check 36 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_28_7_checked :
    (Witness.rising).check 36 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_28_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_36_28_8_checked :
    (Witness.linear .positive case_36_28_8).check 36 28 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_36_28_9_checked :
    (Witness.linear .positive case_36_28_9).check 36 28 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_36_28_10_checked :
    (Witness.linear .positive case_36_28_10).check 36 28 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_36_28_11_checked :
    (Witness.linear .positive case_36_28_11).check 36 28 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_36_28_12_checked :
    (Witness.linear .positive case_36_28_12).check 36 28 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_36_28_13_checked :
    (Witness.linear .positive case_36_28_13).check 36 28 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_28_14 : Certificate := {
  objectiveScale := 2
  eta := 96900
  rows := #[⟨.assumptionRow 14, 3⟩]
  caps := #[0, 0, 29070, 9282, 3016, 1001, 341, 120, 7752] }

theorem case_36_28_14_checked :
    (Witness.linear .conditional case_36_28_14).check 36 28 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_28_15 : Certificate := {
  objectiveScale := 829
  eta := 9286896
  rows := #[⟨.assumptionRow 15, 696⟩]
  caps := #[0, 0, 3333360, 1150016, 421148, 168623, 63954, 14276600, 13188090] }

theorem case_36_28_15_checked :
    (Witness.linear .conditional case_36_28_15).check 36 28 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_28_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 58786, 58786, 41990] }

theorem case_36_28_16_checked :
    (Witness.linear .negative case_36_28_16).check 36 28 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_28_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 16796] }

theorem case_36_28_17_checked :
    (Witness.linear .negative case_36_28_17).check 36 28 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_36_28_18_checked :
    (Witness.linear .negative case_36_28_18).check 36 28 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_29_1_checked :
    (Witness.rising).check 36 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_29_2_checked :
    (Witness.rising).check 36 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_29_3_checked :
    (Witness.rising).check 36 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_29_4_checked :
    (Witness.rising).check 36 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_29_5_checked :
    (Witness.rising).check 36 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_29_6_checked :
    (Witness.rising).check 36 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_29_7_checked :
    (Witness.rising).check 36 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_29_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_36_29_8_checked :
    (Witness.linear .positive case_36_29_8).check 36 29 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_36_29_9_checked :
    (Witness.linear .positive case_36_29_9).check 36 29 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_36_29_10_checked :
    (Witness.linear .positive case_36_29_10).check 36 29 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_36_29_11_checked :
    (Witness.linear .positive case_36_29_11).check 36 29 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_36_29_12_checked :
    (Witness.linear .positive case_36_29_12).check 36 29 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_36_29_13_checked :
    (Witness.linear .positive case_36_29_13).check 36 29 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_29_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_36_29_14_checked :
    (Witness.linear .positive case_36_29_14).check 36 29 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_29_15 : Certificate := {
  objectiveScale := 28
  eta := 618222
  rows := #[⟨.assumptionRow 15, 27⟩]
  caps := #[0, 0, 222870, 78132, 26936, 9191, 326876, 945098] }

theorem case_36_29_15_checked :
    (Witness.linear .conditional case_36_29_15).check 36 29 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_29_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 208012, 208012, 149226] }

theorem case_36_29_16_checked :
    (Witness.linear .negative case_36_29_16).check 36 29 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_29_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 58786] }

theorem case_36_29_17_checked :
    (Witness.linear .negative case_36_29_17).check 36 29 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_36_29_18_checked :
    (Witness.linear .negative case_36_29_18).check 36 29 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_30_1_checked :
    (Witness.rising).check 36 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_30_2_checked :
    (Witness.rising).check 36 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_30_3_checked :
    (Witness.rising).check 36 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_30_4_checked :
    (Witness.rising).check 36 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_30_5_checked :
    (Witness.rising).check 36 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_30_6_checked :
    (Witness.rising).check 36 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_30_7_checked :
    (Witness.rising).check 36 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_36_30_8_checked :
    (Witness.linear .positive case_36_30_8).check 36 30 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_36_30_9_checked :
    (Witness.linear .positive case_36_30_9).check 36 30 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_36_30_10_checked :
    (Witness.linear .positive case_36_30_10).check 36 30 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_36_30_11_checked :
    (Witness.linear .positive case_36_30_11).check 36 30 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_36_30_12_checked :
    (Witness.linear .positive case_36_30_12).check 36 30 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_36_30_13_checked :
    (Witness.linear .positive case_36_30_13).check 36 30 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_36_30_14_checked :
    (Witness.linear .positive case_36_30_14).check 36 30 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_36_30_15_checked :
    (Witness.linear .positive case_36_30_15).check 36 30 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 742900, 742900, 534888] }

theorem case_36_30_16_checked :
    (Witness.linear .negative case_36_30_16).check 36 30 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 208012] }

theorem case_36_30_17_checked :
    (Witness.linear .negative case_36_30_17).check 36 30 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_36_30_18_checked :
    (Witness.linear .negative case_36_30_18).check 36 30 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_36_30_19_checked :
    (Witness.linear .negative case_36_30_19).check 36 30 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_31_1_checked :
    (Witness.rising).check 36 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_31_2_checked :
    (Witness.rising).check 36 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_31_3_checked :
    (Witness.rising).check 36 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_31_4_checked :
    (Witness.rising).check 36 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_31_5_checked :
    (Witness.rising).check 36 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_31_6_checked :
    (Witness.rising).check 36 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_31_7_checked :
    (Witness.rising).check 36 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_36_31_8_checked :
    (Witness.linear .positive case_36_31_8).check 36 31 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_36_31_9_checked :
    (Witness.linear .positive case_36_31_9).check 36 31 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_36_31_10_checked :
    (Witness.linear .positive case_36_31_10).check 36 31 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_36_31_11_checked :
    (Witness.linear .positive case_36_31_11).check 36 31 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_36_31_12_checked :
    (Witness.linear .positive case_36_31_12).check 36 31 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_36_31_13_checked :
    (Witness.linear .positive case_36_31_13).check 36 31 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_36_31_14_checked :
    (Witness.linear .positive case_36_31_14).check 36 31 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_36_31_15_checked :
    (Witness.linear .positive case_36_31_15).check 36 31 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_16 : Certificate := {
  objectiveScale := 999
  eta := 23396505
  rows := #[⟨.assumptionRow 16, 799⟩]
  caps := #[0, 0, 7736496, 3093048, 1140020, 482885] }

theorem case_36_31_16_checked :
    (Witness.linear .conditional case_36_31_16).check 36 31 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 742900] }

theorem case_36_31_17_checked :
    (Witness.linear .negative case_36_31_17).check 36 31 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_36_31_18_checked :
    (Witness.linear .negative case_36_31_18).check 36 31 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_36_31_19_checked :
    (Witness.linear .negative case_36_31_19).check 36 31 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_36_31_20_checked :
    (Witness.linear .negative case_36_31_20).check 36 31 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_32_1_checked :
    (Witness.rising).check 36 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_32_2_checked :
    (Witness.rising).check 36 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_32_3_checked :
    (Witness.rising).check 36 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_32_4_checked :
    (Witness.rising).check 36 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_32_5_checked :
    (Witness.rising).check 36 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_32_6_checked :
    (Witness.rising).check 36 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_32_7_checked :
    (Witness.rising).check 36 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_36_32_8_checked :
    (Witness.linear .positive case_36_32_8).check 36 32 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_36_32_9_checked :
    (Witness.linear .positive case_36_32_9).check 36 32 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_36_32_10_checked :
    (Witness.linear .positive case_36_32_10).check 36 32 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_36_32_11_checked :
    (Witness.linear .positive case_36_32_11).check 36 32 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_36_32_12_checked :
    (Witness.linear .positive case_36_32_12).check 36 32 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_36_32_13_checked :
    (Witness.linear .positive case_36_32_13).check 36 32 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_36_32_14_checked :
    (Witness.linear .positive case_36_32_14).check 36 32 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_36_32_15_checked :
    (Witness.linear .positive case_36_32_15).check 36 32 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_36_32_16_checked :
    (Witness.linear .positive case_36_32_16).check 36 32 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 2674440] }

theorem case_36_32_17_checked :
    (Witness.linear .negative case_36_32_17).check 36 32 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_36_32_18_checked :
    (Witness.linear .negative case_36_32_18).check 36 32 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_36_32_19_checked :
    (Witness.linear .negative case_36_32_19).check 36 32 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_36_32_20_checked :
    (Witness.linear .negative case_36_32_20).check 36 32 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_33_1_checked :
    (Witness.rising).check 36 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_33_2_checked :
    (Witness.rising).check 36 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_33_3_checked :
    (Witness.rising).check 36 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_33_4_checked :
    (Witness.rising).check 36 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_33_5_checked :
    (Witness.rising).check 36 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_33_6_checked :
    (Witness.rising).check 36 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_33_7_checked :
    (Witness.rising).check 36 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_36_33_8_checked :
    (Witness.linear .positive case_36_33_8).check 36 33 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_36_33_9_checked :
    (Witness.linear .positive case_36_33_9).check 36 33 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_36_33_10_checked :
    (Witness.linear .positive case_36_33_10).check 36 33 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_36_33_11_checked :
    (Witness.linear .positive case_36_33_11).check 36 33 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_36_33_12_checked :
    (Witness.linear .positive case_36_33_12).check 36 33 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_36_33_13_checked :
    (Witness.linear .positive case_36_33_13).check 36 33 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_36_33_14_checked :
    (Witness.linear .positive case_36_33_14).check 36 33 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_36_33_15_checked :
    (Witness.linear .positive case_36_33_15).check 36 33 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_36_33_16_checked :
    (Witness.linear .positive case_36_33_16).check 36 33 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 9694845] }

theorem case_36_33_17_checked :
    (Witness.linear .negative case_36_33_17).check 36 33 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_36_33_18_checked :
    (Witness.linear .negative case_36_33_18).check 36 33 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_36_33_19_checked :
    (Witness.linear .negative case_36_33_19).check 36 33 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_36_33_20_checked :
    (Witness.linear .negative case_36_33_20).check 36 33 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_36_33_21_checked :
    (Witness.linear .negative case_36_33_21).check 36 33 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_34_1_checked :
    (Witness.rising).check 36 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_34_2_checked :
    (Witness.rising).check 36 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_34_3_checked :
    (Witness.rising).check 36 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_34_4_checked :
    (Witness.rising).check 36 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_34_5_checked :
    (Witness.rising).check 36 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_34_6_checked :
    (Witness.rising).check 36 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_34_7_checked :
    (Witness.rising).check 36 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_36_34_8_checked :
    (Witness.linear .positive case_36_34_8).check 36 34 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_36_34_9_checked :
    (Witness.linear .positive case_36_34_9).check 36 34 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_36_34_10_checked :
    (Witness.linear .positive case_36_34_10).check 36 34 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_36_34_11_checked :
    (Witness.linear .positive case_36_34_11).check 36 34 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_36_34_12_checked :
    (Witness.linear .positive case_36_34_12).check 36 34 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_36_34_13_checked :
    (Witness.linear .positive case_36_34_13).check 36 34 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_36_34_14_checked :
    (Witness.linear .positive case_36_34_14).check 36 34 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_36_34_15_checked :
    (Witness.linear .positive case_36_34_15).check 36 34 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_36_34_16_checked :
    (Witness.linear .positive case_36_34_16).check 36 34 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_36_34_17_checked :
    (Witness.linear .positive case_36_34_17).check 36 34 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_36_34_18_checked :
    (Witness.linear .negative case_36_34_18).check 36 34 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_36_34_19_checked :
    (Witness.linear .negative case_36_34_19).check 36 34 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_36_34_20_checked :
    (Witness.linear .negative case_36_34_20).check 36 34 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_36_34_21_checked :
    (Witness.linear .negative case_36_34_21).check 36 34 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_36_34_22_checked :
    (Witness.linear .negative case_36_34_22).check 36 34 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_35_1_checked :
    (Witness.rising).check 36 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_35_2_checked :
    (Witness.rising).check 36 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_35_3_checked :
    (Witness.rising).check 36 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_35_4_checked :
    (Witness.rising).check 36 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_35_5_checked :
    (Witness.rising).check 36 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_35_6_checked :
    (Witness.rising).check 36 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_36_35_7_checked :
    (Witness.rising).check 36 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_8_checked :
    (Witness.linear .positive case_36_35_8).check 36 35 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_9_checked :
    (Witness.linear .positive case_36_35_9).check 36 35 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_10_checked :
    (Witness.linear .positive case_36_35_10).check 36 35 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_11_checked :
    (Witness.linear .positive case_36_35_11).check 36 35 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_12_checked :
    (Witness.linear .positive case_36_35_12).check 36 35 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_13_checked :
    (Witness.linear .positive case_36_35_13).check 36 35 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_14_checked :
    (Witness.linear .positive case_36_35_14).check 36 35 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_15_checked :
    (Witness.linear .positive case_36_35_15).check 36 35 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_16_checked :
    (Witness.linear .positive case_36_35_16).check 36 35 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_17_checked :
    (Witness.linear .positive case_36_35_17).check 36 35 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_18_checked :
    (Witness.linear .negative case_36_35_18).check 36 35 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_19_checked :
    (Witness.linear .negative case_36_35_19).check 36 35 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_20_checked :
    (Witness.linear .negative case_36_35_20).check 36 35 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_21_checked :
    (Witness.linear .negative case_36_35_21).check 36 35 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_36_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_36_35_22_checked :
    (Witness.linear .negative case_36_35_22).check 36 35 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_36 (a k : ℕ) (h : Domain 36 a k) :
    ∃ w : Witness, w.check 36 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 18 ≤ a := by omega
  have haHi : a ≤ 35 := by omega
  interval_cases a

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_18_1_checked⟩

    · exact ⟨Witness.rising, case_36_18_2_checked⟩

    · exact ⟨Witness.rising, case_36_18_3_checked⟩

    · exact ⟨Witness.rising, case_36_18_4_checked⟩

    · exact ⟨Witness.rising, case_36_18_5_checked⟩

    · exact ⟨Witness.rising, case_36_18_6_checked⟩

    · exact ⟨Witness.rising, case_36_18_7_checked⟩

    · exact ⟨Witness.rising, case_36_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_18_9, case_36_18_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_18_10, case_36_18_10_checked⟩

    · exact ⟨Witness.linear .conditional case_36_18_11, case_36_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_19_1_checked⟩

    · exact ⟨Witness.rising, case_36_19_2_checked⟩

    · exact ⟨Witness.rising, case_36_19_3_checked⟩

    · exact ⟨Witness.rising, case_36_19_4_checked⟩

    · exact ⟨Witness.rising, case_36_19_5_checked⟩

    · exact ⟨Witness.rising, case_36_19_6_checked⟩

    · exact ⟨Witness.rising, case_36_19_7_checked⟩

    · exact ⟨Witness.rising, case_36_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_19_9, case_36_19_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_19_10, case_36_19_10_checked⟩

    · exact ⟨Witness.linear .conditional case_36_19_11, case_36_19_11_checked⟩

    · exact ⟨Witness.linear .conditional case_36_19_12, case_36_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_20_1_checked⟩

    · exact ⟨Witness.rising, case_36_20_2_checked⟩

    · exact ⟨Witness.rising, case_36_20_3_checked⟩

    · exact ⟨Witness.rising, case_36_20_4_checked⟩

    · exact ⟨Witness.rising, case_36_20_5_checked⟩

    · exact ⟨Witness.rising, case_36_20_6_checked⟩

    · exact ⟨Witness.rising, case_36_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_20_8, case_36_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_20_9, case_36_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_20_10, case_36_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_36_20_11, case_36_20_11_checked⟩

    · exact ⟨Witness.linear .conditional case_36_20_12, case_36_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_21_1_checked⟩

    · exact ⟨Witness.rising, case_36_21_2_checked⟩

    · exact ⟨Witness.rising, case_36_21_3_checked⟩

    · exact ⟨Witness.rising, case_36_21_4_checked⟩

    · exact ⟨Witness.rising, case_36_21_5_checked⟩

    · exact ⟨Witness.rising, case_36_21_6_checked⟩

    · exact ⟨Witness.rising, case_36_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_21_8, case_36_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_21_9, case_36_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_21_10, case_36_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_36_21_11, case_36_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_36_21_12, case_36_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_36_21_13, case_36_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_22_1_checked⟩

    · exact ⟨Witness.rising, case_36_22_2_checked⟩

    · exact ⟨Witness.rising, case_36_22_3_checked⟩

    · exact ⟨Witness.rising, case_36_22_4_checked⟩

    · exact ⟨Witness.rising, case_36_22_5_checked⟩

    · exact ⟨Witness.rising, case_36_22_6_checked⟩

    · exact ⟨Witness.rising, case_36_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_22_8, case_36_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_22_9, case_36_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_22_10, case_36_22_10_checked⟩

    · exact ⟨Witness.linear .conditional case_36_22_11, case_36_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_36_22_12, case_36_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_36_22_13, case_36_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_36_22_14, case_36_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_23_1_checked⟩

    · exact ⟨Witness.rising, case_36_23_2_checked⟩

    · exact ⟨Witness.rising, case_36_23_3_checked⟩

    · exact ⟨Witness.rising, case_36_23_4_checked⟩

    · exact ⟨Witness.rising, case_36_23_5_checked⟩

    · exact ⟨Witness.rising, case_36_23_6_checked⟩

    · exact ⟨Witness.rising, case_36_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_23_8, case_36_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_23_9, case_36_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_23_10, case_36_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_23_11, case_36_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_36_23_12, case_36_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_36_23_13, case_36_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_36_23_14, case_36_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_24_1_checked⟩

    · exact ⟨Witness.rising, case_36_24_2_checked⟩

    · exact ⟨Witness.rising, case_36_24_3_checked⟩

    · exact ⟨Witness.rising, case_36_24_4_checked⟩

    · exact ⟨Witness.rising, case_36_24_5_checked⟩

    · exact ⟨Witness.rising, case_36_24_6_checked⟩

    · exact ⟨Witness.rising, case_36_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_24_8, case_36_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_24_9, case_36_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_24_10, case_36_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_24_11, case_36_24_11_checked⟩

    · exact ⟨Witness.linear .conditional case_36_24_12, case_36_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_36_24_13, case_36_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_36_24_14, case_36_24_14_checked⟩

    · exact ⟨Witness.linear .conditional case_36_24_15, case_36_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_25_1_checked⟩

    · exact ⟨Witness.rising, case_36_25_2_checked⟩

    · exact ⟨Witness.rising, case_36_25_3_checked⟩

    · exact ⟨Witness.rising, case_36_25_4_checked⟩

    · exact ⟨Witness.rising, case_36_25_5_checked⟩

    · exact ⟨Witness.rising, case_36_25_6_checked⟩

    · exact ⟨Witness.rising, case_36_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_25_8, case_36_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_25_9, case_36_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_25_10, case_36_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_25_11, case_36_25_11_checked⟩

    · exact ⟨Witness.linear .conditional case_36_25_12, case_36_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_36_25_13, case_36_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_36_25_14, case_36_25_14_checked⟩

    · exact ⟨Witness.linear .conditional case_36_25_15, case_36_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_36_25_16, case_36_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_26_1_checked⟩

    · exact ⟨Witness.rising, case_36_26_2_checked⟩

    · exact ⟨Witness.rising, case_36_26_3_checked⟩

    · exact ⟨Witness.rising, case_36_26_4_checked⟩

    · exact ⟨Witness.rising, case_36_26_5_checked⟩

    · exact ⟨Witness.rising, case_36_26_6_checked⟩

    · exact ⟨Witness.rising, case_36_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_26_8, case_36_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_26_9, case_36_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_26_10, case_36_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_26_11, case_36_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_36_26_12, case_36_26_12_checked⟩

    · exact ⟨Witness.linear .conditional case_36_26_13, case_36_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_36_26_14, case_36_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_36_26_15, case_36_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_36_26_16, case_36_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_27_1_checked⟩

    · exact ⟨Witness.rising, case_36_27_2_checked⟩

    · exact ⟨Witness.rising, case_36_27_3_checked⟩

    · exact ⟨Witness.rising, case_36_27_4_checked⟩

    · exact ⟨Witness.rising, case_36_27_5_checked⟩

    · exact ⟨Witness.rising, case_36_27_6_checked⟩

    · exact ⟨Witness.rising, case_36_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_27_8, case_36_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_27_9, case_36_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_27_10, case_36_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_27_11, case_36_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_36_27_12, case_36_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_36_27_13, case_36_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_36_27_14, case_36_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_36_27_15, case_36_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_36_27_16, case_36_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_36_27_17, case_36_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_28_1_checked⟩

    · exact ⟨Witness.rising, case_36_28_2_checked⟩

    · exact ⟨Witness.rising, case_36_28_3_checked⟩

    · exact ⟨Witness.rising, case_36_28_4_checked⟩

    · exact ⟨Witness.rising, case_36_28_5_checked⟩

    · exact ⟨Witness.rising, case_36_28_6_checked⟩

    · exact ⟨Witness.rising, case_36_28_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_28_8, case_36_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_28_9, case_36_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_28_10, case_36_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_28_11, case_36_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_36_28_12, case_36_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_36_28_13, case_36_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_36_28_14, case_36_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_36_28_15, case_36_28_15_checked⟩

    · exact ⟨Witness.linear .negative case_36_28_16, case_36_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_36_28_17, case_36_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_36_28_18, case_36_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_29_1_checked⟩

    · exact ⟨Witness.rising, case_36_29_2_checked⟩

    · exact ⟨Witness.rising, case_36_29_3_checked⟩

    · exact ⟨Witness.rising, case_36_29_4_checked⟩

    · exact ⟨Witness.rising, case_36_29_5_checked⟩

    · exact ⟨Witness.rising, case_36_29_6_checked⟩

    · exact ⟨Witness.rising, case_36_29_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_29_8, case_36_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_29_9, case_36_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_29_10, case_36_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_29_11, case_36_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_36_29_12, case_36_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_36_29_13, case_36_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_36_29_14, case_36_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_36_29_15, case_36_29_15_checked⟩

    · exact ⟨Witness.linear .negative case_36_29_16, case_36_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_36_29_17, case_36_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_36_29_18, case_36_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_30_1_checked⟩

    · exact ⟨Witness.rising, case_36_30_2_checked⟩

    · exact ⟨Witness.rising, case_36_30_3_checked⟩

    · exact ⟨Witness.rising, case_36_30_4_checked⟩

    · exact ⟨Witness.rising, case_36_30_5_checked⟩

    · exact ⟨Witness.rising, case_36_30_6_checked⟩

    · exact ⟨Witness.rising, case_36_30_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_30_8, case_36_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_30_9, case_36_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_30_10, case_36_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_30_11, case_36_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_36_30_12, case_36_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_36_30_13, case_36_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_36_30_14, case_36_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_36_30_15, case_36_30_15_checked⟩

    · exact ⟨Witness.linear .negative case_36_30_16, case_36_30_16_checked⟩

    · exact ⟨Witness.linear .negative case_36_30_17, case_36_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_36_30_18, case_36_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_36_30_19, case_36_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_31_1_checked⟩

    · exact ⟨Witness.rising, case_36_31_2_checked⟩

    · exact ⟨Witness.rising, case_36_31_3_checked⟩

    · exact ⟨Witness.rising, case_36_31_4_checked⟩

    · exact ⟨Witness.rising, case_36_31_5_checked⟩

    · exact ⟨Witness.rising, case_36_31_6_checked⟩

    · exact ⟨Witness.rising, case_36_31_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_31_8, case_36_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_31_9, case_36_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_31_10, case_36_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_31_11, case_36_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_36_31_12, case_36_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_36_31_13, case_36_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_36_31_14, case_36_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_36_31_15, case_36_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_36_31_16, case_36_31_16_checked⟩

    · exact ⟨Witness.linear .negative case_36_31_17, case_36_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_36_31_18, case_36_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_36_31_19, case_36_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_36_31_20, case_36_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_32_1_checked⟩

    · exact ⟨Witness.rising, case_36_32_2_checked⟩

    · exact ⟨Witness.rising, case_36_32_3_checked⟩

    · exact ⟨Witness.rising, case_36_32_4_checked⟩

    · exact ⟨Witness.rising, case_36_32_5_checked⟩

    · exact ⟨Witness.rising, case_36_32_6_checked⟩

    · exact ⟨Witness.rising, case_36_32_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_32_8, case_36_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_32_9, case_36_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_32_10, case_36_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_32_11, case_36_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_36_32_12, case_36_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_36_32_13, case_36_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_36_32_14, case_36_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_36_32_15, case_36_32_15_checked⟩

    · exact ⟨Witness.linear .positive case_36_32_16, case_36_32_16_checked⟩

    · exact ⟨Witness.linear .negative case_36_32_17, case_36_32_17_checked⟩

    · exact ⟨Witness.linear .negative case_36_32_18, case_36_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_36_32_19, case_36_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_36_32_20, case_36_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_33_1_checked⟩

    · exact ⟨Witness.rising, case_36_33_2_checked⟩

    · exact ⟨Witness.rising, case_36_33_3_checked⟩

    · exact ⟨Witness.rising, case_36_33_4_checked⟩

    · exact ⟨Witness.rising, case_36_33_5_checked⟩

    · exact ⟨Witness.rising, case_36_33_6_checked⟩

    · exact ⟨Witness.rising, case_36_33_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_33_8, case_36_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_33_9, case_36_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_33_10, case_36_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_33_11, case_36_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_36_33_12, case_36_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_36_33_13, case_36_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_36_33_14, case_36_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_36_33_15, case_36_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_36_33_16, case_36_33_16_checked⟩

    · exact ⟨Witness.linear .negative case_36_33_17, case_36_33_17_checked⟩

    · exact ⟨Witness.linear .negative case_36_33_18, case_36_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_36_33_19, case_36_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_36_33_20, case_36_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_36_33_21, case_36_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_34_1_checked⟩

    · exact ⟨Witness.rising, case_36_34_2_checked⟩

    · exact ⟨Witness.rising, case_36_34_3_checked⟩

    · exact ⟨Witness.rising, case_36_34_4_checked⟩

    · exact ⟨Witness.rising, case_36_34_5_checked⟩

    · exact ⟨Witness.rising, case_36_34_6_checked⟩

    · exact ⟨Witness.rising, case_36_34_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_34_8, case_36_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_34_9, case_36_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_34_10, case_36_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_34_11, case_36_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_36_34_12, case_36_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_36_34_13, case_36_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_36_34_14, case_36_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_36_34_15, case_36_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_36_34_16, case_36_34_16_checked⟩

    · exact ⟨Witness.linear .positive case_36_34_17, case_36_34_17_checked⟩

    · exact ⟨Witness.linear .negative case_36_34_18, case_36_34_18_checked⟩

    · exact ⟨Witness.linear .negative case_36_34_19, case_36_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_36_34_20, case_36_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_36_34_21, case_36_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_36_34_22, case_36_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_36_35_1_checked⟩

    · exact ⟨Witness.rising, case_36_35_2_checked⟩

    · exact ⟨Witness.rising, case_36_35_3_checked⟩

    · exact ⟨Witness.rising, case_36_35_4_checked⟩

    · exact ⟨Witness.rising, case_36_35_5_checked⟩

    · exact ⟨Witness.rising, case_36_35_6_checked⟩

    · exact ⟨Witness.rising, case_36_35_7_checked⟩

    · exact ⟨Witness.linear .positive case_36_35_8, case_36_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_36_35_9, case_36_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_36_35_10, case_36_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_36_35_11, case_36_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_36_35_12, case_36_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_36_35_13, case_36_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_36_35_14, case_36_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_36_35_15, case_36_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_36_35_16, case_36_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_36_35_17, case_36_35_17_checked⟩

    · exact ⟨Witness.linear .negative case_36_35_18, case_36_35_18_checked⟩

    · exact ⟨Witness.linear .negative case_36_35_19, case_36_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_36_35_20, case_36_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_36_35_21, case_36_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_36_35_22, case_36_35_22_checked⟩


#print axioms coverage_36
end ForestUnimodality.FiniteRows.FiniteData
