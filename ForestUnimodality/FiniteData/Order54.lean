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

theorem case_54_27_1_checked :
    (Witness.rising).check 54 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_27_2_checked :
    (Witness.rising).check 54 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_27_3_checked :
    (Witness.rising).check 54 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_27_4_checked :
    (Witness.rising).check 54 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_27_5_checked :
    (Witness.rising).check 54 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_27_6_checked :
    (Witness.rising).check 54 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_27_7_checked :
    (Witness.rising).check 54 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_27_8_checked :
    (Witness.rising).check 54 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_27_9_checked :
    (Witness.rising).check 54 27 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_27_10_checked :
    (Witness.rising).check 54 27 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_27_11 : Certificate := {
  objectiveScale := 4029632230000000
  eta := 5247940908053015172000
  rows := #[⟨.count 2, 1419496991965228176000⟩, ⟨.count 4, 15561748316317563360⟩, ⟨.count 5, 2226320711338323600⟩, ⟨.count 6, 362339049821767200⟩, ⟨.count 7, 67914454492684800⟩, ⟨.count 8, 16206858458481600⟩, ⟨.count 9, 5373853067812320⟩, ⟨.count 10, 4021250594961600⟩, ⟨.count 12, 542080349811000⟩, ⟨.path 11, 1339076066328000⟩, ⟨.path 12, 539349681382200⟩, ⟨.hall 2 1, 1315524206790333540⟩, ⟨.hall 10 1, 32704021104300⟩, ⟨.hall 9 3, 5367043463418⟩, ⟨.hall 8 4, 1231834868992⟩, ⟨.hall 8 5, 1658786255620⟩, ⟨.hall 2 7, 25330268197780⟩, ⟨.hall 7 7, 1061224616445⟩, ⟨.hall 7 8, 116020587690⟩, ⟨.hall 6 11, 702523530270⟩, ⟨.hall 6 12, 307200198240⟩, ⟨.hall 9 16, 1792001156400⟩, ⟨.hall 10 16, 16725344126400⟩, ⟨.hall 5 17, 43536146612920⟩, ⟨.hall 4 22, 171059532253449840⟩, ⟨.hall 1 25, 106901596024891668000⟩]
  caps := #[0, 0, 0, 29202563985154560, 0, 0, 0, 183187695334800, 0, 17680348932480, 8381635038400, 3525574851500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_27_11_checked :
    (Witness.linear .positive case_54_27_11).check 54 27 11 = true := by
  change case_54_27_11.check 54 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_27_12 : Certificate := {
  objectiveScale := 10296000000
  eta := 20940656861124000
  rows := #[⟨.count 2, 6039837888084000⟩, ⟨.count 4, 78391265032080⟩, ⟨.count 5, 12918823117200⟩, ⟨.count 6, 2287186902000⟩, ⟨.count 7, 469077008400⟩, ⟨.count 8, 109412503200⟩, ⟨.count 9, 30434564160⟩, ⟨.count 10, 12252240000⟩, ⟨.count 11, 10306296000⟩, ⟨.count 13, 1288287000⟩, ⟨.path 12, 1901542500⟩, ⟨.path 13, 2005163160⟩, ⟨.privateRow 11 2, 154714560⟩, ⟨.privateRow 13 0, 47567520⟩, ⟨.hall 2 1, 6169410226980⟩, ⟨.hall 11 1, 176396220⟩, ⟨.hall 13 1, 43886700⟩, ⟨.hall 14 1, 25105080⟩, ⟨.hall 15 1, 33333300⟩, ⟨.hall 16 1, 49729680⟩, ⟨.hall 17 1, 78958880⟩, ⟨.hall 18 1, 134774640⟩, ⟨.hall 19 1, 216164520⟩, ⟨.hall 10 3, 20373210⟩, ⟨.hall 9 4, 20236788⟩, ⟨.hall 15 4, 75075⟩, ⟨.hall 9 5, 2205720⟩, ⟨.hall 8 6, 10554720⟩, ⟨.hall 20 6, 25773462000⟩, ⟨.hall 8 7, 628320⟩, ⟨.hall 19 7, 7507560060⟩, ⟨.hall 2 8, 38438400⟩, ⟨.hall 7 8, 2286130⟩, ⟨.hall 18 8, 2719997280⟩, ⟨.hall 7 9, 4555530⟩, ⟨.hall 17 9, 1188467280⟩, ⟨.hall 14 10, 2942940⟩, ⟨.hall 16 10, 619819200⟩, ⟨.hall 15 11, 376576200⟩, ⟨.hall 14 12, 118918800⟩, ⟨.hall 6 13, 10180170⟩, ⟨.hall 6 14, 12295140⟩, ⟨.hall 11 14, 3633630⟩, ⟨.hall 5 21, 1908898992000⟩, ⟨.hall 4 22, 1372544933760⟩, ⟨.hall 1 25, 452030773194000⟩]
  caps := #[0, 10109294052000, 0, 252413647200, 17065911720, 0, 0, 499583700, 299304720, 52084032, 0, 25396800, 0, 3363360, 0, 0, 7207200, 0, 0, 174594420, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_27_12_checked :
    (Witness.linear .positive case_54_27_12).check 54 27 12 = true := by
  change case_54_27_12.check 54 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_27_13 : Certificate := {
  objectiveScale := 35035000000
  eta := 44216560648260000
  rows := #[⟨.count 2, 41907817155204000⟩, ⟨.count 4, 573063117026400⟩, ⟨.count 5, 102889655668800⟩, ⟨.count 6, 19896780103200⟩, ⟨.count 7, 4212381373200⟩, ⟨.count 8, 994024231200⟩, ⟨.count 9, 256267851840⟩, ⟨.count 10, 87480993600⟩, ⟨.count 11, 36626990400⟩, ⟨.count 12, 34962127200⟩, ⟨.path 13, 1624923300⟩, ⟨.path 14, 9253759515⟩, ⟨.privateRow 10 7, 5340862800⟩, ⟨.privateRow 10 8, 1783926144⟩, ⟨.privateRow 11 4, 566596800⟩, ⟨.privateRow 12 2, 1228827600⟩, ⟨.privateRow 13 14, 388468080⟩, ⟨.privateRow 14 0, 660707190⟩, ⟨.privateRow 15 0, 661676400⟩, ⟨.privateRow 19 0, 419298880⟩, ⟨.privateRow 19 4, 7135704576⟩, ⟨.hall 2 1, 40265585920560⟩, ⟨.hall 12 1, 1028647620⟩, ⟨.hall 15 1, 835584750⟩, ⟨.hall 16 1, 1306665360⟩, ⟨.hall 17 1, 2468145680⟩, ⟨.hall 19 1, 1571349780⟩, ⟨.hall 20 1, 5237832600⟩, ⟨.hall 12 2, 32931360⟩, ⟨.hall 18 2, 355314960⟩, ⟨.hall 11 3, 99708840⟩, ⟨.hall 19 3, 2537438904⟩, ⟨.hall 21 3, 66811464720⟩, ⟨.hall 10 4, 131004720⟩, ⟨.hall 20 4, 16916259360⟩, ⟨.hall 22 4, 4409556671520⟩, ⟨.hall 21 5, 334057323600⟩, ⟨.hall 9 6, 60270210⟩, ⟨.hall 8 7, 18784150⟩, ⟨.hall 16 7, 3783780⟩, ⟨.hall 8 8, 37600640⟩, ⟨.hall 17 9, 2401439040⟩, ⟨.hall 7 10, 4410000⟩, ⟨.hall 16 10, 958557600⟩, ⟨.hall 7 11, 60761470⟩, ⟨.hall 15 11, 763062300⟩, ⟨.hall 6 16, 1808766960⟩, ⟨.hall 2 17, 464564100⟩, ⟨.hall 5 21, 10563544391400⟩, ⟨.hall 4 22, 4803907268160⟩]
  caps := #[0, 49608417859000, 0, 0, 108794956270, 23835711900, 17992924950, 2878130640, 2580117540, 542879428, 72814196, 32932900, 72872800, 0, 167655345, 0, 0, 85765680, 1543782240, 0, 0, 24443218800, 0, 0, 0, 0, 0, 0] }

theorem case_54_27_13_checked :
    (Witness.linear .positive case_54_27_13).check 54 27 13 = true := by
  change case_54_27_13.check 54 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_27_14 : Certificate := {
  objectiveScale := 6006000000
  eta := 9570684123000000
  rows := #[⟨.count 2, 10407014674056000⟩, ⟨.count 4, 164556870397920⟩, ⟨.count 5, 34108765891200⟩, ⟨.count 6, 7542478944000⟩, ⟨.count 7, 1734304572000⟩, ⟨.count 8, 439512353280⟩, ⟨.count 9, 118650692160⟩, ⟨.count 10, 37491854400⟩, ⟨.count 11, 13160347200⟩, ⟨.count 12, 6064858800⟩, ⟨.count 13, 5977651680⟩, ⟨.path 15, 1106046480⟩, ⟨.path 16, 433959680⟩, ⟨.privateRow 5 22, 1981995855840⟩, ⟨.privateRow 9 11, 1255854600⟩, ⟨.privateRow 10 8, 460684224⟩, ⟨.privateRow 10 9, 3370727360⟩, ⟨.privateRow 10 10, 1265043780⟩, ⟨.privateRow 11 6, 566092800⟩, ⟨.privateRow 11 7, 601080480⟩, ⟨.privateRow 12 4, 469894425⟩, ⟨.privateRow 12 5, 765765000⟩, ⟨.privateRow 14 13, 36808200⟩, ⟨.privateRow 15 0, 85377600⟩, ⟨.privateRow 16 0, 36336300⟩, ⟨.hall 2 1, 10336338852840⟩, ⟨.hall 13 1, 121750200⟩, ⟨.hall 15 1, 29729700⟩, ⟨.hall 13 2, 31145400⟩, ⟨.hall 12 3, 48961440⟩, ⟨.hall 11 5, 18348000⟩, ⟨.hall 10 6, 25389000⟩, ⟨.hall 9 8, 21501648⟩, ⟨.hall 16 8, 11211200⟩, ⟨.hall 17 9, 1715313600⟩, ⟨.hall 8 10, 28648480⟩, ⟨.hall 16 10, 504504000⟩, ⟨.hall 7 13, 14534520⟩, ⟨.hall 13 13, 29446560⟩, ⟨.hall 7 14, 170159990⟩, ⟨.hall 2 18, 290553120⟩, ⟨.hall 6 20, 3592321761600⟩, ⟨.hall 5 21, 3714205294800⟩]
  caps := #[0, 2165488124800, 0, 81709193720, 50645314720, 5431826400, 0, 2845242400, 202161960, 343062720, 0, 0, 0, 57015200, 31900440, 16964640, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_27_14_checked :
    (Witness.linear .positive case_54_27_14).check 54 27 14 = true := by
  change case_54_27_14.check 54 27 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_27_15 : Certificate := {
  objectiveScale := 4004000000
  eta := 4440797433072000
  rows := #[⟨.count 2, 10477690495272000⟩, ⟨.count 4, 206373397950720⟩, ⟨.count 5, 44735746255200⟩, ⟨.count 6, 10992464683200⟩, ⟨.count 7, 2667802737600⟩, ⟨.count 8, 724450446720⟩, ⟨.count 9, 208631142720⟩, ⟨.count 10, 63466603200⟩, ⟨.count 11, 20929708800⟩, ⟨.count 12, 7967559600⟩, ⟨.count 13, 4019455440⟩, ⟨.count 14, 4019455440⟩, ⟨.path 17, 888017760⟩, ⟨.privateRow 5 22, 1014044391360⟩, ⟨.privateRow 10 10, 3213149940⟩, ⟨.privateRow 10 11, 8688588480⟩, ⟨.privateRow 11 8, 1699297600⟩, ⟨.privateRow 11 9, 4731526800⟩, ⟨.privateRow 12 6, 905764860⟩, ⟨.privateRow 12 7, 2321118800⟩, ⟨.privateRow 12 8, 2147970825⟩, ⟨.privateRow 13 4, 456936480⟩, ⟨.privateRow 13 5, 623927304⟩, ⟨.privateRow 17 0, 81244800⟩, ⟨.privateRow 27 0, 4057970068152000⟩, ⟨.hall 2 1, 9933879315360⟩, ⟨.hall 14 1, 36996960⟩, ⟨.hall 15 1, 110810700⟩, ⟨.hall 17 1, 144304160⟩, ⟨.hall 18 1, 324684360⟩, ⟨.hall 19 1, 881286120⟩, ⟨.hall 20 1, 2937620400⟩, ⟨.hall 21 1, 12338005680⟩, ⟨.hall 22 1, 67859031240⟩, ⟨.hall 23 1, 520252572840⟩, ⟨.hall 24 1, 6243030874080⟩, ⟨.hall 25 1, 156075771852000⟩, ⟨.hall 14 2, 63303240⟩, ⟨.hall 13 3, 64452960⟩, ⟨.hall 12 5, 27094320⟩, ⟨.hall 11 7, 22445500⟩, ⟨.hall 10 8, 32088000⟩, ⟨.hall 10 9, 378000⟩, ⟨.hall 9 10, 47300400⟩, ⟨.hall 8 12, 70511760⟩, ⟨.hall 8 13, 64321400⟩, ⟨.hall 13 13, 272380680⟩, ⟨.hall 7 17, 17202825640⟩, ⟨.hall 2 19, 1518694320⟩, ⟨.hall 6 20, 3748625337600⟩, ⟨.hall 5 21, 3138043708800⟩, ⟨.hall 0 23, 1266275130120⟩]
  caps := #[0, 0, 0, 0, 20501662720, 19399380000, 0, 0, 0, 114354240, 0, 0, 279894615, 0, 108348240, 0, 96132960, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_27_15_checked :
    (Witness.linear .positive case_54_27_15).check 54 27 15 = true := by
  change case_54_27_15.check 54 27 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_27_16 : Certificate := {
  objectiveScale := 1732500000
  eta := 7656547298400000
  rows := #[⟨.count 3, 151953015614400⟩, ⟨.count 4, 39578459880960⟩, ⟨.count 5, 10511748046800⟩, ⟨.count 6, 3062386126800⟩, ⟨.count 7, 921858537600⟩, ⟨.count 8, 289128359520⟩, ⟨.count 9, 95493958560⟩, ⟨.count 10, 33571137600⟩, ⟨.count 11, 12684672000⟩, ⟨.count 12, 5529724200⟩, ⟨.count 13, 2885762880⟩, ⟨.count 14, 2215853640⟩, ⟨.count 15, 2199997800⟩, ⟨.path 15, 228477480⟩, ⟨.privateRow 4 23, 2149722895320⟩, ⟨.privateRow 12 7, 711861150⟩, ⟨.privateRow 13 5, 235062828⟩, ⟨.privateRow 14 3, 179690940⟩, ⟨.privateRow 14 4, 211279068⟩, ⟨.privateRow 17 0, 157248000⟩, ⟨.privateRow 19 2, 413075520⟩, ⟨.privateRow 21 5, 1413383400⟩, ⟨.hall 15 1, 193243050⟩, ⟨.hall 17 1, 280440160⟩, ⟨.hall 18 1, 52072020⟩, ⟨.hall 19 1, 141338340⟩, ⟨.hall 14 2, 94534440⟩, ⟨.hall 1 3, 117152855820⟩, ⟨.hall 20 3, 1072508580⟩, ⟨.hall 21 3, 5296030740⟩, ⟨.hall 13 4, 26378352⟩, ⟨.hall 19 4, 286002288⟩, ⟨.hall 22 4, 463489986960⟩, ⟨.hall 12 5, 33731280⟩, ⟨.hall 21 5, 52960307400⟩, ⟨.hall 11 6, 17737830⟩, ⟨.hall 20 6, 7150057200⟩, ⟨.hall 10 7, 306810⟩, ⟨.hall 11 7, 13719860⟩, ⟨.hall 10 8, 32441360⟩, ⟨.hall 18 8, 1715313600⟩, ⟨.hall 9 10, 43751610⟩, ⟨.hall 15 10, 2252250⟩, ⟨.hall 9 11, 848430⟩, ⟨.hall 8 12, 17928240⟩, ⟨.hall 14 12, 142702560⟩, ⟨.hall 8 13, 145754180⟩, ⟨.hall 7 15, 670765095⟩, ⟨.hall 1 17, 24504480⟩, ⟨.hall 6 20, 3761761489200⟩, ⟨.hall 5 21, 4569717952800⟩, ⟨.hall 4 22, 4051056129120⟩, ⟨.hall 0 26, 1837571351616000⟩, ⟨.assumptionRow 16, 1967715288⟩]
  caps := #[0, 25007818355520, 0, 94014767616, 0, 0, 0, 0, 0, 0, 0, 0, 19189170, 2600136, 0, 22372350, 0, 82706400, 0, 0, 166280400, 3824449200, 0, 0, 0, 0, 0, 0] }

theorem case_54_27_16_checked :
    (Witness.linear .conditional case_54_27_16).check 54 27 16 = true := by
  change case_54_27_16.check 54 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_27_17 : Certificate := {
  objectiveScale := 2310000000
  eta := 1416461250204000
  rows := #[⟨.count 2, 397551494340000⟩, ⟨.count 3, 113788072157760⟩, ⟨.count 4, 33394325524560⟩, ⟨.count 5, 10012408005600⟩, ⟨.count 6, 3065878015200⟩, ⟨.count 7, 960269310000⟩, ⟨.count 8, 330099850080⟩, ⟨.count 9, 118430151840⟩, ⟨.count 10, 43985541600⟩, ⟨.count 11, 16807190400⟩, ⟨.count 12, 6421615200⟩, ⟨.count 13, 3452609160⟩, ⟨.count 14, 1752070320⟩, ⟨.count 15, 1486485000⟩, ⟨.count 16, 1506304800⟩, ⟨.path 14, 279233955⟩, ⟨.privateRow 3 24, 1060137318240⟩, ⟨.privateRow 14 4, 169317720⟩, ⟨.privateRow 18 0, 231567336⟩, ⟨.privateRow 22 0, 1551950400⟩, ⟨.privateRow 23 2, 13657163520⟩, ⟨.privateRow 23 3, 26887540680⟩, ⟨.hall 16 1, 247206960⟩, ⟨.hall 18 1, 364504140⟩, ⟨.hall 19 1, 848030040⟩, ⟨.hall 20 1, 2826766800⟩, ⟨.hall 15 2, 126216090⟩, ⟨.hall 22 2, 24326822520⟩, ⟨.hall 14 3, 83765682⟩, ⟨.hall 19 3, 23279256⟩, ⟨.hall 21 3, 8380532160⟩, ⟨.hall 23 3, 2090826377640⟩, ⟨.hall 13 4, 24216192⟩, ⟨.hall 14 4, 10106096⟩, ⟨.hall 22 4, 161325244080⟩, ⟨.hall 13 5, 40563380⟩, ⟨.hall 12 6, 60341160⟩, ⟨.hall 20 6, 9644263200⟩, ⟨.hall 11 7, 34530650⟩, ⟨.hall 12 7, 363825⟩, ⟨.hall 19 7, 2502520020⟩, ⟨.hall 11 8, 29865990⟩, ⟨.hall 18 8, 1004683680⟩, ⟨.hall 10 9, 63744030⟩, ⟨.hall 10 10, 14950800⟩, ⟨.hall 16 10, 21621600⟩, ⟨.hall 9 11, 98664390⟩, ⟨.hall 15 11, 113963850⟩, ⟨.hall 9 12, 59166360⟩, ⟨.hall 14 12, 531170640⟩, ⟨.hall 8 14, 848904056⟩, ⟨.hall 8 18, 125046361440⟩, ⟨.hall 7 19, 4281055178400⟩, ⟨.hall 6 20, 6111137260800⟩, ⟨.hall 5 21, 7715909401200⟩, ⟨.hall 4 22, 8094430103760⟩, ⟨.hall 3 23, 5860203509160⟩, ⟨.assumptionRow 17, 1472295825⟩]
  caps := #[0, 0, 0, 151085355960, 0, 324566550, 1139788650, 1648947300, 228828600, 107717610, 96996900, 70270200, 10626990, 13376055, 9015435, 20073900, 0, 81687375, 0, 0, 1163962800, 1163962800, 0, 17071454400, 0, 0, 0, 0] }

theorem case_54_27_17_checked :
    (Witness.linear .conditional case_54_27_17).check 54 27 17 = true := by
  change case_54_27_17.check 54 27 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_28_1_checked :
    (Witness.rising).check 54 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_28_2_checked :
    (Witness.rising).check 54 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_28_3_checked :
    (Witness.rising).check 54 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_28_4_checked :
    (Witness.rising).check 54 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_28_5_checked :
    (Witness.rising).check 54 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_28_6_checked :
    (Witness.rising).check 54 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_28_7_checked :
    (Witness.rising).check 54 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_28_8_checked :
    (Witness.rising).check 54 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_28_9_checked :
    (Witness.rising).check 54 28 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_28_10_checked :
    (Witness.rising).check 54 28 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_28_11 : Certificate := {
  objectiveScale := 461890791180000000
  eta := 382993094805837119604000
  rows := #[⟨.count 2, 89779243743397054566720⟩, ⟨.count 3, 15209623107895051115280⟩, ⟨.count 4, 1888808013309029772960⟩, ⟨.count 5, 271677013302628533600⟩, ⟨.count 6, 43873306496076657600⟩, ⟨.count 7, 8175177860250721320⟩, ⟨.count 8, 1897779931537089600⟩, ⟨.count 9, 621686529296632800⟩, ⟨.count 10, 461934263254464000⟩, ⟨.count 12, 57164365077739920⟩, ⟨.path 11, 160728325514757000⟩, ⟨.path 12, 58203621945518400⟩, ⟨.privateRow 7 12, 66165209189427348⟩, ⟨.privateRow 7 13, 340940787098391480⟩, ⟨.privateRow 8 9, 70076069311067820⟩, ⟨.privateRow 8 10, 107679676366211040⟩, ⟨.privateRow 8 11, 161311294180652616⟩, ⟨.privateRow 8 12, 40173310811273640⟩, ⟨.privateRow 9 5, 6689492478981312⟩, ⟨.privateRow 9 6, 25656904383670560⟩, ⟨.privateRow 9 7, 45696616683342240⟩, ⟨.privateRow 9 8, 55321618055343640⟩, ⟨.privateRow 9 9, 53344075400572320⟩, ⟨.privateRow 10 3, 23289185772412560⟩, ⟨.privateRow 10 4, 7236970124319936⟩, ⟨.privateRow 11 0, 3662326045478100⟩, ⟨.hall 7 9, 30448391322195⟩, ⟨.hall 6 11, 60053267151900⟩, ⟨.hall 5 17, 1817796869288400⟩, ⟨.hall 8 19, 221189523055012512⟩, ⟨.hall 7 20, 22203090332022600⟩, ⟨.hall 4 22, 2076342908353754040⟩]
  caps := #[0, 0, 0, 30954591204399720, 0, 291551825015708400, 173971247120470800, 11199670879845420, 2406296670952104, 932587398124200, 1856365549762464, 0, 1039256867778480, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_28_11_checked :
    (Witness.linear .positive case_54_28_11).check 54 28 11 = true := by
  change case_54_28_11.check 54 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_28_12 : Certificate := {
  objectiveScale := 1182102480000000
  eta := 1470601311619596156000
  rows := #[⟨.count 2, 368711586583387407360⟩, ⟨.count 3, 63776592964396231920⟩, ⟨.count 4, 9641414246805300960⟩, ⟨.count 5, 1599977793090877200⟩, ⟨.count 6, 285353628159600000⟩, ⟨.count 7, 56728301278128480⟩, ⟨.count 8, 13036155223291200⟩, ⟨.count 9, 3532377544375680⟩, ⟨.count 10, 1434719170684800⟩, ⟨.count 11, 1190445863607000⟩, ⟨.path 12, 242737790724000⟩, ⟨.path 13, 215484287668650⟩, ⟨.privateRow 7 14, 1719255609661590⟩, ⟨.privateRow 8 10, 52565142029400⟩, ⟨.privateRow 8 11, 731706777049248⟩, ⟨.privateRow 8 12, 1115549125290600⟩, ⟨.privateRow 9 7, 28394162190240⟩, ⟨.privateRow 9 8, 228950396394720⟩, ⟨.privateRow 9 9, 396734082064320⟩, ⟨.privateRow 9 10, 571908745279872⟩, ⟨.privateRow 9 11, 576269705211200⟩, ⟨.privateRow 10 4, 2638563992064⟩, ⟨.privateRow 10 5, 83750848140960⟩, ⟨.privateRow 10 6, 138905171697600⟩, ⟨.privateRow 10 7, 195830921286000⟩, ⟨.privateRow 10 8, 230049798058080⟩, ⟨.privateRow 11 3, 120590619949800⟩, ⟨.privateRow 11 4, 13472578419300⟩, ⟨.privateRow 12 0, 28610715713580⟩, ⟨.privateRow 13 0, 13483621516365⟩, ⟨.privateRow 14 0, 12438944534016⟩, ⟨.privateRow 15 0, 2024567795250⟩, ⟨.privateRow 15 7, 25104640661100⟩, ⟨.privateRow 16 0, 2735290196100⟩, ⟨.privateRow 16 10, 63387377153100⟩, ⟨.privateRow 17 0, 5153445297000⟩, ⟨.privateRow 17 9, 17315576197920⟩, ⟨.privateRow 18 0, 6796301191680⟩, ⟨.privateRow 18 6, 14951862621696⟩, ⟨.privateRow 19 0, 10513028405880⟩, ⟨.privateRow 20 0, 31705958684400⟩, ⟨.privateRow 20 8, 1198485238270320⟩, ⟨.privateRow 21 0, 107007610559850⟩, ⟨.privateRow 21 4, 71338407039900⟩, ⟨.privateRow 22 0, 513636530687280⟩, ⟨.privateRow 23 0, 2563426759633740⟩, ⟨.privateRow 24 0, 20214451018826064⟩, ⟨.privateRow 25 0, 252680637735325800⟩, ⟨.privateRow 26 2, 20214451018826064000⟩, ⟨.hall 15 3, 71355396420⟩, ⟨.hall 18 3, 1201488960672⟩, ⟨.hall 19 3, 1585297934220⟩, ⟨.hall 16 5, 53542288800⟩, ⟨.hall 19 6, 6341191736880⟩, ⟨.hall 21 6, 2282829025276800⟩, ⟨.hall 20 7, 570707256319200⟩, ⟨.hall 7 9, 163551099096⟩, ⟨.hall 18 9, 479394095308128⟩, ⟨.hall 7 10, 262614629970⟩, ⟨.hall 8 10, 96278573160⟩, ⟨.hall 17 10, 244666842900480⟩, ⟨.hall 8 11, 69491532264⟩, ⟨.hall 16 11, 119559930890400⟩, ⟨.hall 6 13, 1015391262600⟩, ⟨.hall 9 18, 1080075339383040⟩, ⟨.hall 5 22, 387597073797133200⟩, ⟨.hall 4 23, 401725593616887540⟩]
  caps := #[0, 562612410627813000, 36503523175616640, 23740927744042080, 1477415321553600, 0, 49626717940800, 298206332899020, 0, 18262866188970, 0, 0, 6847000367220, 0, 0, 5668789826700, 10309773640320, 9070063722720, 0, 0, 47558938026600, 1569444954877800, 0, 5859261164877120, 60643353056478192, 1010722550941303200, 0] }

theorem case_54_28_12_checked :
    (Witness.linear .positive case_54_28_12).check 54 28 12 = true := by
  change case_54_28_12.check 54 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_28_13 : Certificate := {
  objectiveScale := 18897278400000
  eta := 35186116612983336000
  rows := #[⟨.count 2, 9975345133782188160⟩, ⟨.count 3, 2083601836298782800⟩, ⟨.count 4, 337831838928904320⟩, ⟨.count 5, 61141974187694400⟩, ⟨.count 6, 11810893486392000⟩, ⟨.count 7, 2473878620172960⟩, ⟨.count 8, 566691584659200⟩, ⟨.count 9, 145720693198080⟩, ⟨.count 10, 47621141568000⟩, ⟨.count 11, 20189379810600⟩, ⟨.count 12, 18770666634720⟩, ⟨.path 13, 1392815314800⟩, ⟨.path 14, 4642620366384⟩, ⟨.privateRow 8 12, 10794125422080⟩, ⟨.privateRow 8 13, 12775859386290⟩, ⟨.privateRow 9 9, 1771763011200⟩, ⟨.privateRow 9 10, 12293309508480⟩, ⟨.privateRow 9 11, 18073497041600⟩, ⟨.privateRow 9 12, 5134705495920⟩, ⟨.privateRow 10 7, 3445918716240⟩, ⟨.privateRow 10 8, 6255686324160⟩, ⟨.privateRow 10 9, 10103618869344⟩, ⟨.privateRow 10 10, 11790641903040⟩, ⟨.privateRow 11 4, 680302022400⟩, ⟨.privateRow 11 5, 2102503926600⟩, ⟨.privateRow 11 6, 3464107346700⟩, ⟨.privateRow 11 7, 4401347932800⟩, ⟨.privateRow 11 8, 1150844254560⟩, ⟨.privateRow 12 2, 594161928360⟩, ⟨.privateRow 12 3, 1946183459220⟩, ⟨.privateRow 13 0, 574890641325⟩, ⟨.privateRow 14 0, 309726392976⟩, ⟨.privateRow 15 0, 327395348280⟩, ⟨.privateRow 16 0, 454079795400⟩, ⟨.privateRow 17 0, 601878317040⟩, ⟨.privateRow 17 3, 185193328320⟩, ⟨.privateRow 18 0, 1390152516480⟩, ⟨.privateRow 19 0, 2631068071632⟩, ⟨.privateRow 20 0, 7222854759120⟩, ⟨.privateRow 21 0, 17929973961900⟩, ⟨.privateRow 22 0, 54934388308800⟩, ⟨.privateRow 22 1, 42726746462400⟩, ⟨.privateRow 23 0, 458244355809240⟩, ⟨.privateRow 23 1, 84598957995552⟩, ⟨.privateRow 23 2, 17624782915740⟩, ⟨.privateRow 24 0, 4215848073445008⟩, ⟨.privateRow 25 0, 50265880875690480⟩, ⟨.privateRow 26 0, 1351233356873400000⟩, ⟨.hall 20 2, 2724920055000⟩, ⟨.hall 21 2, 4272674646240⟩, ⟨.hall 22 3, 14099826332592⟩, ⟨.hall 24 3, 3242960056496160⟩, ⟨.hall 23 4, 648592011299232⟩, ⟨.hall 18 5, 34267064832⟩, ⟨.hall 19 5, 152595523080⟩, ⟨.hall 21 5, 4577865692400⟩, ⟨.hall 22 5, 46999421108640⟩, ⟨.hall 20 6, 653980813200⟩, ⟨.hall 8 9, 13858096896⟩, ⟨.hall 9 9, 790180272⟩, ⟨.hall 9 10, 4704729120⟩, ⟨.hall 7 11, 22295154420⟩, ⟨.hall 14 12, 7195502160⟩, ⟨.hall 15 12, 83947525200⟩, ⟨.hall 6 16, 345427524000⟩, ⟨.hall 6 17, 125859146400⟩, ⟨.hall 10 17, 19621674072000⟩, ⟨.hall 5 22, 11444266155722400⟩, ⟨.hall 4 23, 9211886537293440⟩]
  caps := #[0, 22551398739979200, 0, 0, 14993203758624, 36419464841760, 7881890496480, 0, 0, 522870513984, 1737319887072, 134112310920, 126611765280, 0, 0, 452117385720, 195877558800, 0, 2044341936000, 0, 21261642882480, 0, 161201910581712, 28199652665184, 0, 152419122655319520, 0] }

theorem case_54_28_13_checked :
    (Witness.linear .positive case_54_28_13).check 54 28 13 = true := by
  change case_54_28_13.check 54 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_28_14 : Certificate := {
  objectiveScale := 29280939187500
  eta := 71209997907228180000
  rows := #[⟨.count 2, 21905114194946062080⟩, ⟨.count 3, 4920381145718798760⟩, ⟨.count 4, 942009397280471520⟩, ⟨.count 5, 191757638123251200⟩, ⟨.count 6, 41039039977135200⟩, ⟨.count 7, 9079433623260000⟩, ⟨.count 8, 2309043329873280⟩, ⟨.count 9, 596375429569920⟩, ⟨.count 10, 186648418756800⟩, ⟨.count 11, 64933410742200⟩, ⟨.count 12, 29683844910720⟩, ⟨.count 13, 28712052369000⟩, ⟨.path 15, 6327092267496⟩, ⟨.path 16, 1311998510592⟩, ⟨.privateRow 9 11, 27751563199360⟩, ⟨.privateRow 9 12, 69821375523900⟩, ⟨.privateRow 9 13, 68327099480640⟩, ⟨.privateRow 10 8, 1083501226080⟩, ⟨.privateRow 10 9, 19227035908080⟩, ⟨.privateRow 10 10, 36380200496640⟩, ⟨.privateRow 10 11, 32916460597020⟩, ⟨.privateRow 11 6, 2857819664700⟩, ⟨.privateRow 11 7, 9007881655500⟩, ⟨.privateRow 11 8, 18552403069200⟩, ⟨.privateRow 11 9, 29343405191100⟩, ⟨.privateRow 12 4, 2513295629460⟩, ⟨.privateRow 12 5, 5101910844030⟩, ⟨.privateRow 12 6, 8114333867640⟩, ⟨.privateRow 12 7, 12038448213792⟩, ⟨.privateRow 13 2, 2000378154060⟩, ⟨.privateRow 13 3, 3071679922080⟩, ⟨.privateRow 13 4, 890809829910⟩, ⟨.privateRow 14 0, 1289833737192⟩, ⟨.privateRow 15 0, 449085947310⟩, ⟨.privateRow 16 0, 140548508100⟩, ⟨.privateRow 16 9, 1018976683725⟩, ⟨.privateRow 17 0, 206137811880⟩, ⟨.privateRow 18 0, 424768824480⟩, ⟨.privateRow 19 0, 764583884064⟩, ⟨.privateRow 20 0, 288235988040⟩, ⟨.privateRow 20 5, 3242654865450⟩, ⟨.privateRow 21 0, 1080884955150⟩, ⟨.privateRow 21 4, 2161769910300⟩, ⟨.privateRow 22 0, 5188247784720⟩, ⟨.privateRow 22 6, 399495079423440⟩, ⟨.privateRow 23 0, 33291256618620⟩, ⟨.privateRow 24 0, 306279560891304⟩, ⟨.hall 19 2, 72058997010⟩, ⟨.hall 23 4, 918838682673912⟩, ⟨.hall 22 5, 133165026474480⟩, ⟨.hall 20 7, 90794336232600⟩, ⟨.hall 16 8, 2271491040⟩, ⟨.hall 19 8, 28247126827920⟩, ⟨.hall 9 9, 54175061304⟩, ⟨.hall 10 9, 24940149360⟩, ⟨.hall 18 9, 12997926029088⟩, ⟨.hall 10 10, 1618822800⟩, ⟨.hall 16 10, 340723656000⟩, ⟨.hall 17 10, 6255686324160⟩, ⟨.hall 8 11, 93344947080⟩, ⟨.hall 7 13, 140102322360⟩, ⟨.hall 7 14, 160827649983⟩, ⟨.hall 12 15, 9508106572965⟩, ⟨.hall 11 16, 64387751828400⟩, ⟨.hall 6 19, 140924938204440⟩, ⟨.hall 5 22, 39365266126586400⟩, ⟨.hall 4 23, 30994159911935220⟩]
  caps := #[0, 198200349609181920, 14024379893443920, 687071742227640, 559930264429536, 87308197808832, 0, 2739816452373, 0, 4087894258448, 0, 133656326076, 0, 568886818500, 39409942572, 295637974632, 0, 2023898516640, 1660459950240, 8861739600714, 0, 4323539820600, 508448282902560, 2263805450066160, 0, 0, 0] }

theorem case_54_28_14_checked :
    (Witness.linear .positive case_54_28_14).check 54 28 14 = true := by
  change case_54_28_14.check 54 28 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_28_15 : Certificate := {
  objectiveScale := 490089600000
  eta := 1403939850545232000
  rows := #[⟨.count 2, 462957726326135040⟩, ⟨.count 3, 108548520151911840⟩, ⟨.count 4, 24753806908871040⟩, ⟨.count 5, 5549169369744000⟩, ⟨.count 6, 1374080034412800⟩, ⟨.count 7, 337010530016160⟩, ⟨.count 8, 90990231171840⟩, ⟨.count 9, 26214304596480⟩, ⟨.count 10, 7933570444800⟩, ⟨.count 11, 2611932523200⟩, ⟨.count 12, 983315773440⟩, ⟨.count 13, 485073182880⟩, ⟨.count 14, 491657886720⟩, ⟨.path 16, 12312558720⟩, ⟨.path 17, 91681438464⟩, ⟨.privateRow 9 12, 511833241920⟩, ⟨.privateRow 9 13, 3295633186560⟩, ⟨.privateRow 10 10, 405990224640⟩, ⟨.privateRow 10 11, 1487544458400⟩, ⟨.privateRow 10 12, 3150281946240⟩, ⟨.privateRow 11 8, 223830046440⟩, ⟨.privateRow 11 9, 700705605600⟩, ⟨.privateRow 11 10, 1350924324750⟩, ⟨.privateRow 11 11, 156137295600⟩, ⟨.privateRow 12 6, 114301146960⟩, ⟨.privateRow 12 7, 335198007144⟩, ⟨.privateRow 12 8, 637049773360⟩, ⟨.privateRow 12 9, 961229579310⟩, ⟨.privateRow 13 4, 59993968320⟩, ⟨.privateRow 13 5, 163420377120⟩, ⟨.privateRow 13 6, 305091277920⟩, ⟨.privateRow 13 7, 283142265120⟩, ⟨.privateRow 14 2, 36806806080⟩, ⟨.privateRow 14 3, 84137882400⟩, ⟨.privateRow 14 4, 76222935360⟩, ⟨.privateRow 15 0, 40788582120⟩, ⟨.privateRow 15 1, 1772804880⟩, ⟨.privateRow 16 0, 10475665200⟩, ⟨.privateRow 17 0, 7449361920⟩, ⟨.privateRow 18 0, 13431425280⟩, ⟨.privateRow 19 0, 30868293456⟩, ⟨.privateRow 20 0, 35805712800⟩, ⟨.privateRow 21 0, 107417138400⟩, ⟨.privateRow 22 0, 257801132160⟩, ⟨.privateRow 23 0, 827111965680⟩, ⟨.hall 23 4, 91313161011072⟩, ⟨.hall 22 5, 16542239313600⟩, ⟨.hall 21 6, 3222514152000⟩, ⟨.hall 20 7, 966754245600⟩, ⟨.hall 19 8, 350895985440⟩, ⟨.hall 10 9, 2499336000⟩, ⟨.hall 9 10, 671731200⟩, ⟨.hall 11 10, 540599400⟩, ⟨.hall 9 11, 3880661400⟩, ⟨.hall 11 11, 2016855225⟩, ⟨.hall 8 12, 3057970608⟩, ⟨.hall 8 13, 7653449232⟩, ⟨.hall 13 14, 340502351904⟩, ⟨.hall 12 15, 1978154778600⟩, ⟨.hall 7 16, 144127416576⟩, ⟨.hall 6 21, 1077550141262400⟩, ⟨.hall 5 22, 1317363785337600⟩, ⟨.hall 4 23, 1031408621202960⟩]
  caps := #[0, 5432914627620480, 211170787027200, 53758929137760, 2106106523136, 2622221954352, 310265923968, 209098509984, 307552227840, 0, 87016808736, 4072267584, 11869404624, 17846962848, 0, 3706208352, 0, 20912500224, 38375500800, 104477300928, 393862840800, 0, 13921261136640, 13564636237152, 0, 0, 0] }

theorem case_54_28_15_checked :
    (Witness.linear .positive case_54_28_15).check 54 28 15 = true := by
  change case_54_28_15.check 54 28 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_28_16 : Certificate := {
  objectiveScale := 21677040000000
  eta := 40035114030791880000
  rows := #[⟨.count 2, 10396003381110547200⟩, ⟨.count 3, 2730263514231052800⟩, ⟨.count 4, 725939630038022400⟩, ⟨.count 5, 196375178651652000⟩, ⟨.count 6, 54402483914064000⟩, ⟨.count 7, 15564743354160000⟩, ⟨.count 8, 4653039065875200⟩, ⟨.count 9, 1507322514297600⟩, ⟨.count 10, 514005972480000⟩, ⟨.count 11, 189941269518000⟩, ⟨.count 12, 81277194398400⟩, ⟨.count 13, 42657906376800⟩, ⟨.count 14, 30037224016800⟩, ⟨.count 15, 30920671782000⟩, ⟨.path 15, 2985620008800⟩, ⟨.privateRow 3 25, 24064822641459600⟩, ⟨.privateRow 9 13, 224954101944000⟩, ⟨.privateRow 10 10, 35694859200⟩, ⟨.privateRow 10 11, 76900112289000⟩, ⟨.privateRow 11 9, 30563723190000⟩, ⟨.privateRow 11 10, 88671049842375⟩, ⟨.privateRow 11 11, 2810970162000⟩, ⟨.privateRow 12 7, 13222268219160⟩, ⟨.privateRow 12 8, 39935111015800⟩, ⟨.privateRow 12 9, 75442758115725⟩, ⟨.privateRow 13 5, 5610466976400⟩, ⟨.privateRow 13 6, 18299989422000⟩, ⟨.privateRow 13 7, 35618370216000⟩, ⟨.privateRow 13 8, 47879713703250⟩, ⟨.privateRow 14 3, 2650343295600⟩, ⟨.privateRow 14 4, 8788584261600⟩, ⟨.privateRow 14 5, 17366058927360⟩, ⟨.privateRow 14 6, 2187584942400⟩, ⟨.privateRow 15 1, 1563022969200⟩, ⟨.privateRow 15 2, 4957123571400⟩, ⟨.privateRow 15 3, 843291048600⟩, ⟨.privateRow 16 0, 2208619413000⟩, ⟨.privateRow 17 0, 1793666674800⟩, ⟨.privateRow 18 0, 3199557379200⟩, ⟨.privateRow 19 0, 7236240331320⟩, ⟨.privateRow 20 0, 9058845338400⟩, ⟨.privateRow 20 3, 617648545800⟩, ⟨.privateRow 21 0, 33970670019000⟩, ⟨.privateRow 22 0, 118588520793600⟩, ⟨.privateRow 23 0, 237794690133000⟩, ⟨.privateRow 23 3, 760943008425600⟩, ⟨.privateRow 24 0, 2187711149223600⟩, ⟨.hall 19 3, 411765697200⟩, ⟨.hall 24 3, 157515202744099200⟩, ⟨.hall 23 4, 17064146963944080⟩, ⟨.hall 22 5, 2282829025276800⟩, ⟨.hall 21 6, 592942603968000⟩, ⟨.hall 20 7, 166765107366000⟩, ⟨.hall 10 8, 85536981600⟩, ⟨.hall 11 8, 180139921500⟩, ⟨.hall 19 8, 51882477847200⟩, ⟨.hall 10 9, 222935025600⟩, ⟨.hall 9 10, 332545500000⟩, ⟨.hall 9 11, 109180024800⟩, ⟨.hall 8 12, 17016476400⟩, ⟨.hall 8 13, 1278211437360⟩, ⟨.hall 12 13, 2757619095660⟩, ⟨.hall 14 13, 8834477652000⟩, ⟨.hall 12 14, 3018446531100⟩, ⟨.hall 13 14, 62783687846880⟩, ⟨.hall 7 16, 9816596206560⟩, ⟨.hall 11 16, 74053709730000⟩, ⟨.hall 7 19, 931290477357240⟩, ⟨.hall 6 21, 106079453245116000⟩, ⟨.hall 5 22, 148519232237376000⟩, ⟨.hall 4 23, 170736587515494000⟩, ⟨.hall 3 24, 133362871656670656⟩, ⟨.assumptionRow 16, 27793971196992⟩]
  caps := #[0, 0, 12060727297449600, 2303025615933504, 561210172250112, 151029589606896, 60526429199808, 0, 5348826342288, 0, 0, 224983639188, 858239432160, 2580597419400, 807222828192, 0, 0, 1223885678400, 0, 26487370269360, 1647062788800, 0, 0, 2282829025276800, 8313302367049680, 0, 0] }

theorem case_54_28_16_checked :
    (Witness.linear .conditional case_54_28_16).check 54 28 16 = true := by
  change case_54_28_16.check 54 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_28_17 : Certificate := {
  objectiveScale := 376868800000000
  eta := 248086444321956240000
  rows := #[⟨.count 2, 71301881775495571200⟩, ⟨.count 3, 20857638096697802400⟩, ⟨.count 4, 6184183829474851200⟩, ⟨.count 5, 1928471701580424000⟩, ⟨.count 6, 618439135938624000⟩, ⟨.count 7, 204105667850884800⟩, ⟨.count 8, 69118383119385600⟩, ⟨.count 9, 24160850736422400⟩, ⟨.count 10, 8680275860256000⟩, ⟨.count 11, 3184829193546000⟩, ⟨.count 12, 1360509558408000⟩, ⟨.count 13, 666119614960800⟩, ⟨.count 14, 346311523958400⟩, ⟨.count 15, 309206717820000⟩, ⟨.count 16, 314828658144000⟩, ⟨.count 18, 305833553625600⟩, ⟨.path 14, 31295467803600⟩, ⟨.privateRow 2 26, 367535473069564800⟩, ⟨.privateRow 3 25, 551303209604347200⟩, ⟨.privateRow 10 11, 582433017566400⟩, ⟨.privateRow 11 9, 120559386948000⟩, ⟨.privateRow 11 10, 1075898829505500⟩, ⟨.privateRow 12 7, 14635784643480⟩, ⟨.privateRow 12 8, 383874414123200⟩, ⟨.privateRow 12 9, 1123451074746000⟩, ⟨.privateRow 13 6, 126863099082720⟩, ⟨.privateRow 13 7, 484129375329600⟩, ⟨.privateRow 13 8, 999400284382500⟩, ⟨.privateRow 14 4, 36944179272000⟩, ⟨.privateRow 14 5, 203192985996000⟩, ⟨.privateRow 14 6, 476865471482400⟩, ⟨.privateRow 14 7, 816084873103500⟩, ⟨.privateRow 15 2, 5668789826700⟩, ⟨.privateRow 15 3, 91075433248800⟩, ⟨.privateRow 15 4, 226957730879880⟩, ⟨.privateRow 15 5, 219193206632400⟩, ⟨.privateRow 16 1, 40290572322000⟩, ⟨.privateRow 16 2, 72574138728000⟩, ⟨.privateRow 17 0, 18365005058400⟩, ⟨.hall 12 7, 2995725380340⟩, ⟨.hall 11 8, 7138648809600⟩, ⟨.hall 12 8, 1852597514460⟩, ⟨.hall 10 9, 6124392086400⟩, ⟨.hall 11 9, 291113482275⟩, ⟨.hall 10 10, 3936308964000⟩, ⟨.hall 9 11, 11897497596600⟩, ⟨.hall 13 11, 2250688354200⟩, ⟨.hall 9 12, 4652976636000⟩, ⟨.hall 13 12, 32813774136000⟩, ⟨.hall 8 13, 2782508208480⟩, ⟨.hall 8 14, 67870299216720⟩, ⟨.hall 12 15, 108222351237000⟩, ⟨.hall 7 16, 108676568320320⟩, ⟨.hall 7 20, 944053566907651200⟩, ⟨.hall 6 21, 2301931210302360000⟩, ⟨.hall 5 22, 3278859811947720000⟩, ⟨.hall 4 23, 4133442421767859200⟩, ⟨.hall 3 24, 4307515744375299456⟩, ⟨.hall 2 25, 2629292230420732800⟩, ⟨.assumptionRow 17, 309663453052800⟩]
  caps := #[0, 782594425172560000, 371590849311281600, 0, 0, 0, 229491956293600, 0, 98636794256000, 40605970845440, 54917480217600, 0, 12507477353140, 26902780704800, 0, 456735232800, 17721529081200, 6403595968000, 71035246374400, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_28_17_checked :
    (Witness.linear .conditional case_54_28_17).check 54 28 17 = true := by
  change case_54_28_17.check 54 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_28_18 : Certificate := {
  objectiveScale := 123559128000000
  eta := 62481030421826016000
  rows := #[⟨.count 2, 18670802031933891840⟩, ⟨.count 3, 5568162417003906720⟩, ⟨.count 4, 1671487412307672960⟩, ⟨.count 5, 549850500224625600⟩, ⟨.count 6, 181588672465200000⟩, ⟨.count 7, 60214803789460320⟩, ⟨.count 8, 19940347696389120⟩, ⟨.count 9, 6575421402950400⟩, ⟨.count 10, 2410688010931200⟩, ⟨.count 11, 927620153460000⟩, ⟨.count 12, 336416908988160⟩, ⟨.count 13, 147005708129280⟩, ⟨.count 14, 64314997306560⟩, ⟨.count 15, 49473074851200⟩, ⟨.count 16, 53970627110400⟩, ⟨.count 17, 45875033043840⟩, ⟨.count 19, 145270937972160⟩, ⟨.path 14, 14179158157164⟩, ⟨.privateRow 2 26, 514549662297390720⟩, ⟨.privateRow 10 11, 39241143461520⟩, ⟨.privateRow 11 10, 193675844161800⟩, ⟨.privateRow 12 8, 39715885088880⟩, ⟨.privateRow 12 9, 253858715330220⟩, ⟨.privateRow 13 6, 5300686591200⟩, ⟨.privateRow 13 7, 80845286602080⟩, ⟨.privateRow 13 8, 255669783248880⟩, ⟨.privateRow 14 5, 21909504576960⟩, ⟨.privateRow 14 6, 105424766647200⟩, ⟨.privateRow 14 7, 250324924269420⟩, ⟨.privateRow 14 8, 163311629738400⟩, ⟨.privateRow 15 3, 2023898516640⟩, ⟨.privateRow 15 4, 38836363758192⟩, ⟨.privateRow 15 5, 113421604936640⟩, ⟨.privateRow 15 6, 223041112454160⟩, ⟨.privateRow 15 7, 27799156344960⟩, ⟨.privateRow 16 2, 8739561776400⟩, ⟨.privateRow 16 3, 51609412174320⟩, ⟨.privateRow 16 4, 84766366885200⟩, ⟨.privateRow 17 1, 21997119231360⟩, ⟨.privateRow 17 2, 11153929602816⟩, ⟨.privateRow 18 0, 5869532847360⟩, ⟨.hall 12 7, 1244851350204⟩, ⟨.hall 13 7, 251559520212⟩, ⟨.hall 11 8, 813188653200⟩, ⟨.hall 12 8, 2185493262876⟩, ⟨.hall 13 8, 1876937682048⟩, ⟨.hall 11 9, 3542172185475⟩, ⟨.hall 10 10, 3613212489600⟩, ⟨.hall 10 11, 2736915442800⟩, ⟨.hall 9 12, 6584314191840⟩, ⟨.hall 9 13, 8437607178000⟩, ⟨.hall 14 13, 818072630575200⟩, ⟨.hall 8 14, 28905058230048⟩, ⟨.hall 7 18, 2013895746246384⟩, ⟨.hall 7 20, 160095491309033280⟩, ⟨.hall 6 21, 817488620493854400⟩, ⟨.hall 5 22, 1136681928354772800⟩, ⟨.hall 4 23, 1425931103488731840⟩, ⟨.hall 3 24, 1539973632161476512⟩, ⟨.hall 2 25, 1249620608436520320⟩, ⟨.assumptionRow 18, 49692412492800⟩]
  caps := #[0, 643884429438650400, 0, 0, 2771638655629536, 0, 122538061033080, 19809673359840, 8834036715504, 4969219232208, 3679200645120, 2665755075984, 2842334394900, 8575191244620, 0, 247158634800, 525346542000, 3817379448960, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_28_18_checked :
    (Witness.linear .conditional case_54_28_18).check 54 28 18 = true := by
  change case_54_28_18.check 54 28 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_29_1_checked :
    (Witness.rising).check 54 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_29_2_checked :
    (Witness.rising).check 54 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_29_3_checked :
    (Witness.rising).check 54 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_29_4_checked :
    (Witness.rising).check 54 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_29_5_checked :
    (Witness.rising).check 54 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_29_6_checked :
    (Witness.rising).check 54 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_29_7_checked :
    (Witness.rising).check 54 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_29_8_checked :
    (Witness.rising).check 54 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_29_9_checked :
    (Witness.rising).check 54 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_29_10_checked :
    (Witness.rising).check 54 29 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_29_11 : Certificate := {
  objectiveScale := 29615487212700000000
  eta := 32632397958678301301918400
  rows := #[⟨.count 2, 7085809325840892245398800⟩, ⟨.count 3, 1041419295422334389761200⟩, ⟨.count 4, 130814588942672372337600⟩, ⟨.count 5, 18518702754581465436000⟩, ⟨.count 6, 2953719452608501777200⟩, ⟨.count 7, 551642312114228134800⟩, ⟨.count 8, 124596806379169924800⟩, ⟨.count 9, 40428944764398590400⟩, ⟨.count 10, 29701088807178789000⟩, ⟨.count 12, 3622392920619673200⟩, ⟨.path 11, 10674866328247440000⟩, ⟨.path 12, 3568680930278964500⟩, ⟨.privateRow 6 16, 12613991198812853850⟩, ⟨.privateRow 6 17, 114938298182232954000⟩, ⟨.privateRow 6 18, 142504008678480348900⟩, ⟨.privateRow 6 19, 157913533061894970360⟩, ⟨.privateRow 7 12, 1761685050396726000⟩, ⟨.privateRow 7 13, 23469559726951938600⟩, ⟨.privateRow 7 14, 31244898066665883600⟩, ⟨.privateRow 7 15, 46454656065044777550⟩, ⟨.privateRow 7 16, 59181432391422712800⟩, ⟨.privateRow 7 17, 59355736679477838600⟩, ⟨.privateRow 7 18, 59513635858068952560⟩, ⟨.privateRow 8 9, 4173838427093781600⟩, ⟨.privateRow 8 10, 6908089063361235750⟩, ⟨.privateRow 8 11, 12423141985019875200⟩, ⟨.privateRow 8 12, 14871231729126732960⟩, ⟨.privateRow 8 13, 11834463688344096800⟩, ⟨.privateRow 8 14, 26836879330997285550⟩, ⟨.privateRow 9 5, 330012097857542100⟩, ⟨.privateRow 9 6, 635724797464877120⟩, ⟨.privateRow 9 7, 698021324253052800⟩, ⟨.privateRow 9 8, 12354804232995100800⟩, ⟨.privateRow 10 3, 1491573555549277200⟩, ⟨.privateRow 10 4, 498712312060837875⟩, ⟨.privateRow 11 0, 227093949507625200⟩, ⟨.hall 5 18, 60755912231878500⟩, ⟨.hall 6 22, 247595897749670870400⟩, ⟨.hall 4 23, 218024314904453953896⟩]
  caps := #[0, 0, 0, 0, 15695225603236967400, 0, 3345809016923363850, 0, 100091631147005120, 178578713621096560, 0, 103939908551386200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_29_11_checked :
    (Witness.linear .positive case_54_29_11).check 54 29 11 = true := by
  change case_54_29_11.check 54 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_29_12 : Certificate := {
  objectiveScale := 4057560000000
  eta := 7660213017660403200
  rows := #[⟨.count 2, 1842513358414528800⟩, ⟨.count 3, 305088084338637600⟩, ⟨.count 4, 43657739780054400⟩, ⟨.count 5, 6872152767480000⟩, ⟨.count 6, 1190566333756800⟩, ⟨.count 7, 228369133792800⟩, ⟨.count 8, 49630883702400⟩, ⟨.count 9, 13255943500800⟩, ⟨.count 10, 5030157132000⟩, ⟨.count 11, 4014262652400⟩, ⟨.path 12, 976166282000⟩, ⟨.path 13, 676613246400⟩, ⟨.privateRow 6 18, 45283390752600⟩, ⟨.privateRow 6 19, 70815031166880⟩, ⟨.privateRow 7 14, 3976219447200⟩, ⟨.privateRow 7 15, 13311951552900⟩, ⟨.privateRow 7 16, 19627878441600⟩, ⟨.privateRow 7 17, 29366536399200⟩, ⟨.privateRow 7 18, 38027987917920⟩, ⟨.privateRow 8 11, 1930767384000⟩, ⟨.privateRow 8 12, 4107961657800⟩, ⟨.privateRow 8 13, 6315641732400⟩, ⟨.privateRow 8 14, 8551267124400⟩, ⟨.privateRow 8 15, 9629157938400⟩, ⟨.privateRow 8 16, 12724434522800⟩, ⟨.privateRow 8 17, 8148854553840⟩, ⟨.privateRow 9 8, 681815164800⟩, ⟨.privateRow 9 9, 1391786396000⟩, ⟨.privateRow 9 10, 2099335929600⟩, ⟨.privateRow 9 11, 2703791650560⟩, ⟨.privateRow 9 12, 3138642707200⟩, ⟨.privateRow 9 13, 2896449956400⟩, ⟨.privateRow 10 5, 234740666160⟩, ⟨.privateRow 10 7, 1670649472800⟩, ⟨.privateRow 10 8, 590550310350⟩, ⟨.privateRow 11 3, 399453654600⟩, ⟨.privateRow 11 4, 18411032640⟩, ⟨.privateRow 12 0, 83953369500⟩, ⟨.privateRow 13 0, 39975012000⟩, ⟨.privateRow 14 0, 39716401725⟩, ⟨.privateRow 15 0, 50630339760⟩, ⟨.privateRow 16 0, 76086410400⟩, ⟨.privateRow 17 0, 137576947200⟩, ⟨.privateRow 18 0, 293425832700⟩, ⟨.privateRow 19 0, 757789905600⟩, ⟨.privateRow 20 0, 2412080110440⟩, ⟨.privateRow 21 0, 9709001702400⟩, ⟨.privateRow 22 0, 51370479710550⟩, ⟨.privateRow 23 0, 380471504212800⟩, ⟨.privateRow 24 0, 4298660503737600⟩, ⟨.privateRow 25 0, 104457450240823680⟩, ⟨.hall 13 13, 55353870⟩, ⟨.hall 6 16, 4192812000⟩, ⟨.hall 5 19, 80220215400⟩, ⟨.hall 5 20, 206225487000⟩, ⟨.hall 7 21, 27162848512800⟩, ⟨.hall 4 22, 6327208663776⟩]
  caps := #[0, 952254473788800, 657148500169200, 0, 14628518190000, 3692888147520, 3261617759400, 22331457720, 183128352680, 0, 3569150000, 93269514000, 45068375300, 40379371200, 0, 0, 194443048800, 0, 0, 0, 318576618360, 3034063032000, 27477233333550, 0, 2149330251868800, 0] }

theorem case_54_29_12_checked :
    (Witness.linear .positive case_54_29_12).check 54 29 12 = true := by
  change case_54_29_12.check 54 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_29_13 : Certificate := {
  objectiveScale := 107931096000000
  eta := 293293307509512710400
  rows := #[⟨.count 2, 76171726793667304800⟩, ⟨.count 3, 13770595387725976800⟩, ⟨.count 4, 2266226632365696000⟩, ⟨.count 5, 392231532524832000⟩, ⟨.count 6, 74866415533509600⟩, ⟨.count 7, 15368136069686400⟩, ⟨.count 8, 3440627478288000⟩, ⟨.count 9, 904008004099200⟩, ⟨.count 10, 286718956524000⟩, ⟨.count 11, 117498552771600⟩, ⟨.count 12, 106013731824000⟩, ⟨.path 13, 10701685612800⟩, ⟨.path 14, 24923194732800⟩, ⟨.privateRow 4 25, 19611576626241600⟩, ⟨.privateRow 6 19, 4352939891380080⟩, ⟨.privateRow 7 15, 112639590063000⟩, ⟨.privateRow 7 16, 1046231620948800⟩, ⟨.privateRow 7 17, 1492303902289200⟩, ⟨.privateRow 7 18, 2954024449215840⟩, ⟨.privateRow 8 12, 30583355362560⟩, ⟨.privateRow 8 13, 270436151585600⟩, ⟨.privateRow 8 14, 448396590341700⟩, ⟨.privateRow 8 15, 742283520778800⟩, ⟨.privateRow 8 16, 980154062487600⟩, ⟨.privateRow 8 17, 1229705746869600⟩, ⟨.privateRow 9 9, 2623572151200⟩, ⟨.privateRow 9 10, 72505993996800⟩, ⟨.privateRow 9 11, 131778281194560⟩, ⟨.privateRow 9 12, 216548812480000⟩, ⟨.privateRow 9 13, 271727115660000⟩, ⟨.privateRow 9 14, 397926290361600⟩, ⟨.privateRow 9 15, 383541262104000⟩, ⟨.privateRow 9 16, 146020530015360⟩, ⟨.privateRow 10 7, 17190163683000⟩, ⟨.privateRow 10 8, 40126599062550⟩, ⟨.privateRow 10 9, 68076586468800⟩, ⟨.privateRow 10 10, 90147813095340⟩, ⟨.privateRow 10 11, 113844291561000⟩, ⟨.privateRow 10 12, 66936226982625⟩, ⟨.privateRow 11 4, 3448123398720⟩, ⟨.privateRow 11 5, 11806074680400⟩, ⟨.privateRow 11 6, 17255032225200⟩, ⟨.privateRow 11 7, 46708954191900⟩, ⟨.privateRow 12 2, 5631979503150⟩, ⟨.privateRow 12 3, 8009926404480⟩, ⟨.privateRow 13 0, 2878200864000⟩, ⟨.privateRow 14 0, 1546033589100⟩, ⟨.privateRow 15 0, 1761541301520⟩, ⟨.privateRow 16 0, 2650343295600⟩, ⟨.privateRow 17 0, 4843517817600⟩, ⟨.privateRow 18 0, 10353740096700⟩, ⟨.privateRow 19 0, 26065359684000⟩, ⟨.privateRow 20 0, 83011964555520⟩, ⟨.privateRow 21 0, 334353746126400⟩, ⟨.privateRow 22 0, 1770489556535700⟩, ⟨.privateRow 23 0, 13126266895341600⟩, ⟨.privateRow 24 0, 153139780445652000⟩, ⟨.privateRow 25 0, 3748861825309560960⟩, ⟨.hall 15 8, 468027000⟩, ⟨.hall 14 10, 823727520⟩, ⟨.hall 18 10, 5213071936800⟩, ⟨.hall 7 15, 160146522900⟩, ⟨.hall 6 16, 350821411200⟩, ⟨.hall 6 17, 350776062000⟩, ⟨.hall 8 20, 480595584268800⟩, ⟨.hall 5 21, 340414676784000⟩, ⟨.hall 4 23, 4532453264731392⟩]
  caps := #[0, 0, 0, 2976167592871200, 0, 0, 129706194618000, 37708503758640, 1562884596000, 0, 0, 2190663455400, 1917364176000, 0, 1732690896300, 0, 5226551114400, 1037896675200, 3982207729500, 0, 20752991138880, 149882713780800, 1225723539140100, 13126266895341600, 214395692623912800, 0] }

theorem case_54_29_13_checked :
    (Witness.linear .positive case_54_29_13).check 54 29 13 = true := by
  change case_54_29_13.check 54 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_29_14 : Certificate := {
  objectiveScale := 703248000000
  eta := 2620311725648897280
  rows := #[⟨.count 2, 740475879566623200⟩, ⟨.count 3, 148612169545519680⟩, ⟨.count 4, 27661295659757760⟩, ⟨.count 5, 5407985337955200⟩, ⟨.count 6, 1106012351283840⟩, ⟨.count 7, 250963416063360⟩, ⟨.count 8, 59967363456000⟩, ⟨.count 9, 15080028163200⟩, ⟨.count 10, 4563692733600⟩, ⟨.count 11, 1600599480480⟩, ⟨.count 12, 685971205920⟩, ⟨.count 13, 685971205920⟩, ⟨.path 15, 173288042928⟩, ⟨.path 16, 16025615424⟩, ⟨.privateRow 4 25, 288405538621200⟩, ⟨.privateRow 6 19, 11475183335616⟩, ⟨.privateRow 7 17, 19516164267600⟩, ⟨.privateRow 7 18, 33847293287808⟩, ⟨.privateRow 8 14, 3391903995480⟩, ⟨.privateRow 8 15, 7115770181520⟩, ⟨.privateRow 8 16, 16378586143920⟩, ⟨.privateRow 8 17, 20583797506272⟩, ⟨.privateRow 9 11, 440936496000⟩, ⟨.privateRow 9 12, 1879369331840⟩, ⟨.privateRow 9 13, 3628907362080⟩, ⟨.privateRow 9 14, 5938784691840⟩, ⟨.privateRow 9 15, 8895158912640⟩, ⟨.privateRow 9 16, 9386656126848⟩, ⟨.privateRow 10 9, 451859695560⟩, ⟨.privateRow 10 10, 901825368444⟩, ⟨.privateRow 10 11, 1591780750560⟩, ⟨.privateRow 10 12, 2612962116765⟩, ⟨.privateRow 10 13, 3213009759960⟩, ⟨.privateRow 10 14, 3821265908460⟩, ⟨.privateRow 10 15, 662727553488⟩, ⟨.privateRow 11 6, 54947471040⟩, ⟨.privateRow 11 7, 235349854740⟩, ⟨.privateRow 11 8, 485831848320⟩, ⟨.privateRow 11 9, 696459195432⟩, ⟨.privateRow 11 10, 1116304229040⟩, ⟨.privateRow 11 11, 808567299540⟩, ⟨.privateRow 12 4, 61618625640⟩, ⟨.privateRow 12 5, 97938779400⟩, ⟨.privateRow 12 6, 304876091520⟩, ⟨.privateRow 12 7, 266924057400⟩, ⟨.privateRow 13 2, 55005616512⟩, ⟨.privateRow 13 3, 79150523760⟩, ⟨.privateRow 14 0, 25983757800⟩, ⟨.privateRow 15 0, 11464348896⟩, ⟨.privateRow 16 0, 14172958800⟩, ⟨.privateRow 17 0, 25777825920⟩, ⟨.privateRow 18 0, 53096103060⟩, ⟨.privateRow 19 0, 140183447040⟩, ⟨.privateRow 20 0, 457786569240⟩, ⟨.privateRow 21 0, 1763326044480⟩, ⟨.privateRow 22 0, 9613517954040⟩, ⟨.privateRow 23 0, 67142030155200⟩, ⟨.privateRow 24 0, 810740014124040⟩, ⟨.privateRow 25 0, 20754944361575424⟩, ⟨.hall 8 14, 466722256⟩, ⟨.hall 7 15, 5126112810⟩, ⟨.hall 8 15, 2978255280⟩, ⟨.hall 6 18, 63256692096⟩, ⟨.hall 6 19, 173653877592⟩, ⟨.hall 9 19, 2603289072384⟩, ⟨.hall 5 22, 60728595127200⟩, ⟨.hall 4 23, 57040206527304⟩]
  caps := #[0, 0, 543079435298400, 33147868746720, 1649102495040, 287246266944, 0, 375447840768, 0, 124551516544, 91378004445, 0, 17533974744, 17276794080, 0, 1322809488, 69882858864, 0, 228000913140, 692155769760, 0, 9630473012160, 0, 396137977915680, 5675180098868280, 0] }

theorem case_54_29_14_checked :
    (Witness.linear .positive case_54_29_14).check 54 29 14 = true := by
  change case_54_29_14.check 54 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_29_15 : Certificate := {
  objectiveScale := 499557240000000
  eta := 2049745333308962889600
  rows := #[⟨.count 2, 560215944826284146400⟩, ⟨.count 3, 116696507650381058400⟩, ⟨.count 4, 26968096925151782400⟩, ⟨.count 5, 5996057964800904000⟩, ⟨.count 6, 1497328310670192000⟩, ⟨.count 7, 371243704907275200⟩, ⟨.count 8, 96745347463564800⟩, ⟨.count 9, 27889321559299200⟩, ⟨.count 10, 8441343396486000⟩, ⟨.count 11, 2733387385528800⟩, ⟨.count 12, 1033633885284000⟩, ⟨.count 13, 482362479799200⟩, ⟨.count 14, 482362479799200⟩, ⟨.path 16, 28546698922560⟩, ⟨.path 17, 76122480994560⟩, ⟨.privateRow 4 25, 2252062715913410400⟩, ⟨.privateRow 7 17, 13400697896586000⟩, ⟨.privateRow 7 18, 52012457107490880⟩, ⟨.privateRow 8 15, 8300741346097200⟩, ⟨.privateRow 8 16, 22412396062656600⟩, ⟨.privateRow 8 17, 41340413458103760⟩, ⟨.privateRow 9 12, 333485171219200⟩, ⟨.privateRow 9 13, 3625027120915200⟩, ⟨.privateRow 9 14, 9616623406790400⟩, ⟨.privateRow 9 15, 16611459405340800⟩, ⟨.privateRow 9 16, 23052054186120960⟩, ⟨.privateRow 10 10, 385889983839360⟩, ⟨.privateRow 10 11, 1501901357556600⟩, ⟨.privateRow 10 12, 3915084104506575⟩, ⟨.privateRow 10 13, 6878363672980800⟩, ⟨.privateRow 10 14, 9466363666059300⟩, ⟨.privateRow 10 15, 10739142845711280⟩, ⟨.privateRow 11 8, 243174473287200⟩, ⟨.privateRow 11 9, 720620310730320⟩, ⟨.privateRow 11 10, 1620867861412800⟩, ⟨.privateRow 11 11, 2913359750150850⟩, ⟨.privateRow 11 12, 1964948456671200⟩, ⟨.privateRow 11 13, 8234268594552000⟩, ⟨.privateRow 11 17, 10630245861635400⟩, ⟨.privateRow 12 6, 132553975103550⟩, ⟨.privateRow 12 7, 354985374744000⟩, ⟨.privateRow 12 8, 752830013115180⟩, ⟨.privateRow 12 10, 4409453442569175⟩, ⟨.privateRow 13 4, 72578631787200⟩, ⟨.privateRow 13 5, 180665067983400⟩, ⟨.privateRow 13 6, 373939344979200⟩, ⟨.privateRow 13 7, 3180411954720⟩, ⟨.privateRow 13 8, 1273931677418400⟩, ⟨.privateRow 13 12, 122975928915840⟩, ⟨.privateRow 14 3, 9276201534600⟩, ⟨.privateRow 14 4, 507724792725150⟩, ⟨.privateRow 14 5, 158177306687400⟩, ⟨.privateRow 14 7, 13398957772200⟩, ⟨.privateRow 15 0, 44338369355280⟩, ⟨.privateRow 15 3, 537176397958200⟩, ⟨.privateRow 16 0, 2349167921100⟩, ⟨.privateRow 16 1, 128180239387200⟩, ⟨.privateRow 16 3, 142516187213400⟩, ⟨.privateRow 16 4, 359579303123040⟩, ⟨.privateRow 17 0, 5996736345600⟩, ⟨.privateRow 17 1, 376794933715200⟩, ⟨.privateRow 17 3, 461898617019840⟩, ⟨.privateRow 17 7, 272851503724800⟩, ⟨.privateRow 18 0, 576358198716300⟩, ⟨.privateRow 18 1, 188249819940000⟩, ⟨.privateRow 18 2, 579809445415200⟩, ⟨.privateRow 18 5, 567976599590400⟩, ⟨.privateRow 18 9, 662639366188800⟩, ⟨.privateRow 18 11, 2899047227076000⟩, ⟨.privateRow 19 0, 2681753149202400⟩, ⟨.privateRow 19 2, 579809445415200⟩, ⟨.privateRow 19 7, 3194868372696000⟩, ⟨.privateRow 20 0, 9611229021193800⟩, ⟨.privateRow 20 7, 4271657342752800⟩, ⟨.privateRow 21 0, 41967159858624000⟩, ⟨.privateRow 21 7, 30351249540612000⟩, ⟨.privateRow 22 0, 210688257227748300⟩, ⟨.privateRow 23 0, 1580288392747864800⟩, ⟨.privateRow 24 0, 18514599455879326800⟩, ⟨.privateRow 25 0, 452950717010931659520⟩, ⟨.hall 19 2, 187353392226000⟩, ⟨.hall 19 5, 93141400706640⟩, ⟨.hall 21 5, 7250576279146200⟩, ⟨.hall 22 5, 70482346155421200⟩, ⟨.hall 23 5, 1194490287476085600⟩, ⟨.hall 20 6, 374706784452000⟩, ⟨.hall 17 9, 21585979353120⟩, ⟨.hall 18 10, 1897558184995200⟩, ⟨.hall 9 11, 897885948960⟩, ⟨.hall 16 12, 2145332427638400⟩, ⟨.hall 15 13, 1652248104507000⟩, ⟨.hall 8 14, 8622876021760⟩, ⟨.hall 13 15, 1748563989272100⟩, ⟨.hall 7 16, 39032072352000⟩, ⟨.hall 9 18, 1524173117987520⟩, ⟨.hall 10 18, 1754045381088000⟩, ⟨.hall 6 20, 2808333196718400⟩, ⟨.hall 7 21, 52894434406741200⟩, ⟨.hall 5 22, 129005029247094000⟩, ⟨.hall 6 22, 1114022820094984800⟩, ⟨.hall 4 24, 3147788792355951744⟩]
  caps := #[0, 0, 0, 4962265253618400, 0, 0, 1606900463007840, 350560919348640, 289378818448720, 71016761204480, 0, 14223620032440, 129121205084235, 18810453450600, 25580078252820, 59063318561520, 0, 371361800409600, 0, 0, 2079622653708600, 0, 139868674966320300, 0, 0, 0] }

theorem case_54_29_15_checked :
    (Witness.linear .positive case_54_29_15).check 54 29 15 = true := by
  change case_54_29_15.check 54 29 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_29_16 : Certificate := {
  objectiveScale := 41772931200000
  eta := 145544047335547660800
  rows := #[⟨.count 2, 35834708624282568000⟩, ⟨.count 3, 8826843779860906800⟩, ⟨.count 4, 2167079217199696800⟩, ⟨.count 5, 587569061619540000⟩, ⟨.count 6, 162495920617430400⟩, ⟨.count 7, 46018392522102000⟩, ⟨.count 8, 13533134747932800⟩, ⟨.count 9, 4148991959112000⟩, ⟨.count 10, 1366131498732000⟩, ⟨.count 11, 491638681333800⟩, ⟨.count 12, 198775747170000⟩, ⟨.count 13, 95412358641600⟩, ⟨.count 14, 64933410742200⟩, ⟨.count 15, 63246828645000⟩, ⟨.path 15, 6962060261520⟩, ⟨.privateRow 3 26, 341568292907041200⟩, ⟨.privateRow 6 19, 2926171750582080⟩, ⟨.privateRow 7 17, 1781753515542000⟩, ⟨.privateRow 7 18, 8832582254976480⟩, ⟨.privateRow 8 15, 829436981373000⟩, ⟨.privateRow 8 16, 3368947739157000⟩, ⟨.privateRow 8 17, 7273104197158800⟩, ⟨.privateRow 9 13, 351090173233800⟩, ⟨.privateRow 9 14, 1307502692496000⟩, ⟨.privateRow 9 15, 2769742599624000⟩, ⟨.privateRow 9 16, 4355429607809280⟩, ⟨.privateRow 10 11, 143640575278200⟩, ⟨.privateRow 10 12, 521470102178025⟩, ⟨.privateRow 10 13, 1111337131905000⟩, ⟨.privateRow 10 14, 1797053224566600⟩, ⟨.privateRow 10 15, 2323182509788140⟩, ⟨.privateRow 11 9, 58440069667980⟩, ⟨.privateRow 11 10, 213352635295800⟩, ⟨.privateRow 11 11, 461596437727425⟩, ⟨.privateRow 11 12, 762455578084200⟩, ⟨.privateRow 11 13, 1030501661389200⟩, ⟨.privateRow 11 14, 1138611573819720⟩, ⟨.privateRow 12 7, 24395205334500⟩, ⟨.privateRow 12 8, 90707999291910⟩, ⟨.privateRow 12 9, 200174539464900⟩, ⟨.privateRow 12 10, 339243941836800⟩, ⟨.privateRow 12 11, 474222139677000⟩, ⟨.privateRow 12 12, 151179998819850⟩, ⟨.privateRow 13 5, 10703309463000⟩, ⟨.privateRow 13 6, 40755978370800⟩, ⟨.privateRow 13 7, 91559167234920⟩, ⟨.privateRow 13 8, 160719535746000⟩, ⟨.privateRow 13 9, 38684818487700⟩, ⟨.privateRow 14 3, 5198750310600⟩, ⟨.privateRow 14 4, 20043221172975⟩, ⟨.privateRow 14 5, 44694425575800⟩, ⟨.privateRow 14 6, 10601373182400⟩, ⟨.privateRow 15 1, 3192458969700⟩, ⟨.privateRow 15 2, 11546600511600⟩, ⟨.privateRow 15 3, 1335210826950⟩, ⟨.privateRow 16 0, 3885162331050⟩, ⟨.privateRow 17 0, 3286672804800⟩, ⟨.privateRow 18 0, 6371532367200⟩, ⟨.privateRow 19 0, 14522128966800⟩, ⟨.privateRow 19 3, 3071988819900⟩, ⟨.privateRow 20 0, 54476601739560⟩, ⟨.privateRow 21 0, 207529911388800⟩, ⟨.privateRow 22 0, 1123579910878425⟩, ⟨.privateRow 23 0, 7704547960309200⟩, ⟨.privateRow 24 0, 91883868267391200⟩, ⟨.privateRow 25 0, 2315473480338258240⟩, ⟨.hall 20 5, 1544121364500⟩, ⟨.hall 9 13, 495605990880⟩, ⟨.hall 8 14, 707509682880⟩, ⟨.hall 9 14, 816747831900⟩, ⟨.hall 8 15, 2783024844600⟩, ⟨.hall 7 17, 15534039797640⟩, ⟨.hall 7 18, 53855344670400⟩, ⟨.hall 10 18, 2675007973638000⟩, ⟨.hall 6 22, 327590476647033600⟩, ⟨.hall 5 23, 552969934205188500⟩, ⟨.hall 4 24, 714253620727719072⟩, ⟨.hall 3 25, 656170667953000200⟩, ⟨.assumptionRow 16, 59356292515520⟩]
  caps := #[0, 0, 0, 2634743722716560, 1476329100719200, 139687072164640, 0, 32555295572800, 0, 23504578035120, 0, 1618371624870, 534593222800, 7371316001840, 3430985778675, 3071524132040, 14460672856630, 0, 22300363285200, 83222969848200, 256818265343640, 0, 0, 31674252725715600, 459419341336956000, 0] }

theorem case_54_29_16_checked :
    (Witness.linear .conditional case_54_29_16).check 54 29 16 = true := by
  change case_54_29_16.check 54 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_29_17 : Certificate := {
  objectiveScale := 32133024000000
  eta := 62848565894895580800
  rows := #[⟨.count 2, 16630980156397807200⟩, ⟨.count 3, 4470349938748293600⟩, ⟨.count 4, 1266036224427374400⟩, ⟨.count 5, 365771468822760000⟩, ⟨.count 6, 108019318877870400⟩, ⟨.count 7, 32685961043736000⟩, ⟨.count 8, 10168965658051200⟩, ⟨.count 9, 3265222940179200⟩, ⟨.count 10, 1155308736582000⟩, ⟨.count 11, 432889404948000⟩, ⟨.count 12, 174922657509600⟩, ⟨.count 13, 74209612276800⟩, ⟨.count 14, 37104806138400⟩, ⟨.count 15, 33731641944000⟩, ⟨.count 16, 26985313555200⟩, ⟨.count 18, 57343791304800⟩, ⟨.path 14, 3442684518000⟩, ⟨.privateRow 3 26, 523338554044706400⟩, ⟨.privateRow 6 19, 965014087957920⟩, ⟨.privateRow 7 17, 360446688201600⟩, ⟨.privateRow 7 18, 6234089311850400⟩, ⟨.privateRow 8 15, 109226269152000⟩, ⟨.privateRow 8 16, 2098357992931200⟩, ⟨.privateRow 8 17, 5950374077728080⟩, ⟨.privateRow 9 13, 24174343393200⟩, ⟨.privateRow 9 14, 709542411177600⟩, ⟨.privateRow 9 15, 2122594802328000⟩, ⟨.privateRow 9 16, 4071184305027840⟩, ⟨.privateRow 10 12, 241075828518525⟩, ⟨.privateRow 10 13, 781971742351800⟩, ⟨.privateRow 10 14, 1583560040762700⟩, ⟨.privateRow 10 15, 2400343640735040⟩, ⟨.privateRow 11 10, 76895650431600⟩, ⟨.privateRow 11 11, 296346529328850⟩, ⟨.privateRow 11 12, 643712167098000⟩, ⟨.privateRow 11 13, 1055331897820200⟩, ⟨.privateRow 11 14, 1366356376344960⟩, ⟨.privateRow 12 8, 25840847132100⟩, ⟨.privateRow 12 9, 111167177121000⟩, ⟨.privateRow 12 10, 267298164458325⟩, ⟨.privateRow 12 11, 468669039438600⟩, ⟨.privateRow 12 12, 661923238076100⟩, ⟨.privateRow 12 13, 717801309225000⟩, ⟨.privateRow 13 6, 8525579832000⟩, ⟨.privateRow 13 7, 44077247731440⟩, ⟨.privateRow 13 8, 112673568823200⟩, ⟨.privateRow 13 9, 214677806943600⟩, ⟨.privateRow 13 10, 326487344436000⟩, ⟨.privateRow 13 11, 22358024211600⟩, ⟨.privateRow 14 4, 2503102001400⟩, ⟨.privateRow 14 5, 18431932919400⟩, ⟨.privateRow 14 6, 50621556945960⟩, ⟨.privateRow 14 7, 102136377743400⟩, ⟨.privateRow 14 8, 33239722165650⟩, ⟨.privateRow 15 2, 43245694800⟩, ⟨.privateRow 15 3, 8479759988700⟩, ⟨.privateRow 15 4, 24378777586800⟩, ⟨.privateRow 15 5, 18158867246520⟩, ⟨.privateRow 16 1, 3308295652200⟩, ⟨.privateRow 16 2, 6957151150950⟩, ⟨.privateRow 17 0, 1614505939200⟩, ⟨.hall 10 12, 630969223500⟩, ⟨.hall 9 13, 1228074447600⟩, ⟨.hall 9 14, 379553494320⟩, ⟨.hall 8 15, 4345535994800⟩, ⟨.hall 8 16, 4409630184960⟩, ⟨.hall 11 17, 565504730590800⟩, ⟨.hall 7 18, 27262798388280⟩, ⟨.hall 7 19, 682912423720800⟩, ⟨.hall 5 21, 2028560452191000⟩, ⟨.hall 6 22, 324125629430803200⟩, ⟨.hall 4 24, 660082087957900608⟩, ⟨.hall 3 25, 654096366579070800⟩, ⟨.assumptionRow 17, 31559449521600⟩]
  caps := #[0, 100453659471547200, 7808802097824000, 0, 1316423661537600, 263541735293760, 21616259464800, 15838459837200, 37452887450160, 0, 15247675919385, 1975621043550, 176212486800, 13523922103680, 0, 7173879776280, 4574135966400, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_29_17_checked :
    (Witness.linear .conditional case_54_29_17).check 54 29 17 = true := by
  change case_54_29_17.check 54 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_29_18 : Certificate := {
  objectiveScale := 16735950000000
  eta := 27565160480217360000
  rows := #[⟨.count 2, 7534477197926078400⟩, ⟨.count 3, 2085364314590356800⟩, ⟨.count 4, 585441880027804800⟩, ⟨.count 5, 166542753889512000⟩, ⟨.count 6, 47991292008660000⟩, ⟨.count 7, 14680010574028800⟩, ⟨.count 8, 4612989433852800⟩, ⟨.count 9, 1484192245536000⟩, ⟨.count 10, 486297838026000⟩, ⟨.count 11, 158726115147600⟩, ⟨.count 12, 61841343564000⟩, ⟨.count 13, 26503432956000⟩, ⟨.count 14, 14429646831600⟩, ⟨.count 15, 11243880648000⟩, ⟨.count 16, 8995104518400⟩, ⟨.count 17, 8495376489600⟩, ⟨.path 13, 2448977731200⟩, ⟨.privateRow 3 26, 98542119591115200⟩, ⟨.privateRow 6 19, 242118229953600⟩, ⟨.privateRow 7 18, 2844798180063840⟩, ⟨.privateRow 8 16, 815202168981200⟩, ⟨.privateRow 8 17, 2910728369749200⟩, ⟨.privateRow 9 14, 231302687616000⟩, ⟨.privateRow 9 15, 959311239286400⟩, ⟨.privateRow 9 16, 2233684343130240⟩, ⟨.privateRow 10 12, 61700795055900⟩, ⟨.privateRow 10 13, 315792419342400⟩, ⟨.privateRow 10 14, 803094175283400⟩, ⟨.privateRow 10 15, 1467551302176960⟩, ⟨.privateRow 11 10, 14179782817200⟩, ⟨.privateRow 11 11, 102670685167050⟩, ⟨.privateRow 11 12, 296195941641600⟩, ⟨.privateRow 11 13, 592958539173000⟩, ⟨.privateRow 11 14, 910604414079360⟩, ⟨.privateRow 12 8, 1796343789240⟩, ⟨.privateRow 12 9, 32049521704200⟩, ⟨.privateRow 12 10, 109713169340775⟩, ⟨.privateRow 12 11, 243810548724600⟩, ⟨.privateRow 12 12, 415195909428300⟩, ⟨.privateRow 12 13, 561519399561120⟩, ⟨.privateRow 13 7, 8059761919440⟩, ⟨.privateRow 13 8, 40351665446400⟩, ⟨.privateRow 13 9, 101630471758200⟩, ⟨.privateRow 13 10, 190067476341600⟩, ⟨.privateRow 13 11, 284492832901200⟩, ⟨.privateRow 13 12, 220182366096000⟩, ⟨.privateRow 14 5, 1258243786800⟩, ⟨.privateRow 14 6, 13693440360600⟩, ⟨.privateRow 14 7, 42896297043600⟩, ⟨.privateRow 14 8, 89927620432650⟩, ⟨.privateRow 14 9, 124061307598800⟩, ⟨.privateRow 15 4, 3935358226800⟩, ⟨.privateRow 15 5, 17596673214120⟩, ⟨.privateRow 15 6, 43538804509200⟩, ⟨.privateRow 15 7, 17217192242250⟩, ⟨.privateRow 16 2, 632468286450⟩, ⟨.privateRow 16 3, 7052979679200⟩, ⟨.privateRow 16 4, 14082960511620⟩, ⟨.privateRow 17 1, 2706860156000⟩, ⟨.privateRow 17 2, 2044341936000⟩, ⟨.privateRow 18 0, 796441545900⟩, ⟨.hall 10 12, 43234537500⟩, ⟨.hall 11 12, 212533813800⟩, ⟨.hall 10 13, 1345187844000⟩, ⟨.hall 11 13, 886671675890⟩, ⟨.hall 9 14, 1390864555080⟩, ⟨.hall 9 15, 3528246201480⟩, ⟨.hall 8 17, 53739111506080⟩, ⟨.hall 8 18, 246983376640⟩, ⟨.hall 7 21, 113697098941608000⟩, ⟨.hall 6 22, 192019306272393600⟩, ⟨.hall 5 23, 291961438185417000⟩, ⟨.hall 4 24, 373753069214773248⟩, ⟨.hall 3 25, 391044221974098000⟩, ⟨.hall 2 26, 197380161463284800⟩, ⟨.assumptionRow 18, 10358080286400⟩]
  caps := #[0, 0, 0, 0, 0, 0, 1730119960800, 5173581853440, 0, 0, 0, 0, 2497421082585, 641915920800, 0, 1215988753980, 4032136139850, 1862703796800, 0, 16735950000000, 0, 0, 0, 0, 0, 0] }

theorem case_54_29_18_checked :
    (Witness.linear .conditional case_54_29_18).check 54 29 18 = true := by
  change case_54_29_18.check 54 29 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_30_1_checked :
    (Witness.rising).check 54 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_30_2_checked :
    (Witness.rising).check 54 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_30_3_checked :
    (Witness.rising).check 54 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_30_4_checked :
    (Witness.rising).check 54 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_30_5_checked :
    (Witness.rising).check 54 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_30_6_checked :
    (Witness.rising).check 54 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_30_7_checked :
    (Witness.rising).check 54 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_30_8_checked :
    (Witness.rising).check 54 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_30_9_checked :
    (Witness.rising).check 54 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_30_10_checked :
    (Witness.rising).check 54 30 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_30_11_checked :
    (Witness.linear .positive case_54_30_11).check 54 30 11 = true := by
  change case_54_30_11.check 54 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_30_12 : Certificate := {
  objectiveScale := 17089090200000
  eta := 42266579402999952000
  rows := #[⟨.count 2, 9188386826739120000⟩, ⟨.count 3, 1332497678549637600⟩, ⟨.count 4, 191135048389084800⟩, ⟨.count 5, 30247484584917600⟩, ⟨.count 6, 5193709098177600⟩, ⟨.count 7, 993959049283200⟩, ⟨.count 8, 212884140268800⟩, ⟨.count 9, 55657209207600⟩, ⟨.count 10, 21363373231200⟩, ⟨.count 11, 16785507538800⟩, ⟨.path 12, 4263710016384⟩, ⟨.path 13, 2768953332600⟩, ⟨.privateRow 4 26, 6848487075830400⟩, ⟨.privateRow 5 21, 26978888480544⟩, ⟨.privateRow 5 22, 1312626689534160⟩, ⟨.privateRow 6 18, 186854939013600⟩, ⟨.privateRow 6 19, 327223698001200⟩, ⟨.privateRow 6 20, 413421428740320⟩, ⟨.privateRow 6 21, 732498667500600⟩, ⟨.privateRow 7 14, 14199414989760⟩, ⟨.privateRow 7 15, 59669906296000⟩, ⟨.privateRow 7 16, 99441415873800⟩, ⟨.privateRow 7 17, 142514274988800⟩, ⟨.privateRow 7 18, 171121155004800⟩, ⟨.privateRow 7 19, 202432685495040⟩, ⟨.privateRow 7 20, 215949436302600⟩, ⟨.privateRow 8 11, 7839483451800⟩, ⟨.privateRow 8 12, 18773873445600⟩, ⟨.privateRow 8 13, 31220508599280⟩, ⟨.privateRow 8 14, 43143186486400⟩, ⟨.privateRow 8 15, 51862399488900⟩, ⟨.privateRow 8 16, 57290249016000⟩, ⟨.privateRow 8 17, 62091207578400⟩, ⟨.privateRow 9 8, 2864512450800⟩, ⟨.privateRow 9 9, 6659836999200⟩, ⟨.privateRow 9 10, 10384973098500⟩, ⟨.privateRow 9 11, 14003742261600⟩, ⟨.privateRow 9 12, 16978259778480⟩, ⟨.privateRow 9 13, 8391266483600⟩, ⟨.privateRow 10 5, 1004921832915⟩, ⟨.privateRow 10 7, 8697944815560⟩, ⟨.privateRow 10 8, 1357914816720⟩, ⟨.privateRow 11 2, 107084577600⟩, ⟨.privateRow 11 3, 1634614581600⟩, ⟨.privateRow 12 0, 325480755600⟩, ⟨.privateRow 13 0, 154792129800⟩, ⟨.privateRow 14 0, 170075505600⟩, ⟨.privateRow 15 0, 238932463770⟩, ⟨.privateRow 16 0, 387289222320⟩, ⟨.privateRow 17 0, 803134332000⟩, ⟨.privateRow 18 0, 1890454658400⟩, ⟨.privateRow 19 0, 5688868185000⟩, ⟨.privateRow 20 0, 21696308917920⟩, ⟨.privateRow 21 0, 98576707909680⟩, ⟨.privateRow 21 3, 22235347648800⟩, ⟨.privateRow 22 0, 766707728186400⟩, ⟨.hall 5 21, 401935401504⟩, ⟨.hall 5 22, 9165904419672⟩, ⟨.hall 6 23, 474451606629000⟩, ⟨.hall 4 25, 9003605386406400⟩]
  caps := #[0, 2092787729028360, 0, 0, 26199554013360, 7138038452688, 25521237912456, 0, 3689572197220, 824657619240, 744918590115, 1047444148296, 0, 209220064200, 0, 0, 2810970162000, 0, 0, 0, 204699958051680, 0, 0, 0, 0] }

theorem case_54_30_12_checked :
    (Witness.linear .positive case_54_30_12).check 54 30 12 = true := by
  change case_54_30_12.check 54 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_30_13 : Certificate := {
  objectiveScale := 85208760000000
  eta := 316356158444627901600
  rows := #[⟨.count 2, 73563023925032241600⟩, ⟨.count 3, 11793094744579948800⟩, ⟨.count 4, 1951818816611664000⟩, ⟨.count 5, 338429402997285600⟩, ⟨.count 6, 62717723747078400⟩, ⟨.count 7, 12755807799134400⟩, ⟨.count 8, 2836456291468800⟩, ⟨.count 9, 742096122768000⟩, ⟨.count 10, 222628836830400⟩, ⟨.count 11, 97179254172000⟩, ⟨.count 12, 80733534235200⟩, ⟨.path 13, 9731219097600⟩, ⟨.path 14, 18940737816000⟩, ⟨.privateRow 5 22, 9102780738291240⟩, ⟨.privateRow 6 19, 3143896113758400⟩, ⟨.privateRow 6 20, 5400692878220640⟩, ⟨.privateRow 6 21, 9018676511044200⟩, ⟨.privateRow 7 16, 863570190483000⟩, ⟨.privateRow 7 17, 1447508128809600⟩, ⟨.privateRow 7 18, 2352915881316000⟩, ⟨.privateRow 7 19, 3380188942690560⟩, ⟨.privateRow 7 20, 3689572350063600⟩, ⟨.privateRow 8 12, 5621940324000⟩, ⟨.privateRow 8 13, 212734221860160⟩, ⟨.privateRow 8 14, 408610951548800⟩, ⟨.privateRow 8 15, 677678056555500⟩, ⟨.privateRow 8 16, 859889158128000⟩, ⟨.privateRow 8 17, 1237513997319600⟩, ⟨.privateRow 8 18, 1262387959953120⟩, ⟨.privateRow 8 19, 934834976875800⟩, ⟨.privateRow 9 10, 54798301658100⟩, ⟨.privateRow 9 11, 118810338847200⟩, ⟨.privateRow 9 12, 199129126276080⟩, ⟨.privateRow 9 13, 270498617589200⟩, ⟨.privateRow 9 14, 341415750926250⟩, ⟨.privateRow 9 15, 423760444707600⟩, ⟨.privateRow 9 16, 103412468959800⟩, ⟨.privateRow 10 7, 12633303042360⟩, ⟨.privateRow 10 8, 36343681909920⟩, ⟨.privateRow 10 9, 48648523603680⟩, ⟨.privateRow 10 10, 99171027315360⟩, ⟨.privateRow 10 11, 140750897951664⟩, ⟨.privateRow 11 4, 2595127810275⟩, ⟨.privateRow 11 5, 11897096571360⟩, ⟨.privateRow 11 6, 21328953188400⟩, ⟨.privateRow 11 7, 29357648812800⟩, ⟨.privateRow 12 2, 4793003938800⟩, ⟨.privateRow 12 3, 5840099409375⟩, ⟨.privateRow 13 0, 2034950194200⟩, ⟨.privateRow 14 0, 1091317827600⟩, ⟨.privateRow 15 0, 1468731909645⟩, ⟨.privateRow 16 0, 2473653742560⟩, ⟨.privateRow 17 0, 4711721414400⟩, ⟨.privateRow 18 0, 11552778468000⟩, ⟨.privateRow 19 0, 35043428019600⟩, ⟨.privateRow 20 0, 134894442402720⟩, ⟨.privateRow 21 0, 399495079423440⟩, ⟨.privateRow 21 1, 317059586844000⟩, ⟨.privateRow 22 0, 4882717637397600⟩, ⟨.privateRow 23 0, 54930573420723000⟩, ⟨.privateRow 24 0, 1155111486790060800⟩, ⟨.hall 6 18, 552335355000⟩, ⟨.hall 5 21, 9733603996116⟩, ⟨.hall 5 22, 162031234076712⟩, ⟨.hall 7 22, 1279846936368000⟩, ⟨.hall 4 24, 5629807580798016⟩, ⟨.hall 3 26, 82562316414177600⟩]
  caps := #[0, 51086367289994400, 33092580654806400, 0, 0, 308900291182560, 0, 0, 86237622330860, 0, 16639669186056, 0, 4475225764800, 0, 8391332149200, 2009843665830, 0, 5300686591200, 16173889855200, 60074448033600, 280165380374880, 2346240942645600, 14648152912192800, 0, 0] }

theorem case_54_30_13_checked :
    (Witness.linear .positive case_54_30_13).check 54 30 13 = true := by
  change case_54_30_13.check 54 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_30_14 : Certificate := {
  objectiveScale := 54701920000000
  eta := 283094198131832287200
  rows := #[⟨.count 2, 69176567952962870400⟩, ⟨.count 3, 12563393893177327200⟩, ⟨.count 4, 2360652742047600000⟩, ⟨.count 5, 459315576381261600⟩, ⟨.count 6, 96698016080265600⟩, ⟨.count 7, 21370119559588800⟩, ⟨.count 8, 4911327067046400⟩, ⟨.count 9, 1249757334025200⟩, ⟨.count 10, 365426121060000⟩, ⟨.count 11, 126333030423600⟩, ⟨.count 12, 53006865912000⟩, ⟨.count 13, 57424104738000⟩, ⟨.path 15, 14918625376200⟩, ⟨.privateRow 7 17, 1342182797841600⟩, ⟨.privateRow 7 18, 2678167438346400⟩, ⟨.privateRow 7 19, 3923771675503680⟩, ⟨.privateRow 7 20, 4904714594379600⟩, ⟨.privateRow 8 14, 208969604043200⟩, ⟨.privateRow 8 15, 664466496794100⟩, ⟨.privateRow 8 16, 1273075000797600⟩, ⟨.privateRow 8 18, 6757947065469600⟩, ⟨.privateRow 8 19, 638277624784800⟩, ⟨.privateRow 9 13, 689166595717600⟩, ⟨.privateRow 9 14, 315484551181800⟩, ⟨.privateRow 9 15, 867974043736800⟩, ⟨.privateRow 9 16, 311424260947800⟩, ⟨.privateRow 9 17, 2351395280314080⟩, ⟨.privateRow 9 18, 1084097492478000⟩, ⟨.privateRow 10 9, 27894193907580⟩, ⟨.privateRow 10 10, 49697952464160⟩, ⟨.privateRow 10 11, 110358688560120⟩, ⟨.privateRow 10 12, 393523329479280⟩, ⟨.privateRow 10 13, 71075380546170⟩, ⟨.privateRow 10 14, 770735893047120⟩, ⟨.privateRow 10 16, 703079856919440⟩, ⟨.privateRow 11 7, 26905000122000⟩, ⟨.privateRow 11 8, 32888350895400⟩, ⟨.privateRow 11 10, 181460170972080⟩, ⟨.privateRow 11 11, 210903075583200⟩, ⟨.privateRow 11 12, 37717196066550⟩, ⟨.privateRow 11 13, 370199033661600⟩, ⟨.privateRow 11 15, 167887200761280⟩, ⟨.privateRow 12 5, 14324474478600⟩, ⟨.privateRow 12 6, 30444969139200⟩, ⟨.privateRow 12 7, 21129125717700⟩, ⟨.privateRow 12 9, 136934403606000⟩, ⟨.privateRow 12 11, 302359997639700⟩, ⟨.privateRow 12 14, 125802961764480⟩, ⟨.privateRow 13 2, 3312929119500⟩, ⟨.privateRow 13 3, 5418479626560⟩, ⟨.privateRow 13 4, 14829301773000⟩, ⟨.privateRow 13 5, 22901684374800⟩, ⟨.privateRow 13 7, 21443686664400⟩, ⟨.privateRow 13 8, 91613533251240⟩, ⟨.privateRow 13 10, 187180495251750⟩, ⟨.privateRow 13 13, 69262304791680⟩, ⟨.privateRow 14 1, 14682299506875⟩, ⟨.privateRow 14 3, 14244161045400⟩, ⟨.privateRow 14 5, 44721196720200⟩, ⟨.privateRow 14 7, 62853292822320⟩, ⟨.privateRow 14 9, 246401613057600⟩, ⟨.privateRow 15 1, 14909385739248⟩, ⟨.privateRow 15 2, 5429188084320⟩, ⟨.privateRow 15 5, 111886834157280⟩, ⟨.privateRow 15 6, 9647249595984⟩, ⟨.privateRow 15 8, 240450387657480⟩, ⟨.privateRow 15 10, 171263042070120⟩, ⟨.privateRow 16 1, 8526609491400⟩, ⟨.privateRow 16 4, 136204281486000⟩, ⟨.privateRow 16 5, 46287308667600⟩, ⟨.privateRow 16 8, 426678499447200⟩, ⟨.privateRow 17 1, 172031373914400⟩, ⟨.privateRow 17 3, 130224581323200⟩, ⟨.privateRow 17 5, 182442374514400⟩, ⟨.privateRow 17 6, 88311312589500⟩, ⟨.privateRow 17 7, 285380399304000⟩, ⟨.privateRow 17 8, 451504274020800⟩, ⟨.privateRow 17 9, 35080907621760⟩, ⟨.privateRow 17 10, 40196873316600⟩, ⟨.privateRow 17 11, 30858205778400⟩, ⟨.privateRow 18 0, 319486837269600⟩, ⟨.privateRow 18 1, 73955286405000⟩, ⟨.privateRow 18 2, 204385518792000⟩, ⟨.privateRow 18 3, 93479482015920⟩, ⟨.privateRow 18 4, 234027395201600⟩, ⟨.privateRow 18 7, 2141745094288800⟩, ⟨.privateRow 18 8, 137261011567680⟩, ⟨.privateRow 19 0, 1538269957224000⟩, ⟨.privateRow 19 6, 3366444637155600⟩, ⟨.privateRow 19 7, 2790185045487840⟩, ⟨.privateRow 19 11, 1029457586757600⟩, ⟨.privateRow 20 0, 7161668578471680⟩, ⟨.privateRow 20 3, 741919433214960⟩, ⟨.privateRow 20 5, 4608893448759600⟩, ⟨.privateRow 21 0, 23673974641677360⟩, ⟨.privateRow 21 1, 20908638572421600⟩, ⟨.privateRow 21 5, 13354549797869280⟩, ⟨.privateRow 21 7, 674472212013600⟩, ⟨.privateRow 21 8, 1348944424027200⟩, ⟨.privateRow 22 0, 299540603490928800⟩, ⟨.privateRow 22 4, 33993399485485440⟩, ⟨.privateRow 22 5, 66098276777332800⟩, ⟨.privateRow 23 0, 3492585731859424200⟩, ⟨.privateRow 24 6, 593661672875614543200⟩, ⟨.hall 14 1, 15804679735845⟩, ⟨.hall 15 1, 49535540854800⟩, ⟨.hall 18 2, 155440565607600⟩, ⟨.hall 20 2, 314753698939680⟩, ⟨.hall 12 4, 215087772900⟩, ⟨.hall 22 4, 34128293927888160⟩, ⟨.hall 15 5, 426715816800⟩, ⟨.hall 13 6, 62850323250⟩, ⟨.hall 19 6, 12847089752640⟩, ⟨.hall 16 7, 267711444000⟩, ⟨.hall 18 7, 2796854467680⟩, ⟨.hall 21 7, 1770489556535700⟩, ⟨.hall 20 8, 59953085512320⟩, ⟨.hall 14 9, 44537449320⟩, ⟨.hall 17 9, 4894495318440⟩, ⟨.hall 20 9, 1618733308832640⟩, ⟨.hall 9 10, 8708345100⟩, ⟨.hall 16 11, 4676026555200⟩, ⟨.hall 15 12, 2907346281840⟩, ⟨.hall 7 17, 555361242800⟩, ⟨.hall 6 18, 1509128290800⟩, ⟨.hall 9 19, 4280705989560⟩, ⟨.hall 10 19, 246297205594440⟩, ⟨.hall 5 21, 113060737199592⟩, ⟨.hall 8 21, 3697669404374400⟩, ⟨.hall 7 22, 4271142871195200⟩, ⟨.hall 4 25, 287325162317793600⟩, ⟨.hall 3 26, 182557145385014400⟩]
  caps := #[0, 496722429173224800, 0, 0, 474280415918400, 63750301342000, 13031775156400, 0, 27922333218780, 29579424514640, 0, 2024763426660, 1695054088000, 7252558514360, 2148629243930, 2274881587524, 0, 114913541884960, 0, 23665691649600, 376069354577280, 9442610968190400, 0, 389507702437854000, 0] }

theorem case_54_30_14_checked :
    (Witness.linear .positive case_54_30_14).check 54 30 14 = true := by
  change case_54_30_14.check 54 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_30_15 : Certificate := {
  objectiveScale := 33786480000000
  eta := 197090897433554124000
  rows := #[⟨.count 2, 45182893482791064000⟩, ⟨.count 3, 10042216764670490400⟩, ⟨.count 4, 2382235852832035200⟩, ⟨.count 5, 567231130303437600⟩, ⟨.count 6, 131415585730228800⟩, ⟨.count 7, 33794607675628800⟩, ⟨.count 8, 8692269332947200⟩, ⟨.count 9, 2236407860887200⟩, ⟨.count 10, 657767017908000⟩, ⟨.count 11, 206726777056800⟩, ⟨.count 12, 74209612276800⟩, ⟨.count 13, 34454462842800⟩, ⟨.count 14, 29234089684800⟩, ⟨.path 16, 6757329786480⟩, ⟨.privateRow 3 27, 514622297766376800⟩, ⟨.privateRow 8 15, 283814287356600⟩, ⟨.privateRow 8 16, 1418549399467200⟩, ⟨.privateRow 8 17, 2664362451550800⟩, ⟨.privateRow 8 18, 4441632692777280⟩, ⟨.privateRow 8 19, 6648319229151600⟩, ⟨.privateRow 8 20, 8624056457016000⟩, ⟨.privateRow 9 13, 198683535450400⟩, ⟨.privateRow 9 14, 588031533139050⟩, ⟨.privateRow 9 16, 5201231789754000⟩, ⟨.privateRow 9 17, 1899728594683920⟩, ⟨.privateRow 9 18, 4418610847150500⟩, ⟨.privateRow 9 19, 5045316644768400⟩, ⟨.privateRow 10 11, 102465484345224⟩, ⟨.privateRow 10 13, 1088969840758800⟩, ⟨.privateRow 10 14, 132179848360560⟩, ⟨.privateRow 10 15, 2626926575593320⟩, ⟨.privateRow 11 8, 6786485105400⟩, ⟨.privateRow 11 9, 41098574134800⟩, ⟨.privateRow 11 11, 306725925105600⟩, ⟨.privateRow 11 12, 614959958012400⟩, ⟨.privateRow 11 13, 276530623855200⟩, ⟨.privateRow 11 14, 1301613040728000⟩, ⟨.privateRow 11 15, 366470195691600⟩, ⟨.privateRow 12 6, 6252091876800⟩, ⟨.privateRow 12 7, 20319298599600⟩, ⟨.privateRow 12 8, 46662104689200⟩, ⟨.privateRow 12 9, 22881297118680⟩, ⟨.privateRow 12 10, 238923540055200⟩, ⟨.privateRow 12 11, 430570354564350⟩, ⟨.privateRow 12 13, 1234618251867000⟩, ⟨.privateRow 12 14, 287297213243040⟩, ⟨.privateRow 13 4, 4417238826000⟩, ⟨.privateRow 13 5, 11416863427200⟩, ⟨.privateRow 13 6, 22527918012600⟩, ⟨.privateRow 13 7, 48429000219600⟩, ⟨.privateRow 13 8, 24118123989960⟩, ⟨.privateRow 13 9, 185033226378000⟩, ⟨.privateRow 13 11, 765949212428400⟩, ⟨.privateRow 13 13, 855884194925760⟩, ⟨.privateRow 14 3, 2759340097800⟩, ⟨.privateRow 14 4, 30760044915600⟩, ⟨.privateRow 14 5, 14530038623100⟩, ⟨.privateRow 14 6, 48407096556000⟩, ⟨.privateRow 14 7, 25684235937360⟩, ⟨.privateRow 14 8, 154523045476800⟩, ⟨.privateRow 14 9, 48679979698350⟩, ⟨.privateRow 14 10, 484898089618800⟩, ⟨.privateRow 14 11, 345066665743800⟩, ⟨.privateRow 14 12, 385263539060400⟩, ⟨.privateRow 14 13, 537959453931900⟩, ⟨.privateRow 15 2, 2401371652680⟩, ⟨.privateRow 15 3, 39353582268000⟩, ⟨.privateRow 15 4, 16809601568760⟩, ⟨.privateRow 15 5, 53950183691040⟩, ⟨.privateRow 15 6, 34788566724912⟩, ⟨.privateRow 15 7, 20788685998080⟩, ⟨.privateRow 15 8, 350809076217600⟩, ⟨.privateRow 15 9, 237840201078480⟩, ⟨.privateRow 15 10, 497223142055640⟩, ⟨.privateRow 16 0, 8282992077360⟩, ⟨.privateRow 16 2, 8995104518400⟩, ⟨.privateRow 16 3, 122214736043400⟩, ⟨.privateRow 16 4, 21925567263600⟩, ⟨.privateRow 16 5, 56519240057280⟩, ⟨.privateRow 16 6, 36271926090400⟩, ⟨.privateRow 16 8, 1065304149109200⟩, ⟨.privateRow 16 9, 193269815138400⟩, ⟨.privateRow 16 12, 680504643218400⟩, ⟨.privateRow 17 0, 30278164316400⟩, ⟨.privateRow 17 2, 185555263693800⟩, ⟨.privateRow 17 4, 233872717478400⟩, ⟨.privateRow 17 7, 986302501984800⟩, ⟨.privateRow 17 8, 337004089422000⟩, ⟨.privateRow 18 0, 130161304072800⟩, ⟨.privateRow 18 1, 257364396689400⟩, ⟨.privateRow 18 2, 106495612423200⟩, ⟨.privateRow 18 3, 311203845192240⟩, ⟨.privateRow 18 5, 468876515807700⟩, ⟨.privateRow 18 6, 740398067323200⟩, ⟨.privateRow 18 7, 1557991366932000⟩, ⟨.privateRow 19 0, 1162577102286600⟩, ⟨.privateRow 19 1, 129085590816000⟩, ⟨.privateRow 19 3, 1613211314114400⟩, ⟨.privateRow 19 5, 1567006868512800⟩, ⟨.privateRow 19 7, 6254842302989280⟩, ⟨.privateRow 20 1, 9078395973703056⟩, ⟨.privateRow 20 5, 13287102576667920⟩, ⟨.privateRow 20 8, 24415894074892320⟩, ⟨.privateRow 21 0, 22729713544858320⟩, ⟨.privateRow 21 1, 20458990431079200⟩, ⟨.privateRow 21 9, 585441880027804800⟩, ⟨.privateRow 22 1, 324589752031545000⟩, ⟨.privateRow 22 4, 2832783290457120⟩, ⟨.privateRow 23 0, 1298359008126180000⟩, ⟨.privateRow 23 1, 2107051190330486400⟩, ⟨.hall 14 1, 3197478559275⟩, ⟨.hall 23 2, 24174208198920780000⟩, ⟨.hall 22 7, 194753851218927000⟩, ⟨.hall 21 8, 58229434303840800⟩, ⟨.hall 18 11, 2147661517201200⟩, ⟨.hall 17 12, 13482162488995200⟩, ⟨.hall 16 13, 9318714111907200⟩, ⟨.hall 8 14, 247708559280⟩, ⟨.hall 11 14, 436952596080⟩, ⟨.hall 15 14, 3668878255442400⟩, ⟨.hall 14 15, 3566558941545600⟩, ⟨.hall 7 16, 451387372800⟩, ⟨.hall 12 16, 6755777028000⟩, ⟨.hall 12 17, 13742324470274400⟩, ⟨.hall 10 18, 1766162141944200⟩, ⟨.hall 11 18, 18450062620189200⟩, ⟨.hall 9 19, 3103303027504680⟩, ⟨.hall 8 21, 55206363665980800⟩, ⟨.hall 7 22, 139445972272807200⟩, ⟨.hall 6 23, 419370847088193000⟩, ⟨.hall 5 24, 643230659153130048⟩, ⟨.hall 4 25, 843712854751166400⟩, ⟨.hall 3 26, 809441595773210400⟩]
  caps := #[0, 0, 25120055972793600, 3772526391597600, 1873892493345600, 252262553743200, 1785306563040, 144952361353800, 4414102252560, 17290523956160, 10511781907536, 6623146646610, 4028241562170, 1295769438390, 20352494353230, 0, 11170106755080, 75869423229600, 0, 519200687060640, 1241028870105024, 0, 0, 0, 0] }

theorem case_54_30_15_checked :
    (Witness.linear .positive case_54_30_15).check 54 30 15 = true := by
  change case_54_30_15.check 54 30 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_30_16 : Certificate := {
  objectiveScale := 10970668800000
  eta := 66294210954922750800
  rows := #[⟨.count 2, 14957095773613593600⟩, ⟨.count 3, 3718028068724970000⟩, ⟨.count 4, 922677986034604800⟩, ⟨.count 5, 227634371554590000⟩, ⟨.count 6, 59744038569415200⟩, ⟨.count 7, 16607399115106800⟩, ⟨.count 8, 4755411922060800⟩, ⟨.count 9, 1414199088502200⟩, ⟨.count 10, 445819867693200⟩, ⟨.count 11, 155045082792600⟩, ⟨.count 12, 58307552503200⟩, ⟨.count 13, 28712052369000⟩, ⟨.count 14, 14617044842400⟩, ⟨.count 15, 10962783631800⟩, ⟨.path 14, 2547017928000⟩, ⟨.privateRow 3 27, 377704438727616000⟩, ⟨.privateRow 5 22, 14518014363592740⟩, ⟨.privateRow 6 20, 6528181041542160⟩, ⟨.privateRow 6 21, 17261163846927000⟩, ⟨.privateRow 7 17, 211300818300000⟩, ⟨.privateRow 7 18, 2440524451365000⟩, ⟨.privateRow 7 19, 6511615057387440⟩, ⟨.privateRow 7 20, 11479339555784100⟩, ⟨.privateRow 8 15, 185453756437950⟩, ⟨.privateRow 8 16, 917741601176400⟩, ⟨.privateRow 8 17, 2415872689230000⟩, ⟨.privateRow 8 18, 4285230312963600⟩, ⟨.privateRow 8 19, 5990552211243600⟩, ⟨.privateRow 9 13, 100830540811000⟩, ⟨.privateRow 9 14, 371821078178550⟩, ⟨.privateRow 9 15, 918611663369400⟩, ⟨.privateRow 9 16, 1646041660863600⟩, ⟨.privateRow 9 17, 2349446341001760⟩, ⟨.privateRow 9 18, 2674005640856550⟩, ⟨.privateRow 9 19, 13398957772200⟩, ⟨.privateRow 10 11, 47213054840952⟩, ⟨.privateRow 10 12, 155590321766880⟩, ⟨.privateRow 10 13, 371638365118020⟩, ⟨.privateRow 10 14, 658080240297480⟩, ⟨.privateRow 10 15, 961679741922900⟩, ⟨.privateRow 10 16, 1161616553625528⟩, ⟨.privateRow 10 17, 1109433703538160⟩, ⟨.privateRow 11 9, 21023866445400⟩, ⟨.privateRow 11 10, 66977387617140⟩, ⟨.privateRow 11 11, 158699344003200⟩, ⟨.privateRow 11 12, 281834895867525⟩, ⟨.privateRow 11 13, 415690856895600⟩, ⟨.privateRow 11 14, 479230255904400⟩, ⟨.privateRow 12 7, 9313011858150⟩, ⟨.privateRow 12 8, 29876597150400⟩, ⟨.privateRow 12 9, 71559268981200⟩, ⟨.privateRow 12 10, 129964982347200⟩, ⟨.privateRow 12 11, 168020721843975⟩, ⟨.privateRow 13 5, 4281323785200⟩, ⟨.privateRow 13 6, 14024733272550⟩, ⟨.privateRow 13 7, 34253679259800⟩, ⟨.privateRow 13 8, 53360245018080⟩, ⟨.privateRow 14 3, 2162726022600⟩, ⟨.privateRow 14 4, 7107738838200⟩, ⟨.privateRow 14 5, 14399529294150⟩, ⟨.privateRow 15 1, 1315534035816⟩, ⟨.privateRow 15 2, 3080020163220⟩, ⟨.privateRow 16 0, 974469656160⟩, ⟨.privateRow 17 0, 870062193000⟩, ⟨.privateRow 18 0, 1365328364400⟩, ⟨.privateRow 18 4, 657380323600⟩, ⟨.privateRow 19 0, 4437317184300⟩, ⟨.privateRow 20 0, 18394696691280⟩, ⟨.privateRow 21 0, 101170831802040⟩, ⟨.privateRow 22 0, 786884247349200⟩, ⟨.privateRow 23 0, 6491795040630900⟩, ⟨.privateRow 24 0, 170641469639440800⟩, ⟨.hall 8 16, 665423304000⟩, ⟨.hall 7 18, 3663579039120⟩, ⟨.hall 7 19, 11286804421620⟩, ⟨.hall 9 20, 689089256856000⟩, ⟨.hall 6 22, 719231237524800⟩, ⟨.hall 6 23, 90827445445436700⟩, ⟨.hall 5 24, 220862670545973456⟩, ⟨.hall 4 25, 380402327575670400⟩, ⟨.hall 3 26, 458753516204583600⟩, ⟨.assumptionRow 16, 15517876865400⟩]
  caps := #[0, 197463652009369200, 0, 0, 3859912274400, 142636551548400, 39858972799464, 134792520831540, 0, 722588466600, 19335601892880, 0, 5853625425375, 0, 3469795486560, 9438902285904, 5292110514600, 0, 0, 79871709317400, 349499237134320, 2023416636040800, 0, 142819490893879800, 0] }

theorem case_54_30_16_checked :
    (Witness.linear .conditional case_54_30_16).check 54 30 16 = true := by
  change case_54_30_16.check 54 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_30_17 : Certificate := {
  objectiveScale := 310810500000
  eta := 765698902228260000
  rows := #[⟨.count 2, 199747539711720000⟩, ⟨.count 3, 53750247049699200⟩, ⟨.count 4, 14665447071475200⟩, ⟨.count 5, 4107362829570000⟩, ⟨.count 6, 1196027647214400⟩, ⟨.count 7, 357867734624400⟩, ⟨.count 8, 109440438307200⟩, ⟨.count 9, 35980418073600⟩, ⟨.count 10, 12368268712800⟩, ⟨.count 11, 4564480120200⟩, ⟨.count 12, 1766895530400⟩, ⟨.count 13, 736206471000⟩, ⟨.count 14, 374796021600⟩, ⟨.count 15, 281097016200⟩, ⟨.count 16, 499728028800⟩, ⟨.path 13, 16110767400⟩, ⟨.path 14, 19729819200⟩, ⟨.privateRow 2 28, 15313978044565200⟩, ⟨.privateRow 5 22, 603566158955760⟩, ⟨.privateRow 6 20, 199428963093360⟩, ⟨.privateRow 6 21, 579354335960400⟩, ⟨.privateRow 7 17, 823531394400⟩, ⟨.privateRow 7 18, 64853097309000⟩, ⟨.privateRow 7 19, 200217819481680⟩, ⟨.privateRow 7 20, 395717670948600⟩, ⟨.privateRow 8 15, 312330018000⟩, ⟨.privateRow 8 16, 21613237245600⟩, ⟨.privateRow 8 17, 69920280029600⟩, ⟨.privateRow 8 18, 143584355874960⟩, ⟨.privateRow 8 19, 234185047496400⟩, ⟨.privateRow 9 14, 7281193544625⟩, ⟨.privateRow 9 15, 25013172584400⟩, ⟨.privateRow 9 16, 53491721082800⟩, ⟨.privateRow 9 17, 89220192941880⟩, ⟨.privateRow 9 18, 122909670333450⟩, ⟨.privateRow 10 12, 2369543736560⟩, ⟨.privateRow 10 13, 9154392827580⟩, ⟨.privateRow 10 14, 20624489645760⟩, ⟨.privateRow 10 15, 35561895849480⟩, ⟨.privateRow 10 16, 50455040427792⟩, ⟨.privateRow 10 17, 58444754618250⟩, ⟨.privateRow 11 10, 789748759800⟩, ⟨.privateRow 11 11, 3368702337000⟩, ⟨.privateRow 11 12, 8243839278675⟩, ⟨.privateRow 11 13, 14909615206200⟩, ⟨.privateRow 11 14, 21983571409800⟩, ⟨.privateRow 11 15, 26803269773280⟩, ⟨.privateRow 11 16, 12482046076500⟩, ⟨.privateRow 12 8, 262563147000⟩, ⟨.privateRow 12 9, 1283264510220⟩, ⟨.privateRow 12 10, 3380257403600⟩, ⟨.privateRow 12 11, 6590463697125⟩, ⟨.privateRow 12 12, 10300418449200⟩, ⟨.privateRow 12 13, 6627745947900⟩, ⟨.privateRow 13 6, 84946900500⟩, ⟨.privateRow 13 7, 505562765400⟩, ⟨.privateRow 13 8, 1452025685880⟩, ⟨.privateRow 13 9, 3045503692000⟩, ⟨.privateRow 13 10, 3522464807400⟩, ⟨.privateRow 14 4, 22652506800⟩, ⟨.privateRow 14 5, 208591833450⟩, ⟨.privateRow 14 6, 655893037800⟩, ⟨.privateRow 14 7, 1452334583700⟩, ⟨.privateRow 15 3, 92257482240⟩, ⟨.privateRow 15 4, 317014968270⟩, ⟨.privateRow 15 5, 151622026920⟩, ⟨.privateRow 16 1, 33463930500⟩, ⟨.privateRow 16 2, 76881235200⟩, ⟨.privateRow 17 0, 26771144400⟩, ⟨.privateRow 18 0, 23338946400⟩, ⟨.privateRow 19 0, 75851575800⟩, ⟨.privateRow 20 0, 314439259680⟩, ⟨.privateRow 21 0, 864707964120⟩, ⟨.privateRow 22 0, 6725506387600⟩, ⟨.privateRow 23 0, 83228141546550⟩, ⟨.privateRow 24 0, 2187711149223600⟩, ⟨.hall 8 18, 93745972320⟩, ⟨.hall 9 18, 585865360080⟩, ⟨.hall 8 19, 3109346735040⟩, ⟨.hall 9 19, 4191691934430⟩, ⟨.hall 7 21, 13788197514000⟩, ⟨.hall 7 22, 1714957958313600⟩, ⟨.hall 6 23, 4370529871808100⟩, ⟨.hall 5 24, 8337168306859392⟩, ⟨.hall 3 25, 787660267317000⟩, ⟨.hall 4 25, 14175889331788800⟩, ⟨.hall 2 27, 20402784413411400⟩, ⟨.assumptionRow 17, 329108812032⟩]
  caps := #[0, 0, 563873800024080, 0, 18713029935600, 0, 2068874039232, 408030485148, 83094844560, 0, 28460361930, 216370178622, 42359247756, 35339509296, 84560054670, 48011795832, 320594219484, 0, 707572588800, 1365328364400, 0, 17294159282400, 141235634139600, 1831019114024100, 0] }

theorem case_54_30_17_checked :
    (Witness.linear .conditional case_54_30_17).check 54 30 17 = true := by
  change case_54_30_17.check 54 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_30_18 : Certificate := {
  objectiveScale := 4668111226548000000
  eta := 9771021041850645543766800
  rows := #[⟨.count 2, 2507175748443501351216000⟩, ⟨.count 3, 660982697316923083502400⟩, ⟨.count 4, 179083982031678667944000⟩, ⟨.count 5, 49112425375354301360400⟩, ⟨.count 6, 14052522991959474422400⟩, ⟨.count 7, 4154189836602292687200⟩, ⟨.count 8, 1270170657809823369600⟩, ⟨.count 9, 399868540421611060800⟩, ⟨.count 10, 129369233665815343200⟩, ⟨.count 11, 46203297737791194000⟩, ⟨.count 12, 21324598955903628000⟩, ⟨.count 13, 9240659547558238800⟩, ⟨.count 14, 5880419712082515600⟩, ⟨.count 15, 2940209856041257800⟩, ⟨.count 16, 5227039744073347200⟩, ⟨.path 11, 167612331125131200⟩, ⟨.path 12, 728162644189551480⟩, ⟨.privateRow 2 28, 299468214397418216950800⟩, ⟨.privateRow 5 21, 65121448011519515616⟩, ⟨.privateRow 5 22, 8823051741005178817140⟩, ⟨.privateRow 6 20, 2670550609244331013200⟩, ⟨.privateRow 6 21, 8486495719483656174300⟩, ⟨.privateRow 7 18, 776464308649371742400⟩, ⟨.privateRow 7 19, 2773373948209888143120⟩, ⟨.privateRow 7 20, 6076177017497833946700⟩, ⟨.privateRow 8 16, 219535669251080582400⟩, ⟨.privateRow 8 17, 901010975884643223600⟩, ⟨.privateRow 8 18, 2120348672183353291680⟩, ⟨.privateRow 8 19, 3878136800118419038200⟩, ⟨.privateRow 9 14, 58681688376823436925⟩, ⟨.privateRow 9 15, 291314125736659225200⟩, ⟨.privateRow 9 16, 750189099935860184600⟩, ⟨.privateRow 9 17, 1438873365549790650480⟩, ⟨.privateRow 9 18, 2272700546223891133350⟩, ⟨.privateRow 10 12, 13938772650862259200⟩, ⟨.privateRow 10 13, 92788122706902027405⟩, ⟨.privateRow 10 14, 268819186838057856000⟩, ⟨.privateRow 10 15, 550962658023731253300⟩, ⟨.privateRow 10 16, 907387964372412707184⟩, ⟨.privateRow 10 17, 1225430464500395563410⟩, ⟨.privateRow 11 10, 2296163887575077520⟩, ⟨.privateRow 11 11, 28562038601543647200⟩, ⟨.privateRow 11 12, 96974421501932199225⟩, ⟨.privateRow 11 13, 217515525064276725000⟩, ⟨.privateRow 11 14, 380197136384763597900⟩, ⟨.privateRow 11 15, 545702949281257447680⟩, ⟨.privateRow 11 16, 626999751800798225850⟩, ⟨.privateRow 12 9, 7795325618324770680⟩, ⟨.privateRow 12 10, 34856504960020251200⟩, ⟨.privateRow 12 11, 88097249436576863175⟩, ⟨.privateRow 12 12, 167076540391016361600⟩, ⟨.privateRow 12 13, 257099632411871426100⟩, ⟨.privateRow 12 14, 282574630164562963920⟩, ⟨.privateRow 13 7, 1421639930393575200⟩, ⟨.privateRow 13 8, 11941775415306031680⟩, ⟨.privateRow 13 9, 36264981557724997000⟩, ⟨.privateRow 13 10, 76620468748503730050⟩, ⟨.privateRow 13 11, 129030747968102587200⟩, ⟨.privateRow 13 12, 32243583421287615300⟩, ⟨.privateRow 14 5, 128342493716086650⟩, ⟨.privateRow 14 6, 3538434372205496400⟩, ⟨.privateRow 14 7, 14687048280891806820⟩, ⟨.privateRow 14 8, 36231474892698885800⟩, ⟨.privateRow 14 9, 38485246865682892275⟩, ⟨.privateRow 15 4, 865728457612148130⟩, ⟨.privateRow 15 5, 5541850092295946520⟩, ⟨.privateRow 15 6, 17112021362160120396⟩, ⟨.privateRow 15 7, 3593589824050426200⟩, ⟨.privateRow 16 2, 125649993847917000⟩, ⟨.privateRow 16 3, 2069036565362366600⟩, ⟨.privateRow 16 4, 4692456133884027600⟩, ⟨.privateRow 17 1, 804159960626668800⟩, ⟨.privateRow 17 2, 598931637341737700⟩, ⟨.privateRow 18 0, 244119988047381600⟩, ⟨.hall 9 17, 1595008579799825190⟩, ⟨.hall 9 18, 25548139275426167400⟩, ⟨.hall 8 19, 20690931350565665280⟩, ⟨.hall 10 19, 1195293313475972670960⟩, ⟨.hall 8 20, 662793165124036419200⟩, ⟨.hall 7 22, 40475582258231964043200⟩, ⟨.hall 6 23, 79294169582593819553700⟩, ⟨.hall 4 24, 9232217591171574406176⟩, ⟨.hall 5 24, 141407606498791765964832⟩, ⟨.hall 3 26, 332179682495797232896800⟩, ⟨.hall 2 27, 344239209905337883936800⟩, ⟨.assumptionRow 18, 3449967601980299400⟩]
  caps := #[0, 3493466543343910114800, 4009537981611569206800, 0, 0, 0, 0, 0, 2742327480144566160, 4470337472943748840, 437885853308240400, 77220169298271720, 796063352017874905, 63686057032175160, 1360385225798210885, 509757745939041600, 0, 6790597665454341200, 0, 4668111226548000000, 0, 0, 0, 0, 0] }

theorem case_54_30_18_checked :
    (Witness.linear .conditional case_54_30_18).check 54 30 18 = true := by
  change case_54_30_18.check 54 30 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_30_19 : Certificate := {
  objectiveScale := 510510000000
  eta := 1378258024010868000
  rows := #[⟨.count 2, 350224019627882400⟩, ⟨.count 3, 89886392870274000⟩, ⟨.count 4, 23347115031240000⟩, ⟨.count 5, 6191309023099200⟩, ⟨.count 6, 1643855350737600⟩, ⟨.count 7, 444945343642800⟩, ⟨.count 8, 121433910998400⟩, ⟨.count 9, 32888350895400⟩, ⟨.count 10, 8620308496800⟩, ⟨.count 11, 2061378118800⟩, ⟨.count 12, 679575204000⟩, ⟨.count 13, 294482588400⟩, ⟨.count 14, 187398010800⟩, ⟨.count 15, 281097016200⟩, ⟨.path 12, 125775703872⟩, ⟨.path 13, 19889933700⟩, ⟨.privateRow 2 28, 37286207412854400⟩, ⟨.privateRow 5 22, 1095584990540040⟩, ⟨.privateRow 6 19, 1972140970800⟩, ⟨.privateRow 6 20, 322035450216480⟩, ⟨.privateRow 6 21, 1060177474956600⟩, ⟨.privateRow 7 18, 93954818557600⟩, ⟨.privateRow 7 19, 335931458903040⟩, ⟨.privateRow 7 20, 771258822734400⟩, ⟨.privateRow 8 16, 26057247216000⟩, ⟨.privateRow 8 17, 106129740116400⟩, ⟨.privateRow 8 18, 260770578628560⟩, ⟨.privateRow 8 19, 507395730741900⟩, ⟨.privateRow 9 14, 6902493397800⟩, ⟨.privateRow 9 15, 32852656036200⟩, ⟨.privateRow 9 16, 88977616627900⟩, ⟨.privateRow 9 17, 182681827528200⟩, ⟨.privateRow 9 18, 312665772769350⟩, ⟨.privateRow 10 12, 1665760096000⟩, ⟨.privateRow 10 13, 9903984870780⟩, ⟨.privateRow 10 14, 30326352376320⟩, ⟨.privateRow 10 15, 67350845081520⟩, ⟨.privateRow 10 16, 121089098658528⟩, ⟨.privateRow 10 17, 180333105792840⟩, ⟨.privateRow 11 10, 325269404460⟩, ⟨.privateRow 11 11, 2825843020000⟩, ⟨.privateRow 11 12, 10246655519100⟩, ⟨.privateRow 11 13, 25271960313600⟩, ⟨.privateRow 11 14, 48812719956000⟩, ⟨.privateRow 11 15, 77855842144080⟩, ⟨.privateRow 11 16, 101047684537800⟩, ⟨.privateRow 11 17, 9896399713200⟩, ⟨.privateRow 12 8, 23682166200⟩, ⟨.privateRow 12 9, 712421338860⟩, ⟨.privateRow 12 10, 3358863369400⟩, ⟨.privateRow 12 11, 9574931468025⟩, ⟨.privateRow 12 12, 20366221649400⟩, ⟨.privateRow 12 13, 35054754273000⟩, ⟨.privateRow 12 14, 49876289472240⟩, ⟨.privateRow 12 15, 47485317379500⟩, ⟨.privateRow 13 7, 101936280600⟩, ⟨.privateRow 13 8, 1015964929980⟩, ⟨.privateRow 13 9, 3595456218200⟩, ⟨.privateRow 13 10, 8729709808050⟩, ⟨.privateRow 13 11, 16581634977600⟩, ⟨.privateRow 13 12, 25954109666100⟩, ⟨.privateRow 13 13, 5087753027280⟩, ⟨.privateRow 14 6, 211735414800⟩, ⟨.privateRow 14 7, 1282337816760⟩, ⟨.privateRow 14 8, 3776218646200⟩, ⟨.privateRow 14 9, 8168545435050⟩, ⟨.privateRow 14 10, 8551468411200⟩, ⟨.privateRow 15 4, 6246600360⟩, ⟨.privateRow 15 5, 356056220520⟩, ⟨.privateRow 15 6, 1579765231044⟩, ⟨.privateRow 15 7, 4112345237000⟩, ⟨.privateRow 15 8, 1351608152895⟩, ⟨.privateRow 16 3, 31233001800⟩, ⟨.privateRow 16 4, 550836577200⟩, ⟨.privateRow 16 5, 1692828697560⟩, ⟨.privateRow 17 2, 93699005400⟩, ⟨.privateRow 17 3, 528121666800⟩, ⟨.privateRow 18 1, 139061222300⟩, ⟨.privateRow 19 0, 37925787900⟩, ⟨.hall 9 17, 273394441320⟩, ⟨.hall 10 17, 2091131662620⟩, ⟨.hall 9 18, 4929976691640⟩, ⟨.hall 8 20, 139790803588800⟩, ⟨.hall 7 22, 5994042159705600⟩, ⟨.hall 6 23, 11138348796775200⟩, ⟨.hall 5 24, 19176801461882064⟩, ⟨.hall 4 25, 30574743291338400⟩, ⟨.hall 3 26, 43238280565880400⟩, ⟨.hall 2 27, 44277371302764600⟩, ⟨.assumptionRow 19, 148914251640⟩]
  caps := #[0, 2302616509027380, 0, 9135653026500, 14350741820520, 5958192762060, 0, 0, 73465452060, 0, 136007011140, 33635417256, 11284149347, 0, 0, 169147844866, 337999105080, 263578278600, 986956723060, 0, 510510000000, 0, 0, 0, 0] }

theorem case_54_30_19_checked :
    (Witness.linear .conditional case_54_30_19).check 54 30 19 = true := by
  change case_54_30_19.check 54 30 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_31_1_checked :
    (Witness.rising).check 54 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_31_2_checked :
    (Witness.rising).check 54 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_31_3_checked :
    (Witness.rising).check 54 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_31_4_checked :
    (Witness.rising).check 54 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_31_5_checked :
    (Witness.rising).check 54 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_31_6_checked :
    (Witness.rising).check 54 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_31_7_checked :
    (Witness.rising).check 54 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_31_8_checked :
    (Witness.rising).check 54 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_31_9_checked :
    (Witness.rising).check 54 31 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_31_10_checked :
    (Witness.rising).check 54 31 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_31_11_checked :
    (Witness.linear .positive case_54_31_11).check 54 31 11 = true := by
  change case_54_31_11.check 54 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_31_12_checked :
    (Witness.linear .positive case_54_31_12).check 54 31 12 = true := by
  change case_54_31_12.check 54 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_31_13 : Certificate := {
  objectiveScale := 7195406400000
  eta := 33078192576260832000
  rows := #[⟨.count 2, 6415164620850585600⟩, ⟨.count 3, 988672497856243200⟩, ⟨.count 4, 164612725713596160⟩, ⟨.count 5, 28704663533145600⟩, ⟨.count 6, 5330241934617600⟩, ⟨.count 7, 1088407646726400⟩, ⟨.count 8, 242867821996800⟩, ⟨.count 9, 62066221176960⟩, ⟨.count 10, 19275223968000⟩, ⟨.count 11, 8154902448000⟩, ⟨.count 12, 6523921958400⟩, ⟨.path 13, 856051773696⟩, ⟨.path 14, 1572749208576⟩, ⟨.privateRow 4 25, 1390450406304960⟩, ⟨.privateRow 5 22, 930607813175040⟩, ⟨.privateRow 5 23, 2175787281507840⟩, ⟨.privateRow 5 24, 3202514211536640⟩, ⟨.privateRow 6 19, 295951176892800⟩, ⟨.privateRow 6 20, 556447160068800⟩, ⟨.privateRow 6 21, 835216871448960⟩, ⟨.privateRow 6 22, 1300702821818400⟩, ⟨.privateRow 6 23, 1368969240038400⟩, ⟨.privateRow 7 16, 79099807987200⟩, ⟨.privateRow 7 17, 152434896213600⟩, ⟨.privateRow 7 18, 240114218572800⟩, ⟨.privateRow 7 19, 313329474057600⟩, ⟨.privateRow 7 20, 430994007924480⟩, ⟨.privateRow 7 21, 451040240851200⟩, ⟨.privateRow 7 22, 352950767769600⟩, ⟨.privateRow 8 12, 374796021600⟩, ⟨.privateRow 8 13, 19319031295200⟩, ⟨.privateRow 8 14, 43007843478600⟩, ⟨.privateRow 8 15, 70024390035600⟩, ⟨.privateRow 8 16, 94167500427000⟩, ⟨.privateRow 8 17, 114928522909200⟩, ⟨.privateRow 8 18, 146451545440200⟩, ⟨.privateRow 8 19, 116149287093840⟩, ⟨.privateRow 9 10, 4889646558720⟩, ⟨.privateRow 9 11, 12318295909920⟩, ⟨.privateRow 9 12, 21206640349440⟩, ⟨.privateRow 9 13, 30223551181824⟩, ⟨.privateRow 9 14, 38112590996480⟩, ⟨.privateRow 9 15, 40440490730640⟩, ⟨.privateRow 10 7, 1117962990144⟩, ⟨.privateRow 10 8, 3731132639520⟩, ⟨.privateRow 10 9, 6835290960960⟩, ⟨.privateRow 10 10, 10296182136240⟩, ⟨.privateRow 10 11, 9988070601600⟩, ⟨.privateRow 11 4, 226767340800⟩, ⟨.privateRow 11 5, 1186167628800⟩, ⟨.privateRow 11 6, 2362450527360⟩, ⟨.privateRow 11 7, 2160519609600⟩, ⟨.privateRow 12 2, 460600971600⟩, ⟨.privateRow 12 3, 455715136800⟩, ⟨.privateRow 13 0, 163878422400⟩, ⟨.privateRow 14 0, 85667662080⟩, ⟨.privateRow 15 0, 123462218880⟩, ⟨.privateRow 16 0, 245959889175⟩, ⟨.privateRow 17 0, 514005972480⟩, ⟨.privateRow 18 0, 1560375273600⟩, ⟨.privateRow 19 0, 6049454906880⟩, ⟨.privateRow 22 0, 1743251255665920⟩, ⟨.privateRow 23 8, 383515276246502400⟩, ⟨.hall 19 1, 25941238923600⟩, ⟨.hall 20 1, 188663555808000⟩, ⟨.hall 5 24, 124013825591040⟩, ⟨.hall 6 24, 441274127374080⟩, ⟨.hall 5 25, 365487900624000⟩, ⟨.hall 4 26, 11077485492353280⟩, ⟨.hall 3 27, 22324289039395200⟩]
  caps := #[0, 28414717436851200, 3697805693836800, 0, 35732593765440, 23787054170880, 13439898991200, 2011027560960, 1040821784688, 923324282496, 112545135360, 2329340878080, 1038230909520, 0, 30731291136, 1728471064320, 0, 8224095559680, 26526379651200, 0, 518824778472000, 0, 36608276368984320, 0] }

theorem case_54_31_13_checked :
    (Witness.linear .positive case_54_31_13).check 54 31 13 = true := by
  change case_54_31_13.check 54 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_31_14 : Certificate := {
  objectiveScale := 23631229440000
  eta := 177615512311661424000
  rows := #[⟨.count 2, 35636413793950569600⟩, ⟨.count 3, 6790586230552924800⟩, ⟨.count 4, 1307936513536773120⟩, ⟨.count 5, 270498855554928000⟩, ⟨.count 6, 56655665809142400⟩, ⟨.count 7, 12102913129507200⟩, ⟨.count 8, 2806472609740800⟩, ⟨.count 9, 701618152435200⟩, ⟨.count 10, 187933433688000⟩, ⟨.count 11, 63608239094400⟩, ⟨.count 12, 21202746364800⟩, ⟨.count 13, 25057791158400⟩, ⟨.path 14, 2455153454208⟩, ⟨.path 15, 4603502502144⟩, ⟨.privateRow 3 28, 218528996692406400⟩, ⟨.privateRow 6 20, 3467023826666400⟩, ⟨.privateRow 6 21, 8027402607544320⟩, ⟨.privateRow 6 22, 12803139182433600⟩, ⟨.privateRow 6 23, 15666687872035200⟩, ⟨.privateRow 7 17, 438511345272000⟩, ⟨.privateRow 7 18, 1751658924787200⟩, ⟨.privateRow 7 19, 3406467498033600⟩, ⟨.privateRow 7 20, 6299528697221760⟩, ⟨.privateRow 7 22, 27226682193110400⟩, ⟨.privateRow 8 14, 30330368047980⟩, ⟨.privateRow 8 15, 362177888872800⟩, ⟨.privateRow 8 16, 737703981889875⟩, ⟨.privateRow 8 17, 1336415528448000⟩, ⟨.privateRow 8 18, 2391713962337700⟩, ⟨.privateRow 8 19, 3454738548501240⟩, ⟨.privateRow 9 12, 60771471284160⟩, ⟨.privateRow 9 13, 165464947615968⟩, ⟨.privateRow 9 14, 333701720031680⟩, ⟨.privateRow 9 15, 520366796389440⟩, ⟨.privateRow 9 16, 912103598165760⟩, ⟨.privateRow 9 17, 1303190753504640⟩, ⟨.privateRow 9 19, 3083221992090240⟩, ⟨.privateRow 10 9, 7324585107840⟩, ⟨.privateRow 10 10, 37899909127080⟩, ⟨.privateRow 10 12, 306582074823024⟩, ⟨.privateRow 10 13, 143664669308160⟩, ⟨.privateRow 10 14, 363181360602060⟩, ⟨.privateRow 10 15, 523886819433120⟩, ⟨.privateRow 10 17, 1603949212049184⟩, ⟨.privateRow 10 19, 847788600859200⟩, ⟨.privateRow 11 8, 38105635075200⟩, ⟨.privateRow 11 9, 19998044866800⟩, ⟨.privateRow 11 10, 36097237612800⟩, ⟨.privateRow 11 11, 201329714345760⟩, ⟨.privateRow 11 13, 452485882648800⟩, ⟨.privateRow 11 15, 477704300673600⟩, ⟨.privateRow 12 5, 5123997038160⟩, ⟨.privateRow 12 7, 51172012861200⟩, ⟨.privateRow 12 8, 7288444062900⟩, ⟨.privateRow 12 9, 28511268786000⟩, ⟨.privateRow 12 10, 167059972399320⟩, ⟨.privateRow 12 12, 297169742019150⟩, ⟨.privateRow 12 13, 69287546156400⟩, ⟨.privateRow 12 15, 394724461491360⟩, ⟨.privateRow 13 4, 13685409017280⟩, ⟨.privateRow 13 5, 3923884879200⟩, ⟨.privateRow 13 6, 41960679868800⟩, ⟨.privateRow 13 8, 35045861760000⟩, ⟨.privateRow 13 9, 102158687030400⟩, ⟨.privateRow 13 11, 323221411913400⟩, ⟨.privateRow 13 14, 153623535024960⟩, ⟨.privateRow 14 2, 3445446284280⟩, ⟨.privateRow 14 3, 12695947520256⟩, ⟨.privateRow 14 4, 7696321570080⟩, ⟨.privateRow 14 5, 24961415038560⟩, ⟨.privateRow 14 7, 102053549445120⟩, ⟨.privateRow 14 8, 66653724481344⟩, ⟨.privateRow 14 10, 322462449969660⟩, ⟨.privateRow 14 12, 273129923626560⟩, ⟨.privateRow 14 16, 825027773890320⟩, ⟨.privateRow 15 0, 5961461425920⟩, ⟨.privateRow 15 4, 20089066757760⟩, ⟨.privateRow 15 5, 149256269001840⟩, ⟨.privateRow 15 7, 141103206211968⟩, ⟨.privateRow 15 9, 286737696325080⟩, ⟨.privateRow 15 10, 179023996831680⟩, ⟨.privateRow 15 12, 440070496721856⟩, ⟨.privateRow 15 16, 705516031059840⟩, ⟨.privateRow 16 2, 43068078553500⟩, ⟨.privateRow 16 4, 226259673289650⟩, ⟨.privateRow 16 6, 105973575107400⟩, ⟨.privateRow 16 8, 5024609164575⟩, ⟨.privateRow 17 1, 85912426828800⟩, ⟨.privateRow 17 2, 6425074656000⟩, ⟨.privateRow 17 3, 388395762955200⟩, ⟨.privateRow 17 4, 97193856614400⟩, ⟨.privateRow 17 5, 151182006655680⟩, ⟨.privateRow 17 6, 76101439814400⟩, ⟨.privateRow 17 7, 5220373158000⟩, ⟨.privateRow 17 9, 2784199017600⟩, ⟨.privateRow 18 0, 201158379021600⟩, ⟨.privateRow 18 3, 1856681081236800⟩, ⟨.privateRow 18 6, 94662766598400⟩, ⟨.privateRow 18 7, 6761626185600⟩, ⟨.privateRow 19 1, 1931120438607360⟩, ⟨.privateRow 19 2, 2834719574319360⟩, ⟨.privateRow 19 5, 3184218811453680⟩, ⟨.privateRow 20 0, 5800461023316960⟩, ⟨.privateRow 20 1, 10705713474324960⟩, ⟨.privateRow 20 9, 52069254767449920⟩, ⟨.privateRow 21 0, 99086099510361600⟩, ⟨.privateRow 21 8, 38669740155446400⟩, ⟨.privateRow 21 10, 539577769610880000⟩, ⟨.privateRow 22 0, 1101952699987819680⟩, ⟨.privateRow 23 0, 24651509700955737600⟩, ⟨.hall 13 1, 1879334336880⟩, ⟨.hall 20 3, 670384501637760⟩, ⟨.hall 12 6, 70509582000⟩, ⟨.hall 21 7, 11567198436033240⟩, ⟨.hall 22 8, 692458137667296000⟩, ⟨.hall 14 12, 181980790992⟩, ⟨.hall 17 13, 172421467732800⟩, ⟨.hall 16 14, 124732115988480⟩, ⟨.hall 15 15, 109627836318000⟩, ⟨.hall 12 18, 207563727571200⟩, ⟨.hall 6 19, 893176075584⟩, ⟨.hall 11 19, 576714701122560⟩, ⟨.hall 10 20, 6595568601336000⟩, ⟨.hall 5 21, 12236795940096⟩, ⟨.hall 9 21, 7595813793466080⟩, ⟨.hall 8 22, 17836607849860800⟩, ⟨.hall 6 23, 721803595312800⟩, ⟨.hall 7 23, 48574876185435600⟩, ⟨.hall 5 25, 7045094360304000⟩, ⟨.hall 4 26, 401325954419470080⟩, ⟨.hall 3 27, 413933231830060800⟩]
  caps := #[0, 0, 0, 3996489891663360, 742779692019456, 814099792746240, 45222952494720, 101615309288064, 0, 0, 4621840358148, 0, 4907209616400, 16748289241056, 433559780472, 0, 53654463951270, 4176298526400, 12063355808400, 652527661574880, 0, 16269087295843200, 0, 0] }

theorem case_54_31_14_checked :
    (Witness.linear .positive case_54_31_14).check 54 31 14 = true := by
  change case_54_31_14.check 54 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_31_15 : Certificate := {
  objectiveScale := 14769518400000
  eta := 120903190836709881600
  rows := #[⟨.count 2, 28837733896853481600⟩, ⟨.count 3, 6750117897832108800⟩, ⟨.count 4, 1536177910082175360⟩, ⟨.count 5, 381680274924748800⟩, ⟨.count 6, 93858133082313600⟩, ⟨.count 7, 22744121774774400⟩, ⟨.count 8, 5846817936960000⟩, ⟨.count 9, 1578640842979200⟩, ⟨.count 10, 425982449692800⟩, ⟨.count 11, 127216478188800⟩, ⟨.count 12, 42405492729600⟩, ⟨.count 13, 12528895579200⟩, ⟨.count 14, 17540453810880⟩, ⟨.path 15, 3408318321408⟩, ⟨.privateRow 2 29, 198294830331998400⟩, ⟨.privateRow 3 28, 1599848086896259200⟩, ⟨.privateRow 7 18, 1595346037084800⟩, ⟨.privateRow 7 19, 5139631386489600⟩, ⟨.privateRow 8 16, 830887642760175⟩, ⟨.privateRow 8 17, 2152881890359200⟩, ⟨.privateRow 8 18, 5003292640846500⟩, ⟨.privateRow 9 13, 32547286515744⟩, ⟨.privateRow 9 14, 326122511594880⟩, ⟨.privateRow 9 15, 863136497943720⟩, ⟨.privateRow 9 16, 1935018317232000⟩, ⟨.privateRow 9 17, 3517510635518880⟩, ⟨.privateRow 9 18, 2677063039402752⟩, ⟨.privateRow 9 19, 3476420498350800⟩, ⟨.privateRow 9 21, 10547659558275840⟩, ⟨.privateRow 10 11, 31436137998720⟩, ⟨.privateRow 10 12, 130926958802640⟩, ⟨.privateRow 10 13, 332711782603200⟩, ⟨.privateRow 10 14, 771623356483980⟩, ⟨.privateRow 10 15, 1395897951745440⟩, ⟨.privateRow 10 16, 2273368102845840⟩, ⟨.privateRow 10 17, 2344657518691488⟩, ⟨.privateRow 11 9, 19516164267600⟩, ⟨.privateRow 11 10, 59490350337600⟩, ⟨.privateRow 11 11, 134348311056960⟩, ⟨.privateRow 11 12, 312044459126400⟩, ⟨.privateRow 11 13, 592110786267000⟩, ⟨.privateRow 11 14, 972297369014400⟩, ⟨.privateRow 11 16, 1547222227911360⟩, ⟨.privateRow 12 7, 11009118304800⟩, ⟨.privateRow 12 8, 28785673016100⟩, ⟨.privateRow 12 10, 257525023555800⟩, ⟨.privateRow 12 11, 202996664270400⟩, ⟨.privateRow 12 12, 459282406933350⟩, ⟨.privateRow 12 14, 1728023828731200⟩, ⟨.privateRow 12 17, 265328812148400⟩, ⟨.privateRow 13 4, 835259705280⟩, ⟨.privateRow 13 5, 4818805992000⟩, ⟨.privateRow 13 6, 15420179174400⟩, ⟨.privateRow 13 7, 31000985215200⟩, ⟨.privateRow 13 8, 5870181844800⟩, ⟨.privateRow 13 10, 679558729449600⟩, ⟨.privateRow 13 11, 138902082719400⟩, ⟨.privateRow 13 12, 135339608289600⟩, ⟨.privateRow 13 13, 953641705816800⟩, ⟨.privateRow 13 15, 725471242095600⟩, ⟨.privateRow 14 4, 16198072141680⟩, ⟨.privateRow 14 5, 13010776178400⟩, ⟨.privateRow 14 6, 37795501663920⟩, ⟨.privateRow 14 7, 6606144941760⟩, ⟨.privateRow 14 9, 464543606086560⟩, ⟨.privateRow 14 10, 602953099749000⟩, ⟨.privateRow 14 12, 632918041675920⟩, ⟨.privateRow 14 13, 562547411506080⟩, ⟨.privateRow 14 15, 352479595628160⟩, ⟨.privateRow 15 0, 1261078378560⟩, ⟨.privateRow 15 2, 1819010024832⟩, ⟨.privateRow 15 3, 21577542386400⟩, ⟨.privateRow 15 4, 18889719488640⟩, ⟨.privateRow 15 5, 12343282311360⟩, ⟨.privateRow 15 7, 144611296974144⟩, ⟨.privateRow 15 8, 377228031340160⟩, ⟨.privateRow 15 9, 746687374032600⟩, ⟨.privateRow 15 10, 341342799557760⟩, ⟨.privateRow 15 11, 431040411241440⟩, ⟨.privateRow 15 13, 1429546985586720⟩, ⟨.privateRow 16 0, 5938174467225⟩, ⟨.privateRow 16 2, 16444175447700⟩, ⟨.privateRow 16 3, 72241933163400⟩, ⟨.privateRow 16 6, 186732747861660⟩, ⟨.privateRow 16 8, 1969646792513400⟩, ⟨.privateRow 16 10, 312439333506300⟩, ⟨.privateRow 17 0, 26171470765440⟩, ⟨.privateRow 17 1, 19091650406400⟩, ⟨.privateRow 17 2, 136854090172800⟩, ⟨.privateRow 17 3, 20881492632000⟩, ⟨.privateRow 17 5, 267283105689600⟩, ⟨.privateRow 17 6, 133641552844800⟩, ⟨.privateRow 17 7, 2251024905729600⟩, ⟨.privateRow 17 8, 1970019676310400⟩, ⟨.privateRow 18 0, 180873500464800⟩, ⟨.privateRow 18 1, 222093413942400⟩, ⟨.privateRow 18 2, 138049867956000⟩, ⟨.privateRow 18 5, 1356832987910400⟩, ⟨.privateRow 18 6, 2712679905335400⟩, ⟨.privateRow 18 7, 5297734116417600⟩, ⟨.privateRow 18 10, 4881048902730000⟩, ⟨.privateRow 19 0, 1703929798771200⟩, ⟨.privateRow 19 3, 272628767803392⟩, ⟨.privateRow 19 4, 2300305228341120⟩, ⟨.privateRow 19 5, 6506881919057520⟩, ⟨.privateRow 19 6, 12304807332554880⟩, ⟨.privateRow 19 9, 30031762703342400⟩, ⟨.privateRow 20 0, 3271190228265960⟩, ⟨.privateRow 20 2, 15094688104864368⟩, ⟨.privateRow 20 4, 13910989372780500⟩, ⟨.privateRow 20 5, 37808985142019520⟩, ⟨.privateRow 21 0, 33846241911955200⟩, ⟨.privateRow 21 1, 37230866103150720⟩, ⟨.privateRow 21 3, 127812484176577200⟩, ⟨.privateRow 21 8, 521591843957184000⟩, ⟨.privateRow 22 0, 711028605904737120⟩, ⟨.privateRow 22 2, 509900992282281600⟩, ⟨.privateRow 22 3, 764851488423422400⟩, ⟨.privateRow 22 7, 783736710359803200⟩, ⟨.privateRow 22 8, 4433305849565392800⟩, ⟨.privateRow 23 0, 20496760874951961600⟩, ⟨.privateRow 23 6, 62321232390056640000⟩, ⟨.hall 13 5, 49279152780⟩, ⟨.hall 22 7, 2440914935277218400⟩, ⟨.hall 17 13, 791110263715200⟩, ⟨.hall 16 14, 20639267317468800⟩, ⟨.hall 15 15, 17767018005937200⟩, ⟨.hall 14 16, 11063899189062720⟩, ⟨.hall 13 17, 12324256951406400⟩, ⟨.hall 12 18, 15777633130459200⟩, ⟨.hall 11 19, 23302878392233440⟩, ⟨.hall 10 20, 39395023999531200⟩, ⟨.hall 9 21, 60616619196981120⟩, ⟨.hall 8 22, 96093723841315200⟩, ⟨.hall 7 23, 243756275966002800⟩, ⟨.hall 6 24, 451069976096707968⟩, ⟨.hall 5 25, 776778997014820800⟩, ⟨.hall 4 26, 1123041197816778240⟩, ⟨.hall 3 27, 1314931753907085600⟩]
  caps := #[0, 253560244328052480, 27146699748604800, 3774462675459840, 0, 0, 47548396756224, 38756050324992, 3606079276800, 0, 17165382821964, 0, 16625153579622, 5648941142208, 7510856737176, 0, 96521687937675, 6642303370560, 45840358037760, 97367417072640, 4269890867911812, 1030103014711680, 0, 0] }

theorem case_54_31_15_checked :
    (Witness.linear .positive case_54_31_15).check 54 31 15 = true := by
  change case_54_31_15.check 54 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_31_16 : Certificate := {
  objectiveScale := 172907280000000
  eta := 1590437850594245452800
  rows := #[⟨.count 2, 373511919457739462400⟩, ⟨.count 3, 85906176699748204800⟩, ⟨.count 4, 20435968446242469120⟩, ⟨.count 5, 5139052273093939200⟩, ⟨.count 6, 1292998728967545600⟩, ⟨.count 7, 331202746735660800⟩, ⟨.count 8, 93821938495084800⟩, ⟨.count 9, 27807466108181760⟩, ⟨.count 10, 8477886008592000⟩, ⟨.count 11, 2869438341369600⟩, ⟨.count 12, 1024799407632000⟩, ⟨.count 13, 484450629062400⟩, ⟨.count 14, 339115440343680⟩, ⟨.path 14, 48085613372160⟩, ⟨.privateRow 4 25, 1702997370520205760⟩, ⟨.privateRow 5 22, 72473814107735040⟩, ⟨.privateRow 5 23, 677383092086500800⟩, ⟨.privateRow 5 24, 1563128399732739840⟩, ⟨.privateRow 6 20, 69011786371528000⟩, ⟨.privateRow 6 21, 244141585908380160⟩, ⟨.privateRow 6 22, 568489356242808000⟩, ⟨.privateRow 6 23, 911870653514620800⟩, ⟨.privateRow 7 18, 37118145817209600⟩, ⟨.privateRow 7 19, 94979237220067200⟩, ⟨.privateRow 7 20, 205697737099895040⟩, ⟨.privateRow 7 21, 330637554335088000⟩, ⟨.privateRow 7 22, 441496006618867200⟩, ⟨.privateRow 8 15, 408194511524800⟩, ⟨.privateRow 8 16, 16302268304021700⟩, ⟨.privateRow 8 17, 38231228810174400⟩, ⟨.privateRow 8 18, 78255597795975600⟩, ⟨.privateRow 8 19, 122872827884526720⟩, ⟨.privateRow 8 20, 161909960501589300⟩, ⟨.privateRow 8 21, 169981614472269600⟩, ⟨.privateRow 9 13, 874164246219264⟩, ⟨.privateRow 9 14, 6292475393043840⟩, ⟨.privateRow 9 15, 15542791015752000⟩, ⟨.privateRow 9 16, 31333190130802560⟩, ⟨.privateRow 9 17, 48367909657907840⟩, ⟨.privateRow 9 18, 63211118080061952⟩, ⟨.privateRow 9 19, 68473059329394720⟩, ⟨.privateRow 9 20, 53216004471710080⟩, ⟨.privateRow 10 11, 620977624525440⟩, ⟨.privateRow 10 12, 2683856485005696⟩, ⟨.privateRow 10 13, 6222499191068160⟩, ⟨.privateRow 10 14, 13116500781864480⟩, ⟨.privateRow 10 15, 20457657992977920⟩, ⟨.privateRow 10 16, 26794156875726240⟩, ⟨.privateRow 10 17, 22546332276564096⟩, ⟨.privateRow 11 9, 343152528919200⟩, ⟨.privateRow 11 10, 1239922589068800⟩, ⟨.privateRow 11 11, 2709196979448960⟩, ⟨.privateRow 11 12, 5614658572723200⟩, ⟨.privateRow 11 13, 9323345519888400⟩, ⟨.privateRow 11 14, 8783994922560000⟩, ⟨.privateRow 12 7, 174741437455200⟩, ⟨.privateRow 12 8, 604916317005000⟩, ⟨.privateRow 12 9, 1296526523292000⟩, ⟨.privateRow 12 10, 2645690470703280⟩, ⟨.privateRow 12 11, 3087682659661600⟩, ⟨.privateRow 13 5, 89170857547200⟩, ⟨.privateRow 13 6, 311023037001600⟩, ⟨.privateRow 13 7, 676988699587200⟩, ⟨.privateRow 13 8, 858798842428800⟩, ⟨.privateRow 14 3, 46830227476032⟩, ⟨.privateRow 14 4, 171287900989920⟩, ⟨.privateRow 14 5, 191916979974720⟩, ⟨.privateRow 15 0, 13298644719360⟩, ⟨.privateRow 15 1, 16484778350040⟩, ⟨.privateRow 15 2, 42703425821056⟩, ⟨.privateRow 16 0, 13246696888425⟩, ⟨.privateRow 17 0, 10765569534720⟩, ⟨.privateRow 18 0, 32681193230400⟩, ⟨.privateRow 19 0, 126702472216320⟩, ⟨.privateRow 20 0, 651989804946480⟩, ⟨.privateRow 21 0, 4741744035974400⟩, ⟨.privateRow 22 0, 54767143615504320⟩, ⟨.privateRow 23 0, 1338752399490105600⟩, ⟨.hall 7 20, 65369984971200⟩, ⟨.hall 7 21, 1173016243744800⟩, ⟨.hall 8 22, 18356466227299200⟩, ⟨.hall 6 24, 1345926575028043008⟩, ⟨.hall 5 25, 3342727973247062400⟩, ⟨.hall 4 26, 6911671478925973760⟩, ⟨.hall 3 27, 11942590398605380800⟩, ⟨.hall 2 28, 12879721360611705600⟩, ⟨.assumptionRow 16, 257404597632000⟩]
  caps := #[0, 0, 0, 0, 0, 398283521126400, 0, 178150875583200, 225185407066620, 0, 315883146765888, 6233922777600, 229117150842440, 1708126318080, 307636275469536, 0, 101228173403175, 345156392555520, 555580284916800, 2280644499893760, 12387806293983120, 94834880719488000, 1150110015925590720, 0] }

theorem case_54_31_16_checked :
    (Witness.linear .conditional case_54_31_16).check 54 31 16 = true := by
  change case_54_31_16.check 54 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_31_17 : Certificate := {
  objectiveScale := 39901680000000
  eta := 361463147862328512000
  rows := #[⟨.count 2, 84172886879828947200⟩, ⟨.count 3, 19174518632856787200⟩, ⟨.count 4, 4795435168443279360⟩, ⟨.count 5, 1204940510777203200⟩, ⟨.count 6, 305986470402412800⟩, ⟨.count 7, 78779125372147200⟩, ⟨.count 8, 20868642482688000⟩, ⟨.count 9, 5791048288945920⟩, ⟨.count 10, 1732842634723200⟩, ⟨.count 11, 567581210380800⟩, ⟨.count 12, 236492170992000⟩, ⟨.count 13, 111796299014400⟩, ⟨.count 14, 78257409310080⟩, ⟨.path 12, 16485960165696⟩, ⟨.privateRow 2 29, 2527714320715584000⟩, ⟨.privateRow 4 25, 590401844909997120⟩, ⟨.privateRow 5 22, 28279991798682624⟩, ⟨.privateRow 5 23, 195850346428376640⟩, ⟨.privateRow 5 24, 490845377366023680⟩, ⟨.privateRow 6 20, 17808736372627200⟩, ⟨.privateRow 6 21, 69095081515299840⟩, ⟨.privateRow 6 22, 169596538331220000⟩, ⟨.privateRow 6 23, 294759223558800000⟩, ⟨.privateRow 7 18, 8075951695468800⟩, ⟨.privateRow 7 19, 25309439915760000⟩, ⟨.privateRow 7 20, 60347642207973120⟩, ⟨.privateRow 7 21, 105246899163806400⟩, ⟨.privateRow 7 22, 153955925553830400⟩, ⟨.privateRow 8 16, 3228118134040800⟩, ⟨.privateRow 8 17, 9472407251907600⟩, ⟨.privateRow 8 18, 22254450772554000⟩, ⟨.privateRow 8 19, 38946104033316480⟩, ⟨.privateRow 8 20, 56977100247167100⟩, ⟨.privateRow 8 21, 70322977532808000⟩, ⟨.privateRow 9 14, 1210574492167040⟩, ⟨.privateRow 9 15, 3599840828263680⟩, ⟨.privateRow 9 16, 8530057614798720⟩, ⟨.privateRow 9 17, 15105129208128960⟩, ⟨.privateRow 9 18, 22275536796729216⟩, ⟨.privateRow 9 19, 27646603655711040⟩, ⟨.privateRow 9 20, 26958228296039040⟩, ⟨.privateRow 10 12, 437682510641376⟩, ⟨.privateRow 10 13, 1385031926678400⟩, ⟨.privateRow 10 14, 3399306216906600⟩, ⟨.privateRow 10 15, 6194313510390720⟩, ⟨.privateRow 10 16, 9326606245276320⟩, ⟨.privateRow 10 17, 11834756213664384⟩, ⟨.privateRow 10 18, 11077615778589360⟩, ⟨.privateRow 11 10, 154013083257600⟩, ⟨.privateRow 11 11, 540062121392640⟩, ⟨.privateRow 11 12, 1407486738873600⟩, ⟨.privateRow 11 13, 2698160678136000⟩, ⟨.privateRow 11 14, 4228602870412800⟩, ⟨.privateRow 11 15, 5382705140366400⟩, ⟨.privateRow 12 8, 52882277124600⟩, ⟨.privateRow 12 9, 213917918306400⟩, ⟨.privateRow 12 10, 605025804121200⟩, ⟨.privateRow 12 11, 1248591073144800⟩, ⟨.privateRow 12 12, 2086550716981500⟩, ⟨.privateRow 12 13, 384018239563200⟩, ⟨.privateRow 13 6, 17199430617600⟩, ⟨.privateRow 13 7, 86355474559200⟩, ⟨.privateRow 13 8, 270109239926400⟩, ⟨.privateRow 13 9, 612299729986560⟩, ⟨.privateRow 13 10, 368832234355200⟩, ⟨.privateRow 14 4, 4791269957760⟩, ⟨.privateRow 14 5, 35688818531520⟩, ⟨.privateRow 14 6, 125770836391200⟩, ⟨.privateRow 14 7, 189037378333440⟩, ⟨.privateRow 15 3, 15527263752000⟩, ⟨.privateRow 15 4, 61535740654080⟩, ⟨.privateRow 15 5, 2173816925280⟩, ⟨.privateRow 16 0, 3056930051175⟩, ⟨.privateRow 16 1, 2173816925280⟩, ⟨.privateRow 16 2, 10480903032600⟩, ⟨.privateRow 17 0, 2484362200320⟩, ⟨.hall 8 22, 39758166425577600⟩, ⟨.hall 7 23, 190545922585418400⟩, ⟨.hall 6 24, 526068664642160640⟩, ⟨.hall 5 25, 1180233528695020800⟩, ⟨.hall 4 26, 2303028603318643200⟩, ⟨.hall 3 27, 3925695098090937600⟩, ⟨.hall 2 28, 4942117309812883200⟩, ⟨.assumptionRow 17, 44314406791200⟩]
  caps := #[0, 1378473819935415840, 12288954086660160, 0, 3198100101805440, 1426769211643776, 114159772960800, 81899441178048, 155657833101540, 29526886744992, 14365585272600, 72559713496320, 0, 0, 0, 231880747573440, 0, 0, 39901680000000, 0, 0, 0, 0, 0] }

theorem case_54_31_17_checked :
    (Witness.linear .conditional case_54_31_17).check 54 31 17 = true := by
  change case_54_31_17.check 54 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_31_18 : Certificate := {
  objectiveScale := 8740368000000
  eta := 50048743550168563200
  rows := #[⟨.count 2, 12217285883458656000⟩, ⟨.count 3, 2979091877986224000⟩, ⟨.count 4, 777573071991555840⟩, ⟨.count 5, 205258004990438400⟩, ⟨.count 6, 55115575414099200⟩, ⟨.count 7, 15042813122937600⟩, ⟨.count 8, 4217204835043200⟩, ⟨.count 9, 1199946942754560⟩, ⟨.count 10, 372654330048000⟩, ⟨.count 11, 134012230228800⟩, ⟨.count 12, 55181506564800⟩, ⟨.count 13, 18632716502400⟩, ⟨.count 14, 13042901551680⟩, ⟨.path 12, 2439475236576⟩, ⟨.privateRow 2 29, 884700012250454400⟩, ⟨.privateRow 4 25, 115352042413608000⟩, ⟨.privateRow 5 22, 2267974252672128⟩, ⟨.privateRow 5 23, 36395285144137920⟩, ⟨.privateRow 5 24, 100939636199001600⟩, ⟨.privateRow 6 20, 1302219853334400⟩, ⟨.privateRow 6 21, 11829083586640320⟩, ⟨.privateRow 6 22, 33875313752280000⟩, ⟨.privateRow 6 23, 65732773317411200⟩, ⟨.privateRow 7 18, 519941517638400⟩, ⟨.privateRow 7 19, 3907694710920000⟩, ⟨.privateRow 7 20, 11558495136988800⟩, ⟨.privateRow 7 21, 23151150254232000⟩, ⟨.privateRow 7 22, 38076991323571200⟩, ⟨.privateRow 8 16, 171527741760375⟩, ⟨.privateRow 8 17, 1296914704885800⟩, ⟨.privateRow 8 18, 4017485405033100⟩, ⟨.privateRow 8 19, 8370282070790640⟩, ⟨.privateRow 8 20, 14055764375302650⟩, ⟨.privateRow 8 21, 19917597577878000⟩, ⟨.privateRow 9 14, 46374761072640⟩, ⟨.privateRow 9 15, 427517328638400⟩, ⟨.privateRow 9 16, 1421469238949760⟩, ⟨.privateRow 9 17, 3119427287776800⟩, ⟨.privateRow 9 18, 5411354932663680⟩, ⟨.privateRow 9 19, 7836972318455280⟩, ⟨.privateRow 9 20, 9198144016501440⟩, ⟨.privateRow 10 12, 8012068096032⟩, ⟨.privateRow 10 13, 137468041751040⟩, ⟨.privateRow 10 14, 509837705296920⟩, ⟨.privateRow 10 15, 1200612396915360⟩, ⟨.privateRow 10 16, 2184375464631360⟩, ⟨.privateRow 10 17, 3279358104422400⟩, ⟨.privateRow 10 18, 4062398015435760⟩, ⟨.privateRow 10 19, 3697662589901280⟩, ⟨.privateRow 11 11, 39988676185920⟩, ⟨.privateRow 11 12, 183699474235200⟩, ⟨.privateRow 11 13, 476746717431600⟩, ⟨.privateRow 11 14, 927438345028800⟩, ⟨.privateRow 11 15, 1468640269958400⟩, ⟨.privateRow 11 16, 1932356029887360⟩, ⟨.privateRow 11 17, 802281774016800⟩, ⟨.privateRow 12 9, 9137197515600⟩, ⟨.privateRow 12 10, 63918578437560⟩, ⟨.privateRow 12 11, 194011169906400⟩, ⟨.privateRow 12 12, 413697068561700⟩, ⟨.privateRow 12 13, 705628822892400⟩, ⟨.privateRow 12 14, 666667050541800⟩, ⟨.privateRow 13 7, 1791607356000⟩, ⟨.privateRow 13 8, 20261450462400⟩, ⟨.privateRow 13 9, 78544066487040⟩, ⟨.privateRow 13 10, 192538070524800⟩, ⟨.privateRow 13 11, 362800489590000⟩, ⟨.privateRow 13 12, 30303758707200⟩, ⟨.privateRow 14 6, 6366178138320⟩, ⟨.privateRow 14 7, 30320511399360⟩, ⟨.privateRow 14 8, 90834492949200⟩, ⟨.privateRow 14 9, 88919463753120⟩, ⟨.privateRow 15 4, 1337733492480⟩, ⟨.privateRow 15 5, 12076760696000⟩, ⟨.privateRow 15 6, 41763634261440⟩, ⟨.privateRow 15 7, 4927318363968⟩, ⟨.privateRow 16 2, 194090796900⟩, ⟨.privateRow 16 3, 4180417164000⟩, ⟨.privateRow 16 4, 10416206100300⟩, ⟨.privateRow 17 1, 1774544428800⟩, ⟨.privateRow 17 2, 1433285884800⟩, ⟨.hall 8 21, 683721272052000⟩, ⟨.hall 9 21, 2328157926974880⟩, ⟨.hall 8 22, 6994964810433600⟩, ⟨.hall 7 23, 65006183636394000⟩, ⟨.hall 6 24, 149470906473592704⟩, ⟨.hall 5 25, 299005651500494400⟩, ⟨.hall 4 26, 537819145769185280⟩, ⟨.hall 3 27, 870083977062643200⟩, ⟨.hall 2 28, 1130207897423404800⟩, ⟨.assumptionRow 18, 7328675062800⟩]
  caps := #[0, 178102285399059840, 21103885510540560, 2877343130188800, 326254026290400, 349520902832192, 63380673966400, 21671614536768, 11930182180035, 6633229568784, 6908831153928, 4807525004352, 4900067925036, 4060438804800, 4564526715840, 21407883653632, 12828444930000, 7328675062800, 97555740937200, 8740368000000, 0, 0, 0, 0] }

theorem case_54_31_18_checked :
    (Witness.linear .conditional case_54_31_18).check 54 31 18 = true := by
  change case_54_31_18.check 54 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_31_19 : Certificate := {
  objectiveScale := 2508105600000
  eta := 14883776676684115200
  rows := #[⟨.count 2, 3583406772308563200⟩, ⟨.count 3, 867706974800265600⟩, ⟨.count 4, 221546725756836480⟩, ⟨.count 5, 56792519899315200⟩, ⟨.count 6, 14608049737881600⟩, ⟨.count 7, 3767096859926400⟩, ⟨.count 8, 966709173830400⟩, ⟨.count 9, 243978981966720⟩, ⟨.count 10, 69050655273600⟩, ⟨.count 11, 20866956264000⟩, ⟨.count 12, 6955652088000⟩, ⟨.count 13, 3288126441600⟩, ⟨.count 14, 2301688509120⟩, ⟨.path 12, 886994351712⟩, ⟨.privateRow 2 29, 297378155378304000⟩, ⟨.privateRow 4 25, 34623313804759680⟩, ⟨.privateRow 5 22, 547801865170560⟩, ⟨.privateRow 5 23, 10567545164336160⟩, ⟨.privateRow 5 24, 30803606921767680⟩, ⟨.privateRow 6 20, 300193765872000⟩, ⟨.privateRow 6 21, 3286811191023360⟩, ⟨.privateRow 6 22, 10039152378855600⟩, ⟨.privateRow 6 23, 20720615901585600⟩, ⟨.privateRow 7 18, 111952876464000⟩, ⟨.privateRow 7 19, 1027174165617600⟩, ⟨.privateRow 7 20, 3299086863072000⟩, ⟨.privateRow 7 21, 7122081872505600⟩, ⟨.privateRow 7 22, 12607772819241600⟩, ⟨.privateRow 8 16, 33266591733375⟩, ⟨.privateRow 8 17, 317852222688000⟩, ⟨.privateRow 8 18, 1092422924693100⟩, ⟨.privateRow 8 19, 2492824559064840⟩, ⟨.privateRow 8 20, 4565854700356950⟩, ⟨.privateRow 8 21, 7080249597220800⟩, ⟨.privateRow 9 14, 7331304140160⟩, ⟨.privateRow 9 15, 95424169440600⟩, ⟨.privateRow 9 16, 362753415984960⟩, ⟨.privateRow 9 17, 889645232636160⟩, ⟨.privateRow 9 18, 1708671251903616⟩, ⟨.privateRow 9 19, 2741758564905360⟩, ⟨.privateRow 9 20, 3659087995442880⟩, ⟨.privateRow 10 12, 427456437408⟩, ⟨.privateRow 10 13, 26779963129920⟩, ⟨.privateRow 10 14, 119502845361900⟩, ⟨.privateRow 10 15, 323152369356960⟩, ⟨.privateRow 10 16, 662420472714000⟩, ⟨.privateRow 10 17, 1114740626231232⟩, ⟨.privateRow 10 18, 1564038443527560⟩, ⟨.privateRow 10 19, 1715415564582720⟩, ⟨.privateRow 11 11, 5577168310560⟩, ⟨.privateRow 11 12, 38164749638400⟩, ⟨.privateRow 11 13, 118625484700800⟩, ⟨.privateRow 11 14, 265904642678400⟩, ⟨.privateRow 11 15, 477642521109600⟩, ⟨.privateRow 11 16, 713194625183040⟩, ⟨.privateRow 11 17, 864208155333600⟩, ⟨.privateRow 11 18, 306301624675200⟩, ⟨.privateRow 12 9, 779876143200⟩, ⟨.privateRow 12 10, 10491441899400⟩, ⟨.privateRow 12 11, 43240970480400⟩, ⟨.privateRow 12 12, 109855830164850⟩, ⟨.privateRow 12 13, 215625214728000⟩, ⟨.privateRow 12 14, 348072423237000⟩, ⟨.privateRow 12 15, 320122294596720⟩, ⟨.privateRow 13 8, 2299389120000⟩, ⟨.privateRow 13 9, 14404523142240⟩, ⟨.privateRow 13 10, 45907303780800⟩, ⟨.privateRow 13 11, 101900303089200⟩, ⟨.privateRow 13 12, 181533486182400⟩, ⟨.privateRow 13 13, 41312357856000⟩, ⟨.privateRow 14 6, 178106848920⟩, ⟨.privateRow 14 7, 4184888198400⟩, ⟨.privateRow 14 8, 18134017325424⟩, ⟨.privateRow 14 9, 49376698731360⟩, ⟨.privateRow 14 10, 65392614607320⟩, ⟨.privateRow 15 5, 681981780480⟩, ⟨.privateRow 15 6, 6533075465280⟩, ⟨.privateRow 15 7, 23144756675040⟩, ⟨.privateRow 15 8, 14975183263040⟩, ⟨.privateRow 16 4, 1558434928050⟩, ⟨.privateRow 16 5, 10244257569000⟩, ⟨.privateRow 16 6, 1534459006080⟩, ⟨.privateRow 17 2, 252932803200⟩, ⟨.privateRow 17 3, 3196789596000⟩, ⟨.privateRow 18 1, 716642942400⟩, ⟨.hall 9 21, 2714318485482240⟩, ⟨.hall 8 22, 10495532812564800⟩, ⟨.hall 7 23, 26029859285430000⟩, ⟨.hall 6 24, 54421693051549824⟩, ⟨.hall 5 25, 102328012459411200⟩, ⟨.hall 4 26, 176444372191127040⟩, ⟨.hall 3 27, 277805817600854400⟩, ⟨.hall 2 28, 358391949326611200⟩, ⟨.assumptionRow 19, 1196731186560⟩]
  caps := #[0, 751958332070400, 2378944534468320, 42724566007200, 239019035392800, 66061449417600, 7584471140400, 2636413868160, 0, 1232992430208, 4395306403620, 0, 2327975067222, 198545059440, 3018053630592, 1196731186560, 7402385103750, 1196731186560, 1196731186560, 26392430413440, 2508105600000, 0, 0, 0] }

theorem case_54_31_19_checked :
    (Witness.linear .conditional case_54_31_19).check 54 31 19 = true := by
  change case_54_31_19.check 54 31 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_31_20 : Certificate := {
  objectiveScale := 420420000000
  eta := 2420940181306046400
  rows := #[⟨.count 2, 621033259830984000⟩, ⟨.count 3, 161250741149097600⟩, ⟨.count 4, 42896432684064960⟩, ⟨.count 5, 11435990380214400⟩, ⟨.count 6, 3058335536256000⟩, ⟨.count 7, 814056958915200⟩, ⟨.count 8, 221504448765600⟩, ⟨.count 9, 59367689821440⟩, ⟨.count 10, 15420179174400⟩, ⟨.count 11, 3669706101600⟩, ⟨.count 12, 815490244800⟩, ⟨.path 12, 22690437336⟩, ⟨.path 13, 112433614272⟩, ⟨.privateRow 2 29, 80625370574548800⟩, ⟨.privateRow 3 28, 118188284535921600⟩, ⟨.privateRow 5 22, 26869662211392⟩, ⟨.privateRow 6 20, 11529439521600⟩, ⟨.privateRow 7 18, 2661816643200⟩, ⟨.privateRow 7 20, 871432875593280⟩, ⟨.privateRow 7 21, 899992332439200⟩, ⟨.privateRow 8 18, 253315261098900⟩, ⟨.privateRow 8 19, 543866506943760⟩, ⟨.privateRow 8 20, 912862560109500⟩, ⟨.privateRow 9 15, 14588935140780⟩, ⟨.privateRow 9 16, 42341241983040⟩, ⟨.privateRow 9 17, 198966714666720⟩, ⟨.privateRow 9 18, 391092152619168⟩, ⟨.privateRow 9 20, 1608874388721600⟩, ⟨.privateRow 10 13, 3822919420320⟩, ⟨.privateRow 10 15, 91619269925040⟩, ⟨.privateRow 10 16, 126983569232520⟩, ⟨.privateRow 10 17, 270171176747472⟩, ⟨.privateRow 10 18, 228062040586380⟩, ⟨.privateRow 10 19, 478186181272800⟩, ⟨.privateRow 10 21, 1965253647717360⟩, ⟨.privateRow 11 11, 926693460000⟩, ⟨.privateRow 11 12, 6107939560800⟩, ⟨.privateRow 11 13, 8789687468100⟩, ⟨.privateRow 11 14, 67717462665600⟩, ⟨.privateRow 11 15, 104951123323200⟩, ⟨.privateRow 11 16, 179333718379200⟩, ⟨.privateRow 11 17, 199405898722800⟩, ⟨.privateRow 11 18, 199202026161600⟩, ⟨.privateRow 12 9, 194605626600⟩, ⟨.privateRow 12 10, 1709131638060⟩, ⟨.privateRow 12 11, 7199721744600⟩, ⟨.privateRow 12 12, 12138912081450⟩, ⟨.privateRow 12 13, 51361323096600⟩, ⟨.privateRow 12 14, 84425892843600⟩, ⟨.privateRow 12 15, 124722437190120⟩, ⟨.privateRow 12 16, 113149271466000⟩, ⟨.privateRow 13 7, 27800803800⟩, ⟨.privateRow 13 8, 424594094400⟩, ⟨.privateRow 13 9, 2320440423840⟩, ⟨.privateRow 13 10, 7878953728800⟩, ⟨.privateRow 13 11, 13576059189000⟩, ⟨.privateRow 13 12, 41039281800000⟩, ⟨.privateRow 13 14, 156907736647200⟩, ⟨.privateRow 14 6, 64250746560⟩, ⟨.privateRow 14 7, 608921848080⟩, ⟨.privateRow 14 8, 2717806579488⟩, ⟨.privateRow 14 9, 8106302524320⟩, ⟨.privateRow 14 10, 13589032897440⟩, ⟨.privateRow 14 11, 33118965182160⟩, ⟨.privateRow 14 12, 15371991114480⟩, ⟨.privateRow 15 5, 131178607560⟩, ⟨.privateRow 15 6, 954026236800⟩, ⟨.privateRow 15 7, 3680496932112⟩, ⟨.privateRow 15 8, 10027875777920⟩, ⟨.privateRow 15 9, 17306206297380⟩, ⟨.privateRow 15 10, 35487829016640⟩, ⟨.privateRow 15 11, 34718604800880⟩, ⟨.privateRow 16 4, 245959889175⟩, ⟨.privateRow 16 5, 1507702177800⟩, ⟨.privateRow 16 6, 5214349650510⟩, ⟨.privateRow 16 7, 13383341271300⟩, ⟨.privateRow 16 8, 23577012233775⟩, ⟨.privateRow 16 9, 43288940494800⟩, ⟨.privateRow 16 10, 54884192413050⟩, ⟨.privateRow 17 3, 481880599200⟩, ⟨.privateRow 17 4, 2599234747200⟩, ⟨.privateRow 17 5, 8448973172640⟩, ⟨.privateRow 17 6, 20952882350400⟩, ⟨.privateRow 17 7, 38108724053400⟩, ⟨.privateRow 17 8, 65994695395200⟩, ⟨.privateRow 17 9, 94502139732000⟩, ⟨.privateRow 18 2, 1061922061200⟩, ⟨.privateRow 18 3, 5130324763200⟩, ⟨.privateRow 18 4, 16201896590880⟩, ⟨.privateRow 18 5, 39746225719200⟩, ⟨.privateRow 18 6, 74865505314600⟩, ⟨.privateRow 18 7, 127170584798400⟩, ⟨.privateRow 18 8, 192511299380400⟩, ⟨.privateRow 18 9, 156557652451200⟩, ⟨.privateRow 19 1, 2730656728800⟩, ⟨.privateRow 19 2, 12511372648320⟩, ⟨.privateRow 19 3, 38666099279808⟩, ⟨.privateRow 19 4, 93934591470720⟩, ⟨.privateRow 19 5, 183090533666040⟩, ⟨.privateRow 19 6, 312699204829440⟩, ⟨.privateRow 19 7, 484964635034880⟩, ⟨.privateRow 19 9, 1169813342617920⟩, ⟨.privateRow 20 0, 7782371677080⟩, ⟨.privateRow 20 1, 38204370051120⟩, ⟨.privateRow 20 2, 118292049491616⟩, ⟨.privateRow 20 3, 288812460016080⟩, ⟨.privateRow 20 4, 577841097023190⟩, ⟨.privateRow 20 5, 1005037713725760⟩, ⟨.privateRow 21 0, 216963089179200⟩, ⟨.privateRow 21 1, 466942300624800⟩, ⟨.privateRow 21 2, 1222120589289600⟩, ⟨.privateRow 21 3, 2412535219894800⟩, ⟨.privateRow 21 8, 8750844596894400⟩, ⟨.privateRow 22 0, 5774519784393360⟩, ⟨.privateRow 22 1, 6537192208747200⟩, ⟨.privateRow 22 2, 16342980521868000⟩, ⟨.privateRow 22 7, 151808130180907200⟩, ⟨.privateRow 23 0, 237033747124574400⟩, ⟨.privateRow 23 8, 9683760725224185600⟩, ⟨.hall 20 4, 90244067528160⟩, ⟨.hall 13 7, 11146063005⟩, ⟨.hall 16 9, 50022725760⟩, ⟨.hall 17 9, 106934808960⟩, ⟨.hall 21 9, 6537192208747200⟩, ⟨.hall 14 10, 446002200⟩, ⟨.hall 18 11, 7246742857200⟩, ⟨.hall 17 12, 5071219639200⟩, ⟨.hall 16 14, 26835395146560⟩, ⟨.hall 9 19, 2934506824704⟩, ⟨.hall 10 19, 6333287875200⟩, ⟨.hall 8 21, 159563110215600⟩, ⟨.hall 7 23, 8966057826726000⟩, ⟨.hall 6 24, 12379486893149376⟩, ⟨.hall 4 26, 63181328578368000⟩, ⟨.hall 3 27, 77078832624565200⟩]
  caps := #[0, 0, 307532709797040, 10707827850720, 0, 4977931916160, 0, 585150076512, 525075258708, 1014435960384, 205245917148, 195832191744, 369957403434, 398840213952, 0, 0, 4702717696950, 179514316800, 21895480736280, 0, 0, 154181217983520, 2505923680019760, 0] }

theorem case_54_31_20_checked :
    (Witness.linear .conditional case_54_31_20).check 54 31 20 = true := by
  change case_54_31_20.check 54 31 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_32_1_checked :
    (Witness.rising).check 54 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_32_2_checked :
    (Witness.rising).check 54 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_32_3_checked :
    (Witness.rising).check 54 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_32_4_checked :
    (Witness.rising).check 54 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_32_5_checked :
    (Witness.rising).check 54 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_32_6_checked :
    (Witness.rising).check 54 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_32_7_checked :
    (Witness.rising).check 54 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_32_8_checked :
    (Witness.rising).check 54 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_32_9_checked :
    (Witness.rising).check 54 32 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_32_10_checked :
    (Witness.rising).check 54 32 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_32_11_checked :
    (Witness.linear .positive case_54_32_11).check 54 32 11 = true := by
  change case_54_32_11.check 54 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_32_12_checked :
    (Witness.linear .positive case_54_32_12).check 54 32 12 = true := by
  change case_54_32_12.check 54 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_32_13_checked :
    (Witness.linear .positive case_54_32_13).check 54 32 13 = true := by
  change case_54_32_13.check 54 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_32_14 : Certificate := {
  objectiveScale := 589176806400000
  eta := 6397897717163214662400
  rows := #[⟨.count 2, 1332249887835439372800⟩, ⟨.count 3, 267224541455364292800⟩, ⟨.count 4, 55768599955902113280⟩, ⟨.count 5, 11716599947417164800⟩, ⟨.count 6, 2467307053814803200⟩, ⟨.count 7, 554877639262346400⟩, ⟨.count 8, 123098904844755840⟩, ⟨.count 9, 29575710904259520⟩, ⟨.count 10, 7378555734950400⟩, ⟨.count 11, 2254558696790400⟩, ⟨.count 12, 614879644579200⟩, ⟨.count 13, 799343537952960⟩, ⟨.path 14, 217066172843520⟩, ⟨.privateRow 3 29, 66612494391771968640⟩, ⟨.privateRow 6 20, 70672119149174400⟩, ⟨.privateRow 6 21, 353487475672531200⟩, ⟨.privateRow 6 22, 664520927884894080⟩, ⟨.privateRow 6 23, 1147057976962497600⟩, ⟨.privateRow 6 24, 1867799400350083200⟩, ⟨.privateRow 6 26, 10206728820172684800⟩, ⟨.privateRow 7 18, 65362987218028500⟩, ⟨.privateRow 7 20, 594400736416687200⟩, ⟨.privateRow 7 22, 1572708410922448800⟩, ⟨.privateRow 7 24, 2816187202150522200⟩, ⟨.privateRow 8 15, 6201573615285048⟩, ⟨.privateRow 8 16, 29600382001109920⟩, ⟨.privateRow 8 17, 54302626111283550⟩, ⟨.privateRow 8 18, 60017377307968080⟩, ⟨.privateRow 8 19, 330102976522879560⟩, ⟨.privateRow 8 20, 136217020462050528⟩, ⟨.privateRow 9 13, 5668072360030080⟩, ⟨.privateRow 9 14, 12753970227782784⟩, ⟨.privateRow 9 15, 25736888234337280⟩, ⟨.privateRow 9 16, 40411256640955200⟩, ⟨.privateRow 9 17, 54824816309440320⟩, ⟨.privateRow 9 18, 176122026195635520⟩, ⟨.privateRow 9 19, 119226529483117056⟩, ⟨.privateRow 9 20, 81644060807028720⟩, ⟨.privateRow 9 22, 252237294198489600⟩, ⟨.privateRow 10 10, 572311053800640⟩, ⟨.privateRow 10 11, 2705470436148480⟩, ⟨.privateRow 10 12, 6372389043820800⟩, ⟨.privateRow 10 13, 11172363142004064⟩, ⟨.privateRow 10 14, 18507877301833920⟩, ⟨.privateRow 10 15, 31159025989050960⟩, ⟨.privateRow 10 16, 37779962161930560⟩, ⟨.privateRow 10 17, 96095440453652640⟩, ⟨.privateRow 10 18, 86255316541570176⟩, ⟨.privateRow 10 21, 364254701448718080⟩, ⟨.privateRow 11 8, 607559648810400⟩, ⟨.privateRow 11 9, 1336180766104800⟩, ⟨.privateRow 11 11, 11729295038260800⟩, ⟨.privateRow 11 12, 5523668807136480⟩, ⟨.privateRow 11 13, 15337831134225600⟩, ⟨.privateRow 11 14, 22545586967904000⟩, ⟨.privateRow 11 15, 26703344564582400⟩, ⟨.privateRow 11 16, 56526227325968400⟩, ⟨.privateRow 11 17, 61539204428301600⟩, ⟨.privateRow 11 19, 45057013955553600⟩, ⟨.privateRow 11 21, 123488328619656000⟩, ⟨.privateRow 12 5, 60847464828150⟩, ⟨.privateRow 12 6, 286943834136960⟩, ⟨.privateRow 12 7, 695399598036000⟩, ⟨.privateRow 12 8, 681885759693600⟩, ⟨.privateRow 12 9, 584989661856600⟩, ⟨.privateRow 12 10, 8589682307606400⟩, ⟨.privateRow 12 11, 3207622145888160⟩, ⟨.privateRow 12 12, 9570487801274400⟩, ⟨.privateRow 12 13, 13200697369559700⟩, ⟨.privateRow 12 15, 57277746891565200⟩, ⟨.privateRow 13 2, 17079990127200⟩, ⟨.privateRow 13 3, 68721842629440⟩, ⟨.privateRow 13 4, 188306891152380⟩, ⟨.privateRow 13 5, 459110134619136⟩, ⟨.privateRow 13 6, 790559543030400⟩, ⟨.privateRow 13 8, 143471917068480⟩, ⟨.privateRow 13 9, 3415376934889920⟩, ⟨.privateRow 13 11, 39837368972681280⟩, ⟨.privateRow 13 12, 11490563358073800⟩, ⟨.privateRow 13 14, 42908351197551840⟩, ⟨.privateRow 13 16, 82885776089276160⟩, ⟨.privateRow 14 1, 69079071181120⟩, ⟨.privateRow 14 3, 727180579665540⟩, ⟨.privateRow 14 5, 1459119156580800⟩, ⟨.privateRow 14 8, 4174349587087680⟩, ⟨.privateRow 14 10, 40598756977018240⟩, ⟨.privateRow 14 13, 96587344169316000⟩, ⟨.privateRow 14 16, 107970588256090560⟩, ⟨.privateRow 15 0, 207237213543360⟩, ⟨.privateRow 15 2, 1272566014414695⟩, ⟨.privateRow 15 5, 310855820315040⟩, ⟨.privateRow 15 6, 5945117563525140⟩, ⟨.privateRow 15 7, 1667317581689760⟩, ⟨.privateRow 15 9, 47750907953949200⟩, ⟨.privateRow 15 10, 19253632370762790⟩, ⟨.privateRow 15 13, 42867017621444016⟩, ⟨.privateRow 16 0, 1312647476540400⟩, ⟨.privateRow 16 1, 1373871705856650⟩, ⟨.privateRow 16 3, 880229491198200⟩, ⟨.privateRow 16 5, 10241589080022300⟩, ⟨.privateRow 16 6, 4329777497245200⟩, ⟨.privateRow 16 8, 62837283677968800⟩, ⟨.privateRow 16 10, 98776022904187200⟩, ⟨.privateRow 17 0, 8659554994490400⟩, ⟨.privateRow 17 4, 20279641611028800⟩, ⟨.privateRow 17 6, 28065839777015040⟩, ⟨.privateRow 17 7, 81019882056713600⟩, ⟨.privateRow 17 8, 62393203934661600⟩, ⟨.privateRow 17 10, 283026823067788800⟩, ⟨.privateRow 18 0, 37042171655064576⟩, ⟨.privateRow 18 4, 96906274166782080⟩, ⟨.privateRow 18 5, 16306608174240384⟩, ⟨.privateRow 18 8, 896000666081938560⟩, ⟨.privateRow 19 0, 141712190085660480⟩, ⟨.privateRow 19 3, 469432659561465600⟩, ⟨.privateRow 19 5, 28687551417645120⟩, ⟨.privateRow 19 7, 1568540405331694080⟩, ⟨.privateRow 19 10, 3312279785392578000⟩, ⟨.privateRow 20 0, 1178396342847884160⟩, ⟨.privateRow 20 2, 1392650223365681280⟩, ⟨.privateRow 20 4, 1778628187893997440⟩, ⟨.privateRow 20 9, 35285688243703497600⟩, ⟨.privateRow 21 0, 18862065057101666400⟩, ⟨.privateRow 21 3, 12526897452371702400⟩, ⟨.privateRow 21 9, 393880080964267497600⟩, ⟨.privateRow 22 0, 489618263922608620800⟩, ⟨.privateRow 22 6, 347004621947835371520⟩, ⟨.privateRow 22 8, 975950499228286982400⟩, ⟨.privateRow 22 9, 6696104814149635684800⟩, ⟨.hall 16 3, 72955957829040⟩, ⟨.hall 11 6, 9988508158200⟩, ⟨.hall 17 6, 584641407512448⟩, ⟨.hall 18 6, 2629076298488640⟩, ⟨.hall 15 9, 7576391342520⟩, ⟨.hall 19 11, 158884900159265280⟩, ⟨.hall 13 13, 9250842949920⟩, ⟨.hall 18 13, 54355360580801280⟩, ⟨.hall 10 14, 1117914918120⟩, ⟨.hall 12 14, 9949226447160⟩, ⟨.hall 16 14, 4307573510079840⟩, ⟨.hall 11 15, 7206840519450⟩, ⟨.hall 15 16, 23314186523628000⟩, ⟨.hall 8 21, 264370793166480⟩, ⟨.hall 7 23, 2964787386254694⟩, ⟨.hall 6 24, 40795214819014656⟩, ⟨.hall 3 28, 48503724865861224960⟩]
  caps := #[0, 0, 89403161545152000, 7098218045755200, 0, 4763764519113600, 2981678276491200, 0, 3463467027294274, 452685833413632, 286095822273360, 12245718895200, 782891102448870, 0, 225811020825000, 5212212167976814, 3894210837252450, 180803895489360, 44757547752897408, 0, 619490620822993920, 10996894710097296000, 0] }

theorem case_54_32_14_checked :
    (Witness.linear .positive case_54_32_14).check 54 32 14 = true := by
  change case_54_32_14.check 54 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_32_15 : Certificate := {
  objectiveScale := 93027916800000
  eta := 1759668324366153801600
  rows := #[⟨.count 2, 376015560308733945600⟩, ⟨.count 3, 87525719375235261120⟩, ⟨.count 4, 19805116837077411840⟩, ⟨.count 5, 4476081587222044800⟩, ⟨.count 6, 1072573692744153600⟩, ⟨.count 7, 250521531553893600⟩, ⟨.count 8, 61719010142549760⟩, ⟨.count 9, 15914203164699840⟩, ⟨.count 10, 4024666764518400⟩, ⟨.count 11, 1229759289158400⟩, ⟨.count 12, 335388897043200⟩, ⟨.count 13, 218002783078080⟩, ⟨.path 13, 47922877684864⟩, ⟨.privateRow 2 30, 22767483988731081600⟩, ⟨.privateRow 6 21, 177833751751656000⟩, ⟨.privateRow 6 22, 308013709957873920⟩, ⟨.privateRow 6 23, 569290045476952800⟩, ⟨.privateRow 6 24, 844397446455763200⟩, ⟨.privateRow 7 18, 13784134305041100⟩, ⟨.privateRow 8 16, 9165536762622240⟩, ⟨.privateRow 8 17, 20410510565685240⟩, ⟨.privateRow 8 18, 30568834693837440⟩, ⟨.privateRow 8 19, 50973289626659400⟩, ⟨.privateRow 8 20, 77860905102908928⟩, ⟨.privateRow 8 21, 105125786506540800⟩, ⟨.privateRow 9 13, 402974841447360⟩, ⟨.privateRow 9 14, 4132363865902272⟩, ⟨.privateRow 9 15, 10135783716938880⟩, ⟨.privateRow 9 16, 18076064096890800⟩, ⟨.privateRow 9 17, 30319688656033920⟩, ⟨.privateRow 9 18, 44973166731292800⟩, ⟨.privateRow 9 19, 65962797653136384⟩, ⟨.privateRow 9 20, 91724670980102160⟩, ⟨.privateRow 9 22, 286407211901690880⟩, ⟨.privateRow 10 11, 429018297467760⟩, ⟨.privateRow 10 12, 1768414184409600⟩, ⟨.privateRow 10 13, 4410363996118080⟩, ⟨.privateRow 10 15, 31828406329399680⟩, ⟨.privateRow 10 16, 14210906694716160⟩, ⟨.privateRow 10 18, 107408294278084800⟩, ⟨.privateRow 11 9, 289165427258400⟩, ⟨.privateRow 11 10, 179339896335600⟩, ⟨.privateRow 11 11, 3272582571148800⟩, ⟨.privateRow 11 12, 3084180399059760⟩, ⟨.privateRow 11 13, 1145912064897600⟩, ⟨.privateRow 11 14, 22778495924184000⟩, ⟨.privateRow 11 15, 13002308847871200⟩, ⟨.privateRow 11 16, 5021517097396800⟩, ⟨.privateRow 11 17, 3040859333191680⟩, ⟨.privateRow 11 21, 787199664972520800⟩, ⟨.privateRow 12 7, 182667167139600⟩, ⟨.privateRow 12 8, 314964573184800⟩, ⟨.privateRow 12 9, 592753293732600⟩, ⟨.privateRow 12 10, 2901622124419200⟩, ⟨.privateRow 12 11, 3095360028961200⟩, ⟨.privateRow 12 12, 1305842881543200⟩, ⟨.privateRow 12 13, 17124048738096300⟩, ⟨.privateRow 12 14, 12960385235740800⟩, ⟨.privateRow 12 15, 6931370538892800⟩, ⟨.privateRow 12 16, 3957588985109760⟩, ⟨.privateRow 13 4, 13625173942380⟩, ⟨.privateRow 13 5, 82729261270656⟩, ⟨.privateRow 13 6, 246750402824640⟩, ⟨.privateRow 13 7, 389567103488640⟩, ⟨.privateRow 13 8, 648418534283520⟩, ⟨.privateRow 13 9, 3256321291292160⟩, ⟨.privateRow 13 10, 3169425077058240⟩, ⟨.privateRow 13 11, 1568874729502080⟩, ⟨.privateRow 13 12, 5154508111432680⟩, ⟨.privateRow 13 13, 32106299986949760⟩, ⟨.privateRow 13 14, 531032420318400⟩, ⟨.privateRow 13 16, 3370658415284160⟩, ⟨.privateRow 14 2, 17098257496320⟩, ⟨.privateRow 14 3, 49958971122060⟩, ⟨.privateRow 14 4, 148564859579136⟩, ⟨.privateRow 14 5, 327004174617120⟩, ⟨.privateRow 14 6, 486313900712640⟩, ⟨.privateRow 14 7, 876048220887840⟩, ⟨.privateRow 14 8, 3990111544823040⟩, ⟨.privateRow 14 9, 3892560804516384⟩, ⟨.privateRow 14 10, 2282300741360640⟩, ⟨.privateRow 14 11, 5113981953039960⟩, ⟨.privateRow 14 12, 27257268608032320⟩, ⟨.privateRow 14 13, 18106342261207200⟩, ⟨.privateRow 15 2, 180155077682580⟩, ⟨.privateRow 15 3, 276944276280672⟩, ⟨.privateRow 15 5, 1659709222451280⟩, ⟨.privateRow 15 7, 7352639320178880⟩, ⟨.privateRow 15 8, 4989235916056392⟩, ⟨.privateRow 15 10, 14311731318254370⟩, ⟨.privateRow 15 11, 23017460513327280⟩, ⟨.privateRow 15 13, 61430762018257632⟩, ⟨.privateRow 16 0, 64118465611200⟩, ⟨.privateRow 16 1, 334952192750175⟩, ⟨.privateRow 16 2, 96890125812480⟩, ⟨.privateRow 16 3, 603400560305400⟩, ⟨.privateRow 16 4, 3137283641091600⟩, ⟨.privateRow 16 6, 11552495966902800⟩, ⟨.privateRow 16 7, 10273381152554520⟩, ⟨.privateRow 16 9, 22061427475036950⟩, ⟨.privateRow 16 12, 124806593312200800⟩, ⟨.privateRow 16 15, 156734917583844600⟩, ⟨.privateRow 17 0, 1226265654814200⟩, ⟨.privateRow 17 2, 1401446462644800⟩, ⟨.privateRow 17 3, 6894105105888000⟩, ⟨.privateRow 17 4, 928530372369600⟩, ⟨.privateRow 17 5, 20699254150848000⟩, ⟨.privateRow 17 6, 23616968166792000⟩, ⟨.privateRow 17 7, 6163288558627200⟩, ⟨.privateRow 17 8, 25221710875561200⟩, ⟨.privateRow 17 9, 13979861010086400⟩, ⟨.privateRow 17 11, 84585079834295040⟩, ⟨.privateRow 17 13, 54096986911968000⟩, ⟨.privateRow 17 14, 421472047284288000⟩, ⟨.privateRow 18 0, 7906234266298368⟩, ⟨.privateRow 18 2, 18498560943582720⟩, ⟨.privateRow 18 3, 6382637037897120⟩, ⟨.privateRow 18 4, 46718657028126720⟩, ⟨.privateRow 18 6, 176426153534991360⟩, ⟨.privateRow 18 8, 68003026873816320⟩, ⟨.privateRow 18 9, 48041354048688000⟩, ⟨.privateRow 18 10, 116946381855663360⟩, ⟨.privateRow 18 11, 216803767771150560⟩, ⟨.privateRow 19 0, 63002804309565120⟩, ⟨.privateRow 19 2, 98827928328729600⟩, ⟨.privateRow 19 7, 411900686998669440⟩, ⟨.privateRow 20 0, 671649805218712320⟩, ⟨.privateRow 20 2, 324335292060648960⟩, ⟨.privateRow 20 10, 7776934393401613440⟩, ⟨.privateRow 20 12, 23330803180204840320⟩, ⟨.privateRow 21 0, 9466891967822889600⟩, ⟨.privateRow 21 10, 85554102205077105600⟩, ⟨.hall 21 3, 7199389969819931520⟩, ⟨.hall 16 5, 119948112484200⟩, ⟨.hall 21 6, 6251989511432246400⟩, ⟨.hall 17 11, 2267069235013440⟩, ⟨.hall 13 12, 1927138767840⟩, ⟨.hall 18 12, 376957955196725760⟩, ⟨.hall 12 14, 3449648442240⟩, ⟨.hall 14 14, 25350541496280⟩, ⟨.hall 7 17, 2856899437938⟩, ⟨.hall 11 17, 18621041868000⟩, ⟨.hall 8 18, 9523313064720⟩, ⟨.hall 11 20, 24441465872023200⟩, ⟨.hall 5 21, 68009142466720⟩, ⟨.hall 9 22, 440867976056988480⟩, ⟨.hall 3 28, 28428194369718823680⟩, ⟨.hall 2 29, 29183063669404444800⟩]
  caps := #[0, 0, 305237773975680, 12226895220787520, 6056548815000320, 0, 222235217358336, 214951922497312, 0, 167402768984048, 29058022958720, 33438139563700, 148468194124940, 0, 93027916800000, 662951502417204, 0, 6194336028284040, 0, 26471766516624000, 177705976486671360, 0, 0] }

theorem case_54_32_15_checked :
    (Witness.linear .positive case_54_32_15).check 54 32 15 = true := by
  change case_54_32_15.check 54 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_32_16 : Certificate := {
  objectiveScale := 8645364000000
  eta := 147871287761861664000
  rows := #[⟨.count 2, 30982555531056729600⟩, ⟨.count 3, 7029754076932947360⟩, ⟨.count 4, 1566422664010364160⟩, ⟨.count 5, 370604731232736000⟩, ⟨.count 6, 90107817005606400⟩, ⟨.count 7, 21618609321909600⟩, ⟨.count 8, 5821481725899840⟩, ⟨.count 9, 1635020873085600⟩, ⟨.count 10, 475134270811200⟩, ⟨.count 11, 153719911144800⟩, ⟨.count 12, 55898149507200⟩, ⟨.count 13, 36333797179680⟩, ⟨.path 13, 4116763827904⟩, ⟨.privateRow 2 30, 938865319122931200⟩, ⟨.privateRow 4 25, 58215826531142280⟩, ⟨.privateRow 4 26, 229157258812241760⟩, ⟨.privateRow 5 23, 39146840499102336⟩, ⟨.privateRow 5 24, 83180173010014080⟩, ⟨.privateRow 5 25, 167458434112569600⟩, ⟨.privateRow 6 20, 2428020414705600⟩, ⟨.privateRow 6 21, 16020513163855200⟩, ⟨.privateRow 6 22, 32030260758175680⟩, ⟨.privateRow 6 23, 59496592881726000⟩, ⟨.privateRow 6 24, 85222939829227200⟩, ⟨.privateRow 7 18, 2047560861896550⟩, ⟨.privateRow 7 19, 6181070972590800⟩, ⟨.privateRow 7 20, 12111265726560000⟩, ⟨.privateRow 7 21, 22130310298856760⟩, ⟨.privateRow 7 22, 30603654582801300⟩, ⟨.privateRow 7 23, 36424631672629200⟩, ⟨.privateRow 8 16, 1119394948912240⟩, ⟨.privateRow 8 17, 2565443630724975⟩, ⟨.privateRow 8 18, 4645679678279640⟩, ⟨.privateRow 8 19, 8453158841066940⟩, ⟨.privateRow 8 20, 11655680280812568⟩, ⟨.privateRow 8 21, 13488669884920230⟩, ⟨.privateRow 8 22, 12429522875930160⟩, ⟨.privateRow 9 13, 54684199795680⟩, ⟨.privateRow 9 14, 468302274760320⟩, ⟨.privateRow 9 15, 1127244843364640⟩, ⟨.privateRow 9 16, 1915093893012300⟩, ⟨.privateRow 9 17, 3369815506680480⟩, ⟨.privateRow 9 18, 4718683696686960⟩, ⟨.privateRow 9 19, 5486403374131680⟩, ⟨.privateRow 9 20, 2561532701167440⟩, ⟨.privateRow 10 11, 48212153949960⟩, ⟨.privateRow 10 12, 205806823185600⟩, ⟨.privateRow 10 13, 486872882207712⟩, ⟨.privateRow 10 14, 860831502410880⟩, ⟨.privateRow 10 15, 1470470695473780⟩, ⟨.privateRow 10 16, 2064238806801600⟩, ⟨.privateRow 10 17, 986602338802080⟩, ⟨.privateRow 11 9, 29919842845200⟩, ⟨.privateRow 11 10, 100150851200400⟩, ⟨.privateRow 11 11, 222957391784400⟩, ⟨.privateRow 11 12, 402000858539280⟩, ⟨.privateRow 11 13, 720982613551200⟩, ⟨.privateRow 11 14, 307148686094250⟩, ⟨.privateRow 12 7, 16469990479800⟩, ⟨.privateRow 12 8, 53210738473200⟩, ⟨.privateRow 12 9, 114319479374100⟩, ⟨.privateRow 12 10, 204959881526400⟩, ⟨.privateRow 12 11, 84778860085920⟩, ⟨.privateRow 13 5, 8943703921152⟩, ⟨.privateRow 13 6, 30344709732480⟩, ⟨.privateRow 13 7, 66432800760480⟩, ⟨.privateRow 13 8, 5123997038160⟩, ⟨.privateRow 14 3, 4794042683430⟩, ⟨.privateRow 14 4, 17494050493920⟩, ⟨.privateRow 15 0, 392494722620⟩, ⟨.privateRow 15 1, 2493495884880⟩, ⟨.privateRow 15 2, 883113125895⟩, ⟨.privateRow 16 0, 890534244600⟩, ⟨.hall 7 24, 10516817593658376⟩, ⟨.hall 6 25, 76412770376342400⟩, ⟨.hall 5 26, 237461550012086400⟩, ⟨.hall 4 27, 567819391781584800⟩, ⟨.hall 3 28, 1139992932745386720⟩, ⟨.hall 2 29, 1734292881157636800⟩, ⟨.assumptionRow 16, 12812176571103⟩]
  caps := #[0, 173362358845222365, 34667121862081800, 4317937566531680, 0, 165519053444160, 25534599122058, 690716772460, 65265833991358, 0, 0, 0, 2338746518285, 0, 53034701910645, 28782342270682, 0, 8645364000000, 0, 0, 0, 0, 0] }

theorem case_54_32_16_checked :
    (Witness.linear .conditional case_54_32_16).check 54 32 16 = true := by
  change case_54_32_16.check 54 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_32_17 : Certificate := {
  objectiveScale := 51872184000000
  eta := 1128750829915544035200
  rows := #[⟨.count 2, 228613705206433747200⟩, ⟨.count 3, 50628312333704064960⟩, ⟨.count 4, 10880954908993128960⟩, ⟨.count 5, 2437755565441996800⟩, ⟨.count 6, 565353884115820800⟩, ⟨.count 7, 131619180283390800⟩, ⟨.count 8, 31198620511618560⟩, ⟨.count 9, 7848100190810880⟩, ⟨.count 10, 2180027830780800⟩, ⟨.count 11, 768599555724000⟩, ⟨.count 12, 335388897043200⟩, ⟨.count 13, 218002783078080⟩, ⟨.path 11, 62487355615776⟩, ⟨.privateRow 2 30, 9153936861448579200⟩, ⟨.privateRow 4 25, 447505212963528720⟩, ⟨.privateRow 4 26, 1771490615292478080⟩, ⟨.privateRow 5 23, 273918074684462208⟩, ⟨.privateRow 5 24, 628586802474190560⟩, ⟨.privateRow 5 25, 1337196774692338560⟩, ⟨.privateRow 6 20, 11661418713859200⟩, ⟨.privateRow 6 21, 109041762424795200⟩, ⟨.privateRow 6 22, 234522549529107840⟩, ⟨.privateRow 6 23, 470098779176426400⟩, ⟨.privateRow 6 24, 726352976507558400⟩, ⟨.privateRow 7 18, 9900959731462800⟩, ⟨.privateRow 7 19, 39863366048563200⟩, ⟨.privateRow 7 20, 86671245355695000⟩, ⟨.privateRow 7 21, 172385700718991760⟩, ⟨.privateRow 7 22, 262057512158442000⟩, ⟨.privateRow 7 23, 344232450113151600⟩, ⟨.privateRow 8 16, 5114991225183840⟩, ⟨.privateRow 8 17, 15482739323191140⟩, ⟨.privateRow 8 18, 32240189364102720⟩, ⟨.privateRow 8 19, 65117229450993720⟩, ⟨.privateRow 8 20, 99784718321127840⟩, ⟨.privateRow 8 21, 129838824221586480⟩, ⟨.privateRow 8 22, 140181845152068720⟩, ⟨.privateRow 9 14, 2189716843362048⟩, ⟨.privateRow 9 15, 6305932354962240⟩, ⟨.privateRow 9 16, 12716829012888000⟩, ⟨.privateRow 9 17, 25506325620135360⟩, ⟨.privateRow 9 18, 40229587655056800⟩, ⟨.privateRow 9 19, 53013432338298432⟩, ⟨.privateRow 9 20, 57928183970136480⟩, ⟨.privateRow 9 21, 27395683073478720⟩, ⟨.privateRow 10 12, 852192697487040⟩, ⟨.privateRow 10 13, 2627772008333472⟩, ⟨.privateRow 10 14, 5377401982592640⟩, ⟨.privateRow 10 15, 10745021789021520⟩, ⟨.privateRow 10 16, 17296484547513600⟩, ⟨.privateRow 10 17, 23686840853676000⟩, ⟨.privateRow 10 18, 14998591475771904⟩, ⟨.privateRow 11 10, 315591635759400⟩, ⟨.privateRow 11 11, 1109070102722400⟩, ⟨.privateRow 11 12, 2414800058711040⟩, ⟨.privateRow 11 13, 4951644410512800⟩, ⟨.privateRow 11 14, 8178597999772200⟩, ⟨.privateRow 11 15, 7570206533260800⟩, ⟨.privateRow 12 8, 112871263428000⟩, ⟨.privateRow 12 9, 472805181248400⟩, ⟨.privateRow 12 10, 1137019177476000⟩, ⟨.privateRow 12 11, 2488865106808080⟩, ⟨.privateRow 12 12, 3277805378047200⟩, ⟨.privateRow 13 6, 39527977151520⟩, ⟨.privateRow 13 7, 205103210114880⟩, ⟨.privateRow 13 8, 557584041334320⟩, ⟨.privateRow 13 9, 1298869728549120⟩, ⟨.privateRow 14 4, 12918683441664⟩, ⟨.privateRow 14 5, 91699583358240⟩, ⟨.privateRow 14 6, 283217290836480⟩, ⟨.privateRow 14 7, 145335188718720⟩, ⟨.privateRow 15 0, 2354968335720⟩, ⟨.privateRow 15 3, 42389430042960⟩, ⟨.privateRow 15 4, 69639777927720⟩, ⟨.privateRow 16 1, 17031467427975⟩, ⟨.hall 7 24, 211429999168275888⟩, ⟨.hall 6 25, 846242085389500800⟩, ⟨.hall 5 26, 2244980100306944000⟩, ⟨.hall 4 27, 4938572761341373440⟩, ⟨.hall 3 28, 9455021256891450240⟩, ⟨.hall 2 29, 14333343871943416320⟩, ⟨.assumptionRow 17, 60204412915920⟩]
  caps := #[0, 1168378046822553840, 0, 84973190849623440, 6620534480549808, 0, 692082698737248, 198641091790440, 0, 0, 120983143578336, 0, 206213062482000, 0, 99218515005792, 0, 387057292119225, 666006163084080, 51872184000000, 0, 0, 0, 0] }

theorem case_54_32_17_checked :
    (Witness.linear .conditional case_54_32_17).check 54 32 17 = true := by
  change case_54_32_17.check 54 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_32_18 : Certificate := {
  objectiveScale := 74723123102628000000
  eta := 900460370757366893145672000
  rows := #[⟨.count 2, 207479348100775781830800000⟩, ⟨.count 3, 47305291366976878257422400⟩, ⟨.count 4, 10727774293379059372135680⟩, ⟨.count 5, 2426659042114336629600000⟩, ⟨.count 6, 592675784874042687417600⟩, ⟨.count 7, 146884244372685434815200⟩, ⟨.count 8, 37970076776612561380800⟩, ⟨.count 9, 10277614766601896313600⟩, ⟨.count 10, 3359989442927543025600⟩, ⟨.count 11, 1268231309340298102800⟩, ⟨.count 12, 592939313457801710400⟩, ⟨.count 13, 256940369165047407840⟩, ⟨.path 10, 28540868462432726400⟩, ⟨.path 11, 41450199144415759152⟩, ⟨.privateRow 2 30, 23790965248888956316598400⟩, ⟨.privateRow 3 27, 1327867827844965003717120⟩, ⟨.privateRow 4 25, 786237529645045067990400⟩, ⟨.privateRow 4 26, 2524696067415755829435840⟩, ⟨.privateRow 5 23, 333325886024825279441856⟩, ⟨.privateRow 5 24, 859279966812686600541360⟩, ⟨.privateRow 5 25, 1951033869859926650198400⟩, ⟨.privateRow 6 21, 123616866498295030660800⟩, ⟨.privateRow 6 22, 300391840483847647254720⟩, ⟨.privateRow 6 23, 673968862784872964509200⟩, ⟨.privateRow 6 24, 1147191166772091296856000⟩, ⟨.privateRow 7 18, 2101022810360023074525⟩, ⟨.privateRow 7 19, 40529284421867597070000⟩, ⟨.privateRow 7 20, 106541037797534588348100⟩, ⟨.privateRow 7 21, 240003716497584699539880⟩, ⟨.privateRow 7 22, 413138701919965811189400⟩, ⟨.privateRow 7 23, 608984361083546390943000⟩, ⟨.privateRow 8 16, 1165747971211789165200⟩, ⟨.privateRow 8 17, 13551820165337049045450⟩, ⟨.privateRow 8 18, 37320588621223135988760⟩, ⟨.privateRow 8 19, 88297082048070087912720⟩, ⟨.privateRow 8 20, 155217677012605139076144⟩, ⟨.privateRow 8 21, 231230273475469851593010⟩, ⟨.privateRow 8 22, 291137229038921402657520⟩, ⟨.privateRow 9 14, 376845874775402864832⟩, ⟨.privateRow 9 15, 4612238231678752234560⟩, ⟨.privateRow 9 16, 13393016742728096133660⟩, ⟨.privateRow 9 17, 33149386040849290967040⟩, ⟨.privateRow 9 18, 61275519890879268854880⟩, ⟨.privateRow 9 19, 93377839940559673507008⟩, ⟨.privateRow 9 20, 120226681071811766251800⟩, ⟨.privateRow 9 21, 121780218674263395486240⟩, ⟨.privateRow 10 12, 53903573950709246400⟩, ⟨.privateRow 10 13, 1545595143746669791776⟩, ⟨.privateRow 10 14, 4945553088544331303040⟩, ⟨.privateRow 10 15, 12935959355271040648560⟩, ⟨.privateRow 10 16, 25284626438164830079200⟩, ⟨.privateRow 10 17, 40458225821604003372960⟩, ⟨.privateRow 10 18, 54178841535017534951616⟩, ⟨.privateRow 10 19, 47044793361931084039320⟩, ⟨.privateRow 11 11, 449196449589243720000⟩, ⟨.privateRow 11 12, 1852935354555630345000⟩, ⟨.privateRow 11 13, 5274231794399334967200⟩, ⟨.privateRow 11 14, 11041435896090939489150⟩, ⟨.privateRow 11 15, 18797587996882451842800⟩, ⟨.privateRow 11 16, 26822268665723057927400⟩, ⟨.privateRow 11 17, 2470580472740840460000⟩, ⟨.privateRow 12 9, 108431031859181331300⟩, ⟨.privateRow 12 10, 652832173403034206400⟩, ⟨.privateRow 12 11, 2226816532763744201280⟩, ⟨.privateRow 12 12, 5127827025644322199200⟩, ⟨.privateRow 12 13, 9439676222930627924250⟩, ⟨.privateRow 12 14, 5715276160273810930800⟩, ⟨.privateRow 13 7, 21285000995921087040⟩, ⟨.privateRow 13 8, 212469920655712279560⟩, ⟨.privateRow 13 9, 916360757162057188800⟩, ⟨.privateRow 13 10, 2512086224682886579728⟩, ⟨.privateRow 13 11, 3884850538914263798880⟩, ⟨.privateRow 14 6, 65882145939755745600⟩, ⟨.privateRow 14 7, 363998856317150494440⟩, ⟨.privateRow 14 8, 1225008628746488651520⟩, ⟨.privateRow 14 9, 622366671977559276768⟩, ⟨.privateRow 15 4, 10705848715210308660⟩, ⟨.privateRow 15 5, 142195631653306150920⟩, ⟨.privateRow 15 6, 453809031650303639310⟩, ⟨.privateRow 16 3, 45882208779472751400⟩, ⟨.privateRow 16 4, 98823218909633618400⟩, ⟨.privateRow 17 1, 19032619938151659840⟩, ⟨.privateRow 17 2, 20392092790876778400⟩, ⟨.hall 8 23, 97489837478197339615440⟩, ⟨.hall 7 24, 614785503640695016862232⟩, ⟨.hall 6 25, 1763269753931622775238400⟩, ⟨.hall 5 26, 4024658959477036824944000⟩, ⟨.hall 4 27, 8045830720034294529101760⟩, ⟨.hall 3 28, 14494936525936956344455200⟩, ⟨.hall 2 29, 21799163507121508811022720⟩, ⟨.assumptionRow 18, 67622524364744818560⟩]
  caps := #[0, 2848864258606396188347280, 441901357915496514890400, 44215954243658333856720, 0, 2550234367617185104128, 1623128922379409150160, 923586237706505270430, 0, 0, 191911650372023372232, 1575735540912947232, 0, 33339601974032214336, 128144449991606455680, 563970469831369675620, 609040335621064247160, 67622524364744818560, 903778075969419181440, 74723123102628000000, 0, 0, 0] }

theorem case_54_32_18_checked :
    (Witness.linear .conditional case_54_32_18).check 54 32 18 = true := by
  change case_54_32_18.check 54 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_32_19 : Certificate := {
  objectiveScale := 4750842206682000000
  eta := 66808350088449801749517600
  rows := #[⟨.count 2, 14491634467346493069412800⟩, ⟨.count 3, 3067502361920700405221520⟩, ⟨.count 4, 632350013158963597417920⟩, ⟨.count 5, 133652913396451155907200⟩, ⟨.count 6, 28526969191914237844800⟩, ⟨.count 7, 6024098719366415988300⟩, ⟨.count 8, 1275917559699936273120⟩, ⟨.count 9, 276705012946974131520⟩, ⟨.count 10, 106425004979605435200⟩, ⟨.count 11, 34841519487370827000⟩, ⟨.count 12, 22805358209915450400⟩, ⟨.count 13, 9882321890963361840⟩, ⟨.path 10, 8772369643125950400⟩, ⟨.privateRow 2 30, 1670474751375476807560800⟩, ⟨.privateRow 3 27, 97533026884980068382000⟩, ⟨.privateRow 4 25, 55397825940267865634580⟩, ⟨.privateRow 4 26, 168783469683060244652640⟩, ⟨.privateRow 5 23, 22310329901038885689984⟩, ⟨.privateRow 5 24, 55887824400694798992480⟩, ⟨.privateRow 5 25, 131898252242922327882720⟩, ⟨.privateRow 6 20, 384312517981908516000⟩, ⟨.privateRow 6 21, 7375140226033768188000⟩, ⟨.privateRow 6 22, 18881823026333996688960⟩, ⟨.privateRow 6 23, 44412801631637842002600⟩, ⟨.privateRow 6 24, 80493341861506019846400⟩, ⟨.privateRow 7 18, 257352132577170881250⟩, ⟨.privateRow 7 19, 2305875107891451096000⟩, ⟨.privateRow 7 20, 6303411567256838784750⟩, ⟨.privateRow 7 21, 15336540047950890628860⟩, ⟨.privateRow 7 22, 28443587100959234479275⟩, ⟨.privateRow 7 23, 45443582706653603772300⟩, ⟨.privateRow 8 16, 94370073860001980040⟩, ⟨.privateRow 8 17, 727791830928239252175⟩, ⟨.privateRow 8 18, 2094777731942817061140⟩, ⟨.privateRow 8 19, 5386780460379751032600⟩, ⟨.privateRow 8 20, 10420633925079449411340⟩, ⟨.privateRow 8 21, 17038015094080436671215⟩, ⟨.privateRow 8 22, 23798552676029684853300⟩, ⟨.privateRow 9 14, 21521501006986876896⟩, ⟨.privateRow 9 15, 225341339908757152080⟩, ⟨.privateRow 9 16, 705762488379633424740⟩, ⟨.privateRow 9 17, 1926425319728905504080⟩, ⟨.privateRow 9 18, 3957869917330826416920⟩, ⟨.privateRow 9 19, 6724371028917736434240⟩, ⟨.privateRow 9 20, 9701969516453280486420⟩, ⟨.privateRow 9 21, 11414813807906457989040⟩, ⟨.privateRow 10 13, 63931020848462979288⟩, ⟨.privateRow 10 14, 238358225438449633440⟩, ⟨.privateRow 10 15, 708106372417874734920⟩, ⟨.privateRow 10 16, 1559886501558216807360⟩, ⟨.privateRow 10 17, 2804298881212603217520⟩, ⟨.privateRow 10 18, 4238147769730687302336⟩, ⟨.privateRow 10 19, 5320300025721525282900⟩, ⟨.privateRow 10 20, 3607047490201627071600⟩, ⟨.privateRow 11 11, 10538839778824564200⟩, ⟨.privateRow 11 12, 77284825044713470800⟩, ⟨.privateRow 11 13, 265640191000681820400⟩, ⟨.privateRow 11 14, 641954996554807487475⟩, ⟨.privateRow 11 15, 1238548144686122437200⟩, ⟨.privateRow 11 16, 1994413039746772491000⟩, ⟨.privateRow 11 17, 2698380661970995903440⟩, ⟨.privateRow 11 18, 85044981657809700450⟩, ⟨.privateRow 12 9, 475111629373238550⟩, ⟨.privateRow 12 10, 18716518732885155000⟩, ⟨.privateRow 12 11, 98443129606135027560⟩, ⟨.privateRow 12 12, 274368167599538350800⟩, ⟨.privateRow 12 13, 581457449081281778775⟩, ⟨.privateRow 12 14, 1013661973449456190200⟩, ⟨.privateRow 12 15, 691656952005352386900⟩, ⟨.privateRow 13 8, 2217187603741779900⟩, ⟨.privateRow 13 9, 29992501403343349920⟩, ⟨.privateRow 13 10, 118435826970160905744⟩, ⟨.privateRow 13 11, 288445549210597270800⟩, ⟨.privateRow 13 12, 523287948591684938970⟩, ⟨.privateRow 14 7, 5947693730672393700⟩, ⟨.privateRow 14 8, 44021252059745884560⟩, ⟨.privateRow 14 9, 146697578292522793536⟩, ⟨.privateRow 14 10, 138352506473487065760⟩, ⟨.privateRow 15 5, 591250027664474640⟩, ⟨.privateRow 15 6, 11849635971108845910⟩, ⟨.privateRow 15 7, 66031878089618826840⟩, ⟨.privateRow 15 8, 28054813812679321668⟩, ⟨.privateRow 16 4, 2533928689990605600⟩, ⟨.privateRow 16 5, 22646987666791037550⟩, ⟨.privateRow 16 6, 5240625245207843400⟩, ⟨.privateRow 17 3, 6757143173308281600⟩, ⟨.privateRow 17 4, 915029804718829800⟩, ⟨.privateRow 18 1, 2666658288037732560⟩, ⟨.hall 8 23, 16795738077536008510920⟩, ⟨.hall 7 24, 60046140747047332265388⟩, ⟨.hall 6 25, 147418903326273452596800⟩, ⟨.hall 5 26, 309008411812941282041600⟩, ⟨.hall 4 27, 585334160882570334652560⟩, ⟨.hall 3 28, 1020556241692516206437760⟩, ⟨.hall 2 29, 1515131239464126735010560⟩, ⟨.assumptionRow 19, 2788839392166467640⟩]
  caps := #[0, 84551050666345220357400, 12842322205431184666200, 704663604605182931280, 567010808859496021020, 0, 26081605742724908640, 29594928486504267810, 3464886085807467552, 2529710649248087448, 3148700513535930276, 3561384788420002650, 7857091626689771235, 656376359275185120, 6404515361983870560, 26318678774488287012, 10605442655212634250, 41225353391021461200, 2788839392166467640, 54221267088017532360, 4750842206682000000, 0, 0] }

theorem case_54_32_19_checked :
    (Witness.linear .conditional case_54_32_19).check 54 32 19 = true := by
  change case_54_32_19.check 54 32 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_32_20 : Certificate := {
  objectiveScale := 214687569096000000
  eta := 5864601150110791920031200
  rows := #[⟨.count 2, 995180690769057530337600⟩, ⟨.count 3, 179011977552199917805680⟩, ⟨.count 4, 35656470453424190610240⟩, ⟨.count 5, 7848465224359878518400⟩, ⟨.count 6, 1907517085173764064000⟩, ⟨.count 7, 468067371715192649400⟩, ⟨.count 8, 112239411098630175360⟩, ⟨.count 9, 26124690514336333920⟩, ⟨.count 10, 5741690222931062400⟩, ⟨.count 11, 877202672947801200⟩, ⟨.path 5, 149749018400107526400⟩, ⟨.path 12, 128813447434322560⟩, ⟨.privateRow 2 30, 112510333815075144748800⟩, ⟨.privateRow 3 29, 173520401735035535740560⟩, ⟨.privateRow 4 25, 3333541610451357084780⟩, ⟨.privateRow 4 26, 10584853773391937959920⟩, ⟨.privateRow 5 23, 1346458255556350416480⟩, ⟨.privateRow 5 24, 3546495850259025944280⟩, ⟨.privateRow 5 25, 8598064148482872903840⟩, ⟨.privateRow 6 21, 451192296052272574800⟩, ⟨.privateRow 6 22, 1184733980943792158880⟩, ⟨.privateRow 6 23, 2878381079883128219400⟩, ⟨.privateRow 6 24, 5390348400832817822400⟩, ⟨.privateRow 7 18, 4924296823138793100⟩, ⟨.privateRow 7 19, 137695187107166703300⟩, ⟨.privateRow 7 20, 393641376747928258950⟩, ⟨.privateRow 7 21, 981334604796459273360⟩, ⟨.privateRow 7 22, 1884968989194128537700⟩, ⟨.privateRow 7 23, 3134012558824666619100⟩, ⟨.privateRow 8 16, 3064006912175249040⟩, ⟨.privateRow 8 17, 42150252982621353570⟩, ⟨.privateRow 8 18, 128619177373491845040⟩, ⟨.privateRow 8 19, 340225714892722719060⟩, ⟨.privateRow 8 20, 679387090542268772664⟩, ⟨.privateRow 8 21, 1159283141573674817700⟩, ⟨.privateRow 8 22, 1708103221776854622720⟩, ⟨.privateRow 9 14, 1271678056782509376⟩, ⟨.privateRow 9 15, 13031628395893227120⟩, ⟨.privateRow 9 16, 42219365920489968210⟩, ⟨.privateRow 9 17, 119022352286592783600⟩, ⟨.privateRow 9 18, 253010946714020094600⟩, ⟨.privateRow 9 19, 448542966767309013600⟩, ⟨.privateRow 9 20, 684269919602686396980⟩, ⟨.privateRow 9 21, 870247075995639342000⟩, ⟨.privateRow 10 12, 434976532040232000⟩, ⟨.privateRow 10 13, 4014398414199301128⟩, ⟨.privateRow 10 14, 13976762588968299120⟩, ⟨.privateRow 10 15, 42374870030694351150⟩, ⟨.privateRow 10 16, 97007223385520997120⟩, ⟨.privateRow 10 17, 182450181403388578680⟩, ⟨.privateRow 10 18, 291524751585619808256⟩, ⟨.privateRow 10 19, 393808178165284242360⟩, ⟨.privateRow 10 20, 408951886128264919440⟩, ⟨.privateRow 11 10, 126264021106122900⟩, ⟨.privateRow 11 11, 1203435071977975200⟩, ⟨.privateRow 11 12, 4633225027115204520⟩, ⟨.privateRow 11 13, 15390919625356875600⟩, ⟨.privateRow 11 14, 38472314957295894675⟩, ⟨.privateRow 11 15, 78014076679825228800⟩, ⟨.privateRow 11 16, 132962659699542472800⟩, ⟨.privateRow 11 17, 192657630688599356280⟩, ⟨.privateRow 11 18, 136235556036109079550⟩, ⟨.privateRow 12 8, 30671422131042000⟩, ⟨.privateRow 12 9, 338919214548014100⟩, ⟨.privateRow 12 10, 1511543448839806200⟩, ⟨.privateRow 12 11, 5677893664898495040⟩, ⟨.privateRow 12 12, 15811799695710618600⟩, ⟨.privateRow 12 13, 35172836721549051525⟩, ⟨.privateRow 12 14, 65015527980689629200⟩, ⟨.privateRow 12 15, 102174174974033662500⟩, ⟨.privateRow 12 16, 19426051920916761120⟩, ⟨.privateRow 13 6, 6835345503489360⟩, ⟨.privateRow 13 7, 84653125081675920⟩, ⟨.privateRow 13 8, 466512330613148820⟩, ⟨.privateRow 13 10, 10890072456159248352⟩, ⟨.privateRow 13 11, 14641310068474209120⟩, ⟨.privateRow 13 12, 34133152189862055330⟩, ⟨.privateRow 13 13, 44074307806499393280⟩, ⟨.privateRow 14 5, 14809915257560280⟩, ⟨.privateRow 14 6, 127593116065134720⟩, ⟨.privateRow 14 7, 742964082087607380⟩, ⟨.privateRow 14 8, 332998700639688720⟩, ⟨.privateRow 14 9, 12772070918119985472⟩, ⟨.privateRow 14 10, 18061514429664625920⟩, ⟨.privateRow 14 11, 19101088203438371130⟩, ⟨.privateRow 15 4, 25917351700730490⟩, ⟨.privateRow 15 5, 232591617827068500⟩, ⟨.privateRow 15 6, 1219555382806595835⟩, ⟨.privateRow 15 7, 791657288313222240⟩, ⟨.privateRow 15 8, 16424689684476269196⟩, ⟨.privateRow 15 10, 6077618973821299905⟩, ⟨.privateRow 16 3, 55537182215851050⟩, ⟨.privateRow 16 4, 458537760859077900⟩, ⟨.privateRow 16 5, 2224572687646033725⟩, ⟨.privateRow 16 6, 1743530932594596600⟩, ⟨.privateRow 16 7, 23947632971474972760⟩, ⟨.privateRow 16 8, 9387840727153488600⟩, ⟨.privateRow 16 10, 1962313771626737100⟩, ⟨.privateRow 17 2, 98732768383735200⟩, ⟨.privateRow 17 3, 1010112168848983200⟩, ⟨.privateRow 17 4, 4665123306131488200⟩, ⟨.privateRow 17 5, 4398096046184568000⟩, ⟨.privateRow 17 6, 41053085093957096160⟩, ⟨.privateRow 17 7, 33865339555621173600⟩, ⟨.privateRow 17 10, 921505838248195200⟩, ⟨.privateRow 17 11, 276451751474458560⟩, ⟨.privateRow 17 12, 1209476412700756200⟩, ⟨.privateRow 18 1, 335691412504699680⟩, ⟨.privateRow 18 2, 2711353716384112800⟩, ⟨.privateRow 18 3, 11749199437664488800⟩, ⟨.privateRow 18 4, 13458173901324778080⟩, ⟨.privateRow 18 5, 86474107861210637568⟩, ⟨.privateRow 18 6, 109920288072372217440⟩, ⟨.privateRow 18 7, 46703067764716342980⟩, ⟨.privateRow 18 10, 939935955013159104⟩, ⟨.privateRow 19 0, 1510611356271148560⟩, ⟨.privateRow 19 1, 8947467264067572240⟩, ⟨.privateRow 19 2, 37891168186467976380⟩, ⟨.privateRow 19 3, 51910099333681286880⟩, ⟨.privateRow 19 5, 867090918499639273440⟩, ⟨.privateRow 20 0, 56667292672427957520⟩, ⟨.privateRow 20 1, 161845222253828333220⟩, ⟨.privateRow 20 2, 267881747178750344640⟩, ⟨.privateRow 20 3, 120546786230437655088⟩, ⟨.privateRow 20 4, 2604405875348961684000⟩, ⟨.privateRow 20 5, 2620218339592151808510⟩, ⟨.privateRow 21 0, 1897495709182814941200⟩, ⟨.privateRow 21 1, 1643819812233240751200⟩, ⟨.privateRow 21 2, 1674260919867189654000⟩, ⟨.privateRow 21 10, 210287171535319020542400⟩, ⟨.privateRow 22 0, 77990117758177088973600⟩, ⟨.privateRow 22 10, 4866071937502000010385600⟩, ⟨.hall 18 5, 697205241355914720⟩, ⟨.hall 19 8, 4266958676895401760⟩, ⟨.hall 14 10, 2788888204248510⟩, ⟨.hall 16 15, 1036694068029219600⟩, ⟨.hall 9 18, 5992978397962608⟩, ⟨.hall 8 23, 1337559964805766281580⟩, ⟨.hall 7 24, 3892651455220875799452⟩, ⟨.hall 6 25, 9162780647427487080000⟩, ⟨.hall 5 26, 14391028689000085522400⟩, ⟨.hall 3 28, 64104563964956300145360⟩]
  caps := #[0, 0, 0, 247181061887198559120, 0, 0, 7749608125823363800, 365852726151269500, 171906962734707200, 922410185400200068, 0, 346800016356705210, 186369666299016340, 470703837630087864, 2144779931356920, 123144117379461360, 0, 3315931138629036720, 34887637108307854884, 176588378253285228360, 249365133668838569382, 0, 0] }

theorem case_54_32_20_checked :
    (Witness.linear .conditional case_54_32_20).check 54 32 20 = true := by
  change case_54_32_20.check 54 32 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_33_1_checked :
    (Witness.rising).check 54 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_33_2_checked :
    (Witness.rising).check 54 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_33_3_checked :
    (Witness.rising).check 54 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_33_4_checked :
    (Witness.rising).check 54 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_33_5_checked :
    (Witness.rising).check 54 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_33_6_checked :
    (Witness.rising).check 54 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_33_7_checked :
    (Witness.rising).check 54 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_33_8_checked :
    (Witness.rising).check 54 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_33_9_checked :
    (Witness.rising).check 54 33 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_33_10_checked :
    (Witness.rising).check 54 33 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_33_11_checked :
    (Witness.linear .positive case_54_33_11).check 54 33 11 = true := by
  change case_54_33_11.check 54 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_33_12_checked :
    (Witness.linear .positive case_54_33_12).check 54 33 12 = true := by
  change case_54_33_12.check 54 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_33_13_checked :
    (Witness.linear .positive case_54_33_13).check 54 33 13 = true := by
  change case_54_33_13.check 54 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_33_14_checked :
    (Witness.linear .positive case_54_33_14).check 54 33 14 = true := by
  change case_54_33_14.check 54 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_33_15 : Certificate := {
  objectiveScale := 2511366137280000
  eta := 91723855649693447980800
  rows := #[⟨.count 2, 19545345156767137868160⟩, ⟨.count 3, 3925245186662274034560⟩, ⟨.count 4, 854864874307788664320⟩, ⟨.count 5, 175605117374425939200⟩, ⟨.count 6, 39275744737318689600⟩, ⟨.count 7, 8354871882607330080⟩, ⟨.count 8, 1949332441221285120⟩, ⟨.count 9, 434596932788578560⟩, ⟨.count 10, 104836979400753600⟩, ⟨.count 11, 28591903472932800⟩, ⟨.count 12, 11436761389173120⟩, ⟨.path 11, 884551264012416⟩, ⟨.path 12, 2366742238468608⟩, ⟨.privateRow 2 31, 2040975845608362062400⟩, ⟨.privateRow 5 23, 8904154117104005760⟩, ⟨.privateRow 5 27, 746726483119360423680⟩, ⟨.privateRow 6 21, 6156562961302696800⟩, ⟨.privateRow 6 22, 11455425548384617800⟩, ⟨.privateRow 6 23, 19026641009971314720⟩, ⟨.privateRow 6 25, 109161240061187714400⟩, ⟨.privateRow 6 26, 94126531781747064600⟩, ⟨.privateRow 7 18, 465765637438701600⟩, ⟨.privateRow 7 20, 10239895233001399680⟩, ⟨.privateRow 7 21, 6202483978758827760⟩, ⟨.privateRow 7 22, 15707819929959821664⟩, ⟨.privateRow 7 23, 14940063784148302800⟩, ⟨.privateRow 7 24, 45896041142568096480⟩, ⟨.privateRow 7 26, 282785362108694565120⟩, ⟨.privateRow 8 16, 372314236390039944⟩, ⟨.privateRow 8 17, 650465804009221200⟩, ⟨.privateRow 8 18, 1717797589556098050⟩, ⟨.privateRow 8 19, 5302255039120971360⟩, ⟨.privateRow 8 20, 5259824805647051640⟩, ⟨.privateRow 8 21, 9525710329823928240⟩, ⟨.privateRow 8 22, 10876717479897048780⟩, ⟨.privateRow 8 23, 18378928500370598160⟩, ⟨.privateRow 8 24, 12502365747218507160⟩, ⟨.privateRow 9 13, 25520921248062240⟩, ⟨.privateRow 9 14, 181370862434361600⟩, ⟨.privateRow 9 15, 390501863876988864⟩, ⟨.privateRow 9 16, 678581175757605120⟩, ⟨.privateRow 9 17, 1262173694421800160⟩, ⟨.privateRow 9 18, 3564820371415754880⟩, ⟨.privateRow 9 19, 3463008990266105280⟩, ⟨.privateRow 9 21, 17990661040802049600⟩, ⟨.privateRow 9 24, 64080174063536991360⟩, ⟨.privateRow 10 11, 24486399384511680⟩, ⟨.privateRow 10 12, 86093398235164320⟩, ⟨.privateRow 10 13, 195724575591985440⟩, ⟨.privateRow 10 14, 338909362499163456⟩, ⟨.privateRow 10 15, 526302815779540800⟩, ⟨.privateRow 10 16, 1028831993301031920⟩, ⟨.privateRow 10 17, 2339362311771101760⟩, ⟨.privateRow 10 18, 2375987178600715680⟩, ⟨.privateRow 10 20, 8491795331461041600⟩, ⟨.privateRow 10 21, 4723064765912132640⟩, ⟨.privateRow 11 8, 1386274107778560⟩, ⟨.privateRow 11 9, 15100485816873600⟩, ⟨.privateRow 11 10, 45320499677376000⟩, ⟨.privateRow 11 11, 99494047943690400⟩, ⟨.privateRow 11 12, 180294399585518400⟩, ⟨.privateRow 11 14, 1040860809257068800⟩, ⟨.privateRow 11 15, 528841911584586600⟩, ⟨.privateRow 11 16, 1661919861173457600⟩, ⟨.privateRow 11 17, 1822517241070125600⟩, ⟨.privateRow 11 18, 779605901361967680⟩, ⟨.privateRow 12 6, 1727427501489690⟩, ⟨.privateRow 12 8, 44113222501096320⟩, ⟨.privateRow 12 10, 199746214540072200⟩, ⟨.privateRow 12 11, 123378395592291840⟩, ⟨.privateRow 12 12, 11055536009534016⟩, ⟨.privateRow 12 13, 950310154689255360⟩, ⟨.privateRow 12 15, 2375578722836816640⟩, ⟨.privateRow 12 16, 1071084472877699280⟩, ⟨.privateRow 12 17, 1144819815056229312⟩, ⟨.privateRow 12 18, 419586183465288840⟩, ⟨.privateRow 12 19, 33992596351153440⟩, ⟨.privateRow 12 20, 12866356562819760⟩, ⟨.privateRow 13 4, 1495001488780800⟩, ⟨.privateRow 13 5, 1985548852287000⟩, ⟨.privateRow 13 6, 15842032442780544⟩, ⟨.privateRow 13 7, 40664040494837760⟩, ⟨.privateRow 13 8, 23851023751779840⟩, ⟨.privateRow 13 9, 223864014599184960⟩, ⟨.privateRow 13 10, 153067766067216000⟩, ⟨.privateRow 13 12, 983843868638991360⟩, ⟨.privateRow 13 13, 199507948677797760⟩, ⟨.privateRow 13 14, 1850939986095383040⟩, ⟨.privateRow 13 15, 1773545182832142720⟩, ⟨.privateRow 13 16, 1234916079777604224⟩, ⟨.privateRow 13 17, 954016512546857760⟩, ⟨.privateRow 13 18, 340137755389111680⟩, ⟨.privateRow 14 2, 1261926603897960⟩, ⟨.privateRow 14 3, 2672315161195680⟩, ⟨.privateRow 14 4, 8259883225513920⟩, ⟨.privateRow 14 5, 28221267687172560⟩, ⟨.privateRow 14 6, 54131734710064440⟩, ⟨.privateRow 14 7, 33198376810238640⟩, ⟨.privateRow 14 8, 336073998738097620⟩, ⟨.privateRow 14 10, 440871267161805480⟩, ⟨.privateRow 14 11, 896426771168969040⟩, ⟨.privateRow 14 13, 2857034608539368400⟩, ⟨.privateRow 14 14, 1918702040926671000⟩, ⟨.privateRow 14 17, 1294048371997180800⟩, ⟨.privateRow 14 19, 17178492138262575120⟩, ⟨.privateRow 15 1, 2982735609213360⟩, ⟨.privateRow 15 2, 6802256773952640⟩, ⟨.privateRow 15 3, 19875344011392870⟩, ⟨.privateRow 15 4, 52037264320737696⟩, ⟨.privateRow 15 5, 92628690457548960⟩, ⟨.privateRow 15 6, 61631436374988480⟩, ⟨.privateRow 15 8, 1200686661599705280⟩, ⟨.privateRow 15 9, 53689240965840480⟩, ⟨.privateRow 15 11, 3195542322870697800⟩, ⟨.privateRow 15 12, 1515688571881804320⟩, ⟨.privateRow 15 14, 7471890365799892032⟩, ⟨.privateRow 16 0, 16060884049610400⟩, ⟨.privateRow 16 2, 81953528878145925⟩, ⟨.privateRow 16 3, 96365304297662400⟩, ⟨.privateRow 16 4, 216084445096033800⟩, ⟨.privateRow 16 6, 277050249855779400⟩, ⟨.privateRow 16 7, 2067786675659905200⟩, ⟨.privateRow 16 9, 1414505002369258800⟩, ⟨.privateRow 16 10, 3571108888280783850⟩, ⟨.privateRow 16 13, 20360612150891812800⟩, ⟨.privateRow 16 16, 11878744563692206200⟩, ⟨.privateRow 17 0, 120497119995732480⟩, ⟨.privateRow 17 1, 173457547735792320⟩, ⟨.privateRow 17 2, 288545254011286272⟩, ⟨.privateRow 17 3, 606511425416307840⟩, ⟨.privateRow 17 4, 30498030371128320⟩, ⟨.privateRow 17 5, 616737947505039360⟩, ⟨.privateRow 17 6, 4598502261186113280⟩, ⟨.privateRow 17 7, 1420699914788394240⟩, ⟨.privateRow 17 8, 2136556460999600640⟩, ⟨.privateRow 17 12, 54687034859482561536⟩, ⟨.privateRow 17 15, 27125456512587713280⟩, ⟨.privateRow 18 0, 1693792303931948220⟩, ⟨.privateRow 18 1, 571033260323862336⟩, ⟨.privateRow 18 2, 1845493909243395840⟩, ⟨.privateRow 18 3, 1090939961400569280⟩, ⟨.privateRow 18 4, 1579702666879537200⟩, ⟨.privateRow 18 5, 13467364149962923200⟩, ⟨.privateRow 18 8, 1263762133503629760⟩, ⟨.privateRow 18 10, 103137031895379562080⟩, ⟨.privateRow 18 12, 157303281117493470960⟩, ⟨.privateRow 19 0, 21399705460661463936⟩, ⟨.privateRow 19 2, 6545639768403415680⟩, ⟨.privateRow 19 3, 7793199823272383520⟩, ⟨.privateRow 19 9, 670496020831092456000⟩, ⟨.privateRow 19 12, 1024209000197275052160⟩, ⟨.privateRow 20 13, 56843178256904264184960⟩, ⟨.hall 14 1, 1304192088239040⟩, ⟨.hall 16 5, 11709065231772480⟩, ⟨.hall 17 12, 118892396076257232⟩, ⟨.hall 14 14, 555418188341016⟩, ⟨.hall 18 14, 27128760465877918848⟩, ⟨.hall 16 16, 2128134619279468800⟩, ⟨.hall 9 17, 60957276185520⟩, ⟨.hall 12 19, 9421712953937856⟩, ⟨.hall 7 20, 630311044354992⟩, ⟨.hall 11 21, 255161077962991200⟩, ⟨.hall 10 22, 425149173380131200⟩, ⟨.hall 5 23, 14046507969542048⟩, ⟨.hall 3 27, 4182865899020142048⟩, ⟨.hall 4 27, 7875859689147415680⟩, ⟨.hall 2 30, 2011284229891099363200⟩]
  caps := #[0, 0, 0, 964667962047229440, 41620888312907904, 0, 32318692056956448, 1687939215746784, 12405146276541018, 4719520600265856, 11717381960522832, 0, 0, 5524475216495136, 46019013641832660, 11944469547897744, 0, 991589572744962048, 0, 9896229630051500736, 0, 0] }

theorem case_54_33_15_checked :
    (Witness.linear .positive case_54_33_15).check 54 33 15 = true := by
  change case_54_33_15.check 54 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_33_16 : Certificate := {
  objectiveScale := 144081371053620000000
  eta := 12047026408301743951476384000
  rows := #[⟨.count 2, 1652801769111154674223411200⟩, ⟨.count 3, 290504009382357111570028800⟩, ⟨.count 4, 61029842470142802396940800⟩, ⟨.count 5, 12302777232910479002688000⟩, ⟨.count 6, 2549873033050532533344000⟩, ⟨.count 7, 544549156210791693561600⟩, ⟨.count 8, 116689104902312505763200⟩, ⟨.count 9, 25930912200513890169600⟩, ⟨.count 10, 6648951846285612864000⟩, ⟨.count 11, 1662237961571403216000⟩, ⟨.count 12, 997342776942841929600⟩, ⟨.path 2, 160024845371811319014635520⟩, ⟨.path 10, 604349629486450848000⟩, ⟨.privateRow 2 31, 177983298616277213651592000⟩, ⟨.privateRow 5 27, 61388553422249911210953600⟩, ⟨.privateRow 6 21, 303299062345296393948000⟩, ⟨.privateRow 6 27, 101371859126092287028296000⟩, ⟨.privateRow 7 18, 13805809736384710044000⟩, ⟨.privateRow 7 20, 593529768145095708326400⟩, ⟨.privateRow 7 21, 307389355043591739718800⟩, ⟨.privateRow 7 22, 814374703719472339604160⟩, ⟨.privateRow 7 23, 1315183453169813867039400⟩, ⟨.privateRow 7 24, 1718763286920172988695200⟩, ⟨.privateRow 7 25, 724624935381027041961600⟩, ⟨.privateRow 8 16, 12497259074414333178960⟩, ⟨.privateRow 8 17, 37575812586855776032800⟩, ⟨.privateRow 8 18, 114325610300703166815450⟩, ⟨.privateRow 8 19, 346568699568772944806400⟩, ⟨.privateRow 8 20, 363422934995396638962600⟩, ⟨.privateRow 8 21, 655944033205499280081840⟩, ⟨.privateRow 8 23, 3031695792850358913879600⟩, ⟨.privateRow 9 14, 6991473608063962617600⟩, ⟨.privateRow 9 15, 20678240241948256007040⟩, ⟨.privateRow 9 16, 45397565661583434499200⟩, ⟨.privateRow 9 18, 441411248404718436873600⟩, ⟨.privateRow 9 20, 832670402883168251001600⟩, ⟨.privateRow 10 12, 3282919974103521351600⟩, ⟨.privateRow 10 13, 9920538379742056466400⟩, ⟨.privateRow 10 14, 20985754264838965602000⟩, ⟨.privateRow 10 15, 38499278121062111152800⟩, ⟨.privateRow 10 17, 327413385916378679174400⟩, ⟨.privateRow 10 18, 62832594947399041564800⟩, ⟨.privateRow 10 19, 413082755830109413208160⟩, ⟨.privateRow 10 21, 658273936748301863589600⟩, ⟨.privateRow 11 10, 1447193190319158744000⟩, ⟨.privateRow 11 11, 4772637783602741052000⟩, ⟨.privateRow 11 12, 10385552883867610176000⟩, ⟨.privateRow 11 13, 18866400863835426501600⟩, ⟨.privateRow 11 14, 37114919333874614232000⟩, ⟨.privateRow 11 16, 236966053300899910416000⟩, ⟨.privateRow 11 17, 101963187688209483636000⟩, ⟨.privateRow 11 18, 227167484330026404964800⟩, ⟨.privateRow 11 20, 215083518057875507040000⟩, ⟨.privateRow 12 8, 635212363886214800400⟩, ⟨.privateRow 12 9, 2371885706703809973600⟩, ⟨.privateRow 12 10, 5547719196744558233400⟩, ⟨.privateRow 12 11, 10426765395311529264000⟩, ⟨.privateRow 12 12, 20453838117136116572880⟩, ⟨.privateRow 12 13, 35627300309680408929600⟩, ⟨.privateRow 12 14, 6711285769844540484600⟩, ⟨.privateRow 12 15, 169809480902815777108800⟩, ⟨.privateRow 12 16, 23492963190209165452800⟩, ⟨.privateRow 12 17, 387334689805368377392320⟩, ⟨.privateRow 13 6, 288121246672376557440⟩, ⟨.privateRow 13 7, 1234805342881613817600⟩, ⟨.privateRow 13 8, 3213660059038046217600⟩, ⟨.privateRow 13 10, 26142469759259341488000⟩, ⟨.privateRow 13 11, 2050093485938063966400⟩, ⟨.privateRow 13 12, 68090192055480442848000⟩, ⟨.privateRow 13 14, 135353662585099976160000⟩, ⟨.privateRow 13 15, 92365022731317638702400⟩, ⟨.privateRow 13 16, 229832102153272684665600⟩, ⟨.privateRow 13 19, 951797456795785481481600⟩, ⟨.privateRow 14 4, 146311570575816220575⟩, ⟨.privateRow 14 5, 684287960846894323920⟩, ⟨.privateRow 14 6, 2006558682182622453600⟩, ⟨.privateRow 14 7, 4460338530216598629600⟩, ⟨.privateRow 14 9, 35867821105635058940400⟩, ⟨.privateRow 14 10, 5600356732194319335240⟩, ⟨.privateRow 14 11, 76632248246889042708000⟩, ⟨.privateRow 14 12, 24692891218718522149350⟩, ⟨.privateRow 14 13, 117100706683273043702400⟩, ⟨.privateRow 14 14, 151863907100231810484000⟩, ⟨.privateRow 14 15, 210076403979996557443440⟩, ⟨.privateRow 14 19, 2315054217012545639030400⟩, ⟨.privateRow 15 2, 84741543138934281600⟩, ⟨.privateRow 15 3, 427679975529308952450⟩, ⟨.privateRow 15 4, 1392586025583153360960⟩, ⟨.privateRow 15 5, 3447164915544505240800⟩, ⟨.privateRow 15 6, 8283485841830826026400⟩, ⟨.privateRow 15 8, 56314607304146327136000⟩, ⟨.privateRow 15 9, 18151638540359723118720⟩, ⟨.privateRow 15 13, 973429636934568881667600⟩, ⟨.privateRow 16 0, 50021049769509819000⟩, ⟨.privateRow 16 1, 317780786771003556000⟩, ⟨.privateRow 16 2, 1069199938823272381125⟩, ⟨.privateRow 16 3, 3001262986170589140000⟩, ⟨.privateRow 16 4, 6559903384058573406000⟩, ⟨.privateRow 16 5, 20916494349773490468000⟩, ⟨.privateRow 16 7, 103543573022885325330000⟩, ⟨.privateRow 16 8, 59064855567837194275200⟩, ⟨.privateRow 16 10, 24535324911944566219500⟩, ⟨.privateRow 16 12, 975410470505441470500000⟩, ⟨.privateRow 17 1, 2701136687553530226000⟩, ⟨.privateRow 17 2, 9027799062401132133120⟩, ⟨.privateRow 17 5, 175033657353468758644800⟩, ⟨.privateRow 17 7, 433334354995254342389760⟩, ⟨.privateRow 17 11, 956082336874502876438400⟩, ⟨.privateRow 17 16, 10311859418404356990777600⟩, ⟨.privateRow 18 0, 17602407413890505306100⟩, ⟨.privateRow 18 1, 33470084821774410089280⟩, ⟨.privateRow 18 2, 2623961353623429362400⟩, ⟨.privateRow 18 4, 525521148878470158414000⟩, ⟨.privateRow 18 5, 174771728947402961774400⟩, ⟨.privateRow 18 6, 1082471523748118726302080⟩, ⟨.privateRow 18 9, 1782544412894849680190400⟩, ⟨.privateRow 19 10, 45698910934705645775558400⟩, ⟨.privateRow 20 10, 440246923930262166708790800⟩, ⟨.hall 16 1, 1694830862778685632000⟩, ⟨.hall 13 6, 3089535426940312350⟩, ⟨.hall 14 6, 7552935157589850600⟩, ⟨.hall 17 7, 1445013682502413023000⟩, ⟨.hall 14 12, 16711009434786466800⟩, ⟨.hall 18 14, 176330202963494453153280⟩, ⟨.hall 11 17, 112646383618908110400⟩, ⟨.hall 7 18, 12543781796476578648⟩, ⟨.hall 12 19, 997342776942841929600⟩, ⟨.hall 13 19, 52870248764381098290240⟩, ⟨.hall 6 21, 176705555810878894800⟩, ⟨.hall 9 22, 4074289786242950274000⟩, ⟨.hall 10 22, 806944259127195765576000⟩, ⟨.hall 7 25, 505278784368667292583600⟩, ⟨.hall 4 26, 69552290217969010566400⟩, ⟨.hall 3 29, 145839772034390203962192000⟩, ⟨.hall 2 30, 173998093827525655547059200⟩]
  caps := #[0, 3393194607338280025881600, 268199414998484914264320, 6857511779811063571200, 0, 0, 0, 2722431308703594508020, 859205168460194019750, 346251847860339220800, 509535875222789421600, 1957089629752227144000, 0, 3005514786264275450880, 296315753170679522280, 144081371053620000000, 5820072765290323929675, 45715237805350413780480, 11779996198160941213320, 0, 0, 0] }

theorem case_54_33_16_checked :
    (Witness.linear .positive case_54_33_16).check 54 33 16 = true := by
  change case_54_33_16.check 54 33 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_33_17 : Certificate := {
  objectiveScale := 632827982666880000
  eta := 27326728676438521691961600
  rows := #[⟨.count 2, 5296139984969199560113920⟩, ⟨.count 3, 1009891162427286413514240⟩, ⟨.count 4, 209577648640112935902720⟩, ⟨.count 5, 41384688158395905523200⟩, ⟨.count 6, 8971047907753542811200⟩, ⟨.count 7, 1925173784583606997440⟩, ⟨.count 8, 419085449705274992640⟩, ⟨.count 9, 96712026855063459840⟩, ⟨.count 10, 25185423660172776000⟩, ⟨.count 11, 10074169464069110400⟩, ⟨.count 12, 6044501678441466240⟩, ⟨.path 10, 1658148771313507200⟩, ⟨.path 11, 367075906620142720⟩, ⟨.privateRow 2 31, 329951213121084317642880⟩, ⟨.privateRow 3 28, 33395871773389100976000⟩, ⟨.privateRow 3 29, 128685425900126002427520⟩, ⟨.privateRow 4 26, 24917030995367534783760⟩, ⟨.privateRow 4 27, 47051072676285977819520⟩, ⟨.privateRow 4 28, 86272668747921844188000⟩, ⟨.privateRow 5 23, 2281687448395386071040⟩, ⟨.privateRow 5 24, 9233849408506225671168⟩, ⟨.privateRow 5 25, 17300371220645883289920⟩, ⟨.privateRow 5 26, 31751543446420487289600⟩, ⟨.privateRow 5 27, 41445804786477924792960⟩, ⟨.privateRow 6 21, 1523238409085021085600⟩, ⟨.privateRow 6 22, 3397793489797976068800⟩, ⟨.privateRow 6 23, 6213160065552423263280⟩, ⟨.privateRow 6 24, 11337953035483530155700⟩, ⟨.privateRow 6 25, 15597472791765334470000⟩, ⟨.privateRow 6 26, 17178137964481844750400⟩, ⟨.privateRow 7 18, 90462310613465030240⟩, ⟨.privateRow 7 19, 619351543509748849800⟩, ⟨.privateRow 7 20, 1344877637335454645280⟩, ⟨.privateRow 7 21, 2289690816358507642080⟩, ⟨.privateRow 7 22, 4146763215365007453216⟩, ⟨.privateRow 7 23, 5723135672537661618240⟩, ⟨.privateRow 7 24, 6681357091395035169120⟩, ⟨.privateRow 7 25, 5584531890994510774320⟩, ⟨.privateRow 8 16, 67446564561942694128⟩, ⟨.privateRow 8 17, 245557880686684566000⟩, ⟨.privateRow 8 18, 532997022134931444090⟩, ⟨.privateRow 8 19, 906459376706275597920⟩, ⟨.privateRow 8 20, 1591760751029019731160⟩, ⟨.privateRow 8 21, 2222680799140007942736⟩, ⟨.privateRow 8 22, 2600185114382337682200⟩, ⟨.privateRow 8 23, 2363540075290947593040⟩, ⟨.privateRow 8 24, 442004185236032218800⟩, ⟨.privateRow 9 14, 34679565185401543680⟩, ⟨.privateRow 9 15, 104166912258474601536⟩, ⟨.privateRow 9 16, 219019906496613622400⟩, ⟨.privateRow 9 17, 377781354902591640000⟩, ⟨.privateRow 9 18, 666910018521375108480⟩, ⟨.privateRow 9 19, 933315833237869361280⟩, ⟨.privateRow 9 20, 1118501455030713097344⟩, ⟨.privateRow 9 21, 241947969962059801440⟩, ⟨.privateRow 10 12, 15405084138805681320⟩, ⟨.privateRow 10 13, 47165429763596289600⟩, ⟨.privateRow 10 14, 97618702106829679776⟩, ⟨.privateRow 10 15, 168910241347558751040⟩, ⟨.privateRow 10 16, 303988063578285406320⟩, ⟨.privateRow 10 17, 440025330519875786400⟩, ⟨.privateRow 10 18, 150860687724434928240⟩, ⟨.privateRow 11 10, 6446059482254011200⟩, ⟨.privateRow 11 11, 22323443698789506000⟩, ⟨.privateRow 11 12, 48081263351238936000⟩, ⟨.privateRow 11 13, 84073523345594939520⟩, ⟨.privateRow 11 14, 153300366642627422400⟩, ⟨.privateRow 11 15, 70862623843849765200⟩, ⟨.privateRow 12 8, 2626479895989446640⟩, ⟨.privateRow 12 9, 10926599187951881280⟩, ⟨.privateRow 12 10, 25857034957777383360⟩, ⟨.privateRow 12 11, 47485971519271215840⟩, ⟨.privateRow 12 12, 26041728064618650384⟩, ⟨.privateRow 13 6, 1074578076167371776⟩, ⟨.privateRow 13 7, 5564779323009603840⟩, ⟨.privateRow 13 8, 14982098177333548800⟩, ⟨.privateRow 13 9, 8842882085127330240⟩, ⟨.privateRow 14 4, 477473656890775545⟩, ⟨.privateRow 14 5, 2983073513527131024⟩, ⟨.privateRow 14 6, 3975699020641559640⟩, ⟨.privateRow 15 2, 128396277483233760⟩, ⟨.privateRow 15 3, 1364210448259358700⟩, ⟨.privateRow 16 1, 320990693708084400⟩, ⟨.hall 6 26, 4410340800283811192800⟩, ⟨.hall 5 27, 16735354230418235755200⟩, ⟨.hall 4 28, 43391601669700045681920⟩, ⟨.hall 3 29, 93642024452583039136704⟩, ⟨.hall 2 30, 174118175327751691196160⟩, ⟨.assumptionRow 17, 764885211122567808⟩]
  caps := #[0, 42385968244356321661440, 1581703741124121538560, 229645671592741272960, 83273897024822479248, 212528818731678164352, 0, 0, 4137456715942726358, 555980707638685056, 12780689117704004744, 0, 3621556644803985312, 7552793104325459712, 764885211122567808, 9791435584744992360, 122903823706399008, 8727534528880632192, 632827982666880000, 0, 0, 0] }

theorem case_54_33_17_checked :
    (Witness.linear .conditional case_54_33_17).check 54 33 17 = true := by
  change case_54_33_17.check 54 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_33_18 : Certificate := {
  objectiveScale := 176678199184544857800000
  eta := 7122379763228700613382419680000
  rows := #[⟨.count 2, 1355287120660089888146483287680⟩, ⟨.count 3, 248372912344772281540358364480⟩, ⟨.count 4, 49196187036236338071383329920⟩, ⟨.count 5, 9450304860542282989892640000⟩, ⟨.count 6, 1827058939704841378045910400⟩, ⟨.count 7, 382212329915265667591213440⟩, ⟨.count 8, 86102777618274133907910720⟩, ⟨.count 9, 21808395832020653053598400⟩, ⟨.count 10, 8481042823563587298621600⟩, ⟨.count 11, 3634732638670108842266400⟩, ⟨.count 12, 1453893055468043536906560⟩, ⟨.path 9, 1092525544873259698481280⟩, ⟨.path 10, 143338517683671897787200⟩, ⟨.privateRow 2 31, 111923110565022438210295166400⟩, ⟨.privateRow 3 28, 10710345508614587388544992000⟩, ⟨.privateRow 3 29, 37539761007694128796850196960⟩, ⟨.privateRow 4 26, 6693965942884117117840620000⟩, ⟨.privateRow 4 27, 13489085148905149783239720480⟩, ⟨.privateRow 4 28, 26088616601400365780597509680⟩, ⟨.privateRow 5 23, 459914836546391105508108480⟩, ⟨.privateRow 5 24, 2367196364178502530268218624⟩, ⟨.privateRow 5 25, 4814405309509596389850861600⟩, ⟨.privateRow 5 26, 9570708744691414299097198080⟩, ⟨.privateRow 5 27, 13522336221562613371537490880⟩, ⟨.privateRow 6 21, 285759218402111890408658400⟩, ⟨.privateRow 6 22, 828214217639191745364202200⟩, ⟨.privateRow 6 23, 1689504502290281481193028640⟩, ⟨.privateRow 6 24, 3385702970523447079503897900⟩, ⟨.privateRow 6 25, 5156541346590340153651604400⟩, ⟨.privateRow 6 26, 6287734088114973147650096100⟩, ⟨.privateRow 7 18, 1691721240467445720412880⟩, ⟨.privateRow 7 19, 120688268323175405683420590⟩, ⟨.privateRow 7 20, 307134907967624197171510800⟩, ⟨.privateRow 7 21, 606219556239230894018298240⟩, ⟨.privateRow 7 22, 1227384594609763842987278544⟩, ⟨.privateRow 7 23, 1901611344715786054966174560⟩, ⟨.privateRow 7 24, 2515706155005468851476050000⟩, ⟨.privateRow 7 25, 2494092957778117519082499240⟩, ⟨.privateRow 8 16, 2047566053117494647810072⟩, ⟨.privateRow 8 17, 43255562062296931092625880⟩, ⟨.privateRow 8 18, 117505353144451095093074805⟩, ⟨.privateRow 8 19, 229957418273195552754054240⟩, ⟨.privateRow 8 20, 463939966394399855670470160⟩, ⟨.privateRow 8 21, 737123779122298073211625920⟩, ⟨.privateRow 8 22, 989525671439281548066675180⟩, ⟨.privateRow 8 23, 1089235138000280913501699840⟩, ⟨.privateRow 8 24, 724260864173226632475383160⟩, ⟨.privateRow 9 14, 719603633514486195034560⟩, ⟨.privateRow 9 15, 15265877082414457137518880⟩, ⟨.privateRow 9 16, 45106583313471523558594880⟩, ⟨.privateRow 9 17, 92402980858635655901172480⟩, ⟨.privateRow 9 18, 187552204155377616260946240⟩, ⟨.privateRow 9 19, 304455975393196968802581120⟩, ⟨.privateRow 9 20, 421112046332677321334224512⟩, ⟨.privateRow 9 21, 482167477478693660753539440⟩, ⟨.privateRow 9 22, 137042882450598918571377600⟩, ⟨.privateRow 10 13, 5341955544712129662118800⟩, ⟨.privateRow 10 14, 17701147950323430061837368⟩, ⟨.privateRow 10 15, 38716633588204566779104320⟩, ⟨.privateRow 10 16, 81902642124699785912402880⟩, ⟨.privateRow 10 17, 137081345229844104908332800⟩, ⟨.privateRow 10 18, 196679421670260334020415200⟩, ⟨.privateRow 10 19, 132619278209610037958160048⟩, ⟨.privateRow 11 11, 1578722257200148285024800⟩, ⟨.privateRow 11 12, 7129282751330902191993600⟩, ⟨.privateRow 11 13, 17039186036432298118139760⟩, ⟨.privateRow 11 14, 38317669668943133956687200⟩, ⟨.privateRow 11 15, 68178772828387799192815200⟩, ⟨.privateRow 11 16, 80782326263776358425089600⟩, ⟨.privateRow 12 9, 447351709374782626740480⟩, ⟨.privateRow 12 10, 2715952999450720218249060⟩, ⟨.privateRow 12 11, 7875254050451902491577200⟩, ⟨.privateRow 12 12, 19288314535876044256293696⟩, ⟨.privateRow 12 13, 37222354614529077588394800⟩, ⟨.privateRow 12 14, 3543864322703356121209740⟩, ⟨.privateRow 13 7, 103849503962003109779040⟩, ⟨.privateRow 13 8, 1018967782464782649797760⟩, ⟨.privateRow 13 9, 3553960802255217534660480⟩, ⟨.privateRow 13 10, 10412224003301443107744960⟩, ⟨.privateRow 13 11, 7398700215604043776702272⟩, ⟨.privateRow 14 5, 17500564556559783314616⟩, ⟨.privateRow 14 6, 375012097640566785313200⟩, ⟨.privateRow 14 7, 1635629687401548979019880⟩, ⟨.privateRow 14 8, 4440768256227045016083810⟩, ⟨.privateRow 15 4, 105003387339358699887696⟩, ⟨.privateRow 15 5, 750024195281133570626400⟩, ⟨.privateRow 15 6, 807718364148913076059200⟩, ⟨.privateRow 16 3, 262508468348396749719240⟩, ⟨.privateRow 16 4, 93753024410141696328300⟩, ⟨.hall 7 25, 333446333679775040624139240⟩, ⟨.hall 6 26, 2295782393744700907822375600⟩, ⟨.hall 5 27, 6626463765308815096484244000⟩, ⟨.hall 4 28, 15171758396340939652463043840⟩, ⟨.hall 3 29, 30331698480396511484359417344⟩, ⟨.hall 2 30, 54025055715550420320863883840⟩, ⟨.assumptionRow 18, 170381931790835939206032⟩]
  caps := #[0, 0, 1273652853179360233289149440, 0, 0, 22951044749712931943787696, 0, 0, 4215454237678221496077119, 652237076385295960663104, 487667807335465037029320, 631817418964377703959408, 0, 6797169128314063877398416, 299466467074843393188864, 170381931790835939206032, 170381931790835939206032, 15818803738330126123109520, 2303112856792792069993968, 176678199184544857800000, 0, 0] }

theorem case_54_33_18_checked :
    (Witness.linear .conditional case_54_33_18).check 54 33 18 = true := by
  change case_54_33_18.check 54 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_33_19 : Certificate := {
  objectiveScale := 141949785704172201756000000
  eta := 6642051417939665864195273214000000
  rows := #[⟨.count 2, 1174314690691732924789724304235200⟩, ⟨.count 3, 199513241328764531684922438352320⟩, ⟨.count 4, 35759872616444292287793779717760⟩, ⟨.count 5, 6086833497554616395671210128000⟩, ⟨.count 6, 1011730432701645698199403845600⟩, ⟨.count 7, 180411551414006197673498029920⟩, ⟨.count 8, 41675616740013589736127204480⟩, ⟨.count 9, 12907630285874654310986765760⟩, ⟨.count 10, 4429088823584440204750360800⟩, ⟨.count 11, 1898180924393331516321583200⟩, ⟨.count 12, 759272369757332606528633280⟩, ⟨.path 8, 1925278547002832478381724800⟩, ⟨.path 9, 648433121179540426240230720⟩, ⟨.privateRow 2 31, 90863263397414629022191337567520⟩, ⟨.privateRow 3 28, 8222160492102154796098569789120⟩, ⟨.privateRow 3 29, 30930984708384296613894619682880⟩, ⟨.privateRow 4 26, 5129528130135159497225893454040⟩, ⟨.privateRow 4 27, 10872766274325562974886203965280⟩, ⟨.privateRow 4 28, 22079577239845752420135445062960⟩, ⟨.privateRow 5 23, 327555724553089266697982238720⟩, ⟨.privateRow 5 24, 1749059830972991392399359623808⟩, ⟨.privateRow 5 25, 3775481858618336385963628984800⟩, ⟨.privateRow 5 26, 8000256111740854366538664410880⟩, ⟨.privateRow 5 27, 12056317232183405051822272601280⟩, ⟨.privateRow 6 21, 187716534987326248881945138600⟩, ⟨.privateRow 6 22, 585492148554193112383914262500⟩, ⟨.privateRow 6 23, 1283718668268050178582549811680⟩, ⟨.privateRow 6 24, 2776260965480921740604427795150⟩, ⟨.privateRow 6 25, 4591400868369369987650636919000⟩, ⟨.privateRow 6 26, 6065584416650991045641276849400⟩, ⟨.privateRow 7 19, 72486784050270347279530458450⟩, ⟨.privateRow 7 20, 205518760371100850888589701040⟩, ⟨.privateRow 7 21, 443991548515320216969530612640⟩, ⟨.privateRow 7 22, 983215537037425873643106284640⟩, ⟨.privateRow 7 23, 1675387211117454211069771598520⟩, ⟨.privateRow 7 24, 2446157636066806423875975061200⟩, ⟨.privateRow 7 25, 2723583808466611800288286748040⟩, ⟨.privateRow 8 17, 23214049675358446914421732320⟩, ⟨.privateRow 8 18, 73395010895344656595325993745⟩, ⟨.privateRow 8 19, 160709638613041126585836390960⟩, ⟨.privateRow 8 20, 360548921138933358572416275600⟩, ⟨.privateRow 8 21, 637664354291115826640204206968⟩, ⟨.privateRow 8 22, 955797368129522196185127860640⟩, ⟨.privateRow 8 23, 1200413131736202838572725366760⟩, ⟨.privateRow 8 24, 1014540795014705825138846634060⟩, ⟨.privateRow 9 15, 6487560581593208604672433248⟩, ⟨.privateRow 9 16, 25777765639909440345107920000⟩, ⟨.privateRow 9 17, 60689062332686793757948396200⟩, ⟨.privateRow 9 18, 139621752438709495978320897600⟩, ⟨.privateRow 9 19, 255734182613821582361903372160⟩, ⟨.privateRow 9 20, 398196176139401100312794342400⟩, ⟨.privateRow 9 21, 521831027014886759742540128160⟩, ⟨.privateRow 9 22, 529915871692858356941687612160⟩, ⟨.privateRow 9 23, 74830510219417113554544191040⟩, ⟨.privateRow 10 13, 1535800929736422772296553680⟩, ⟨.privateRow 10 14, 8693668633721458344752851056⟩, ⟨.privateRow 10 15, 23410898067517755367966192800⟩, ⟨.privateRow 10 16, 57372518439788445080819852220⟩, ⟨.privateRow 10 17, 109913714479156720183192627200⟩, ⟨.privateRow 10 18, 178766461279531977026019324480⟩, ⟨.privateRow 10 19, 247408901685426829837355154288⟩, ⟨.privateRow 10 20, 148184657497639413707504928480⟩, ⟨.privateRow 11 11, 244462694808232089223234200⟩, ⟨.privateRow 11 12, 2734844692720970752165807200⟩, ⟨.privateRow 11 13, 8990475105535688363668589520⟩, ⟨.privateRow 11 14, 24689134380240537533839312800⟩, ⟨.privateRow 11 15, 51042372660107047099874693700⟩, ⟨.privateRow 11 16, 87760053127795586988374496000⟩, ⟨.privateRow 11 17, 116862754890680359514949996000⟩, ⟨.privateRow 12 10, 711817846647499318620593700⟩, ⟨.privateRow 12 11, 3330444712799208933182414160⟩, ⟨.privateRow 12 12, 10863922157277834045080527848⟩, ⟨.privateRow 12 13, 25372351689390864601498495440⟩, ⟨.privateRow 12 14, 47462432197018260122690919930⟩, ⟨.privateRow 12 15, 20898068081892297455883335040⟩, ⟨.privateRow 13 8, 90853104073526978558981760⟩, ⟨.privateRow 13 9, 1082666156876196494494532640⟩, ⟨.privateRow 13 10, 4732030829699739578062290240⟩, ⟨.privateRow 13 11, 13186030154785676266713931296⟩, ⟨.privateRow 13 12, 19159910170172689478327486720⟩, ⟨.privateRow 14 7, 221454441179222010237518040⟩, ⟨.privateRow 14 8, 1850726401283498228413543620⟩, ⟨.privateRow 14 9, 6979170267466390625667235200⟩, ⟨.privateRow 14 10, 3701452802566996456827087240⟩, ⟨.privateRow 15 5, 19584406362788341041413160⟩, ⟨.privateRow 15 6, 506181579838221737685755520⟩, ⟨.privateRow 15 7, 3335877217128280757387374920⟩, ⟨.privateRow 16 4, 48961015906970852603532900⟩, ⟨.privateRow 16 5, 1001817710096480522503057800⟩, ⟨.privateRow 17 3, 156675250902306728331305280⟩, ⟨.hall 7 25, 733088018450284594556263885080⟩, ⟨.hall 6 26, 2753088804674728146530566863200⟩, ⟨.hall 5 27, 6817723543013877283336749259200⟩, ⟨.hall 4 28, 14334294341380064378279280007680⟩, ⟨.hall 3 29, 27082789865822199675312431917632⟩, ⟨.hall 2 30, 46348663313829307088474887150080⟩, ⟨.assumptionRow 19, 96913022319345226874369490⟩]
  caps := #[0, 2913748567922529405200055924000, 489440686011248833247148112350, 76928945406993112737803949450, 0, 3736550490003862689975419460, 835730458366369942999987650, 1106802513556830757613833458, 268863474413612398093264491, 0, 277783576403102042897190996, 0, 440875117082308308136120098, 1342622230054844205746024592, 308030325229125156949511220, 148789281253863478867108470, 96913022319345226874369490, 17597045688311771488155800880, 11418698400904664981798827140, 1748434191834893395953630510, 141949785704172201756000000, 0] }

theorem case_54_33_19_checked :
    (Witness.linear .conditional case_54_33_19).check 54 33 19 = true := by
  change case_54_33_19.check 54 33 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_33_20 : Certificate := {
  objectiveScale := 588927330615149526000000
  eta := 36670080952394624300900343609600
  rows := #[⟨.count 2, 6678757252261884403748886111360⟩, ⟨.count 3, 1161215660043993564666048032640⟩, ⟨.count 4, 211065208823098135470259975680⟩, ⟨.count 5, 35071131371345805762490464000⟩, ⟨.count 6, 5874939521637119258716591200⟩, ⟨.count 7, 859977742309347752080230240⟩, ⟨.count 8, 109203522832933047883203840⟩, ⟨.count 9, 8723358332808261221439360⟩, ⟨.path 9, 7648482732836050604378880⟩, ⟨.path 10, 102364947181217081961600⟩, ⟨.privateRow 2 31, 531126033772197388597946153280⟩, ⟨.privateRow 3 28, 46340094900605781434437998720⟩, ⟨.privateRow 3 29, 178755666538777463514815916480⟩, ⟨.privateRow 4 26, 29373122557375505913084640560⟩, ⟨.privateRow 4 27, 62441314315223044475217303360⟩, ⟨.privateRow 4 28, 128095732283030465166998104320⟩, ⟨.privateRow 5 23, 2083267204812876605771888640⟩, ⟨.privateRow 5 24, 9977841878535221098128424704⟩, ⟨.privateRow 5 25, 21489993252873151519015863360⟩, ⟨.privateRow 5 26, 46033485009574854030765926400⟩, ⟨.privateRow 5 27, 70621078188959087196468821760⟩, ⟨.privateRow 6 21, 1239039970604432658674812800⟩, ⟨.privateRow 6 22, 3331669977455068748520021000⟩, ⟨.privateRow 6 23, 7211107625530458714787522800⟩, ⟨.privateRow 6 24, 15768883693688192755634746800⟩, ⟨.privateRow 6 25, 26670860384197109771474784000⟩, ⟨.privateRow 6 26, 36268169987014494941210198400⟩, ⟨.privateRow 7 18, 55651795289860110940478880⟩, ⟨.privateRow 7 19, 445214362318880887523831040⟩, ⟨.privateRow 7 20, 1177837996269492159311698560⟩, ⟨.privateRow 7 21, 2455504212930903196873770960⟩, ⟨.privateRow 7 22, 5489367083326994112728971488⟩, ⟨.privateRow 7 23, 9598097128222430359984572120⟩, ⟨.privateRow 7 24, 14539119022298736782116680480⟩, ⟨.privateRow 7 25, 16958047055306430031862904000⟩, ⟨.privateRow 8 16, 34283605966300615513332744⟩, ⟨.privateRow 8 17, 151963235566127451781915600⟩, ⟨.privateRow 8 18, 412597685126592591371215470⟩, ⟨.privateRow 8 19, 879253364128072884845328720⟩, ⟨.privateRow 8 20, 1972751139638201574140088600⟩, ⟨.privateRow 8 21, 3587440728449189981663133840⟩, ⟨.privateRow 8 22, 5606524612750883582128668300⟩, ⟨.privateRow 8 23, 7444390151069400626371354080⟩, ⟨.privateRow 8 24, 6861971362627091037660933600⟩, ⟨.privateRow 9 13, 403859182074456538029600⟩, ⟨.privateRow 9 14, 13510925363945455090444800⟩, ⟨.privateRow 9 15, 53858660521449523911627456⟩, ⟨.privateRow 9 16, 146573959147556092868876160⟩, ⟨.privateRow 9 17, 324783554224277947883404320⟩, ⟨.privateRow 9 18, 750578059302264253878554880⟩, ⟨.privateRow 9 19, 1407906956602498752442922880⟩, ⟨.privateRow 9 20, 2292433952392879135948179072⟩, ⟨.privateRow 9 21, 3187256664931610998129603200⟩, ⟨.privateRow 9 22, 3534575561515643620835059200⟩, ⟨.privateRow 9 23, 1765672344029523984265411200⟩, ⟨.privateRow 10 11, 186396545572826094475200⟩, ⟨.privateRow 10 12, 4603994675648804533537440⟩, ⟨.privateRow 10 13, 19517412835525554146957760⟩, ⟨.privateRow 10 14, 54690610436522904379968432⟩, ⟨.privateRow 10 15, 124980954879308483302226880⟩, ⟨.privateRow 10 16, 300986151920540596380010140⟩, ⟨.privateRow 10 17, 592496036604548408992682880⟩, ⟨.privateRow 10 18, 1005124732346907431848068480⟩, ⟨.privateRow 10 19, 1475265283383423776899086432⟩, ⟨.privateRow 10 20, 1636538370561216506230446600⟩, ⟨.privateRow 11 9, 47204319982728686263200⟩, ⟨.privateRow 11 10, 1491172364582608755801600⟩, ⟨.privateRow 11 11, 7140964628498345149705200⟩, ⟨.privateRow 11 12, 21548056855146209996025600⟩, ⟨.privateRow 11 13, 51370887959870871637365120⟩, ⟨.privateRow 11 14, 128378267271546941937288000⟩, ⟨.privateRow 11 15, 267978924541950751916186400⟩, ⟨.privateRow 11 16, 480949081530695008106990400⟩, ⟨.privateRow 11 17, 747543346019819051892789600⟩, ⟨.privateRow 11 18, 378232481248277386798267200⟩, ⟨.privateRow 12 8, 467322767829013994005680⟩, ⟨.privateRow 12 9, 2646830947134130541547840⟩, ⟨.privateRow 12 10, 8905094964741766663552680⟩, ⟨.privateRow 12 11, 22777657868999348744869440⟩, ⟨.privateRow 12 12, 59561152172340850228605408⟩, ⟨.privateRow 12 13, 131496549683443048782437760⟩, ⟨.privateRow 12 14, 252492760632950227576105920⟩, ⟨.privateRow 12 15, 324633549385221721169279040⟩, ⟨.privateRow 13 6, 150774094641130440864384⟩, ⟨.privateRow 13 7, 992339704525807493444160⟩, ⟨.privateRow 13 8, 3852195275171739285820800⟩, ⟨.privateRow 13 9, 10850350025067065655061920⟩, ⟨.privateRow 13 10, 30428953645755416247175680⟩, ⟨.privateRow 13 11, 71531538329027742015802752⟩, ⟨.privateRow 13 12, 146753452117366962441333760⟩, ⟨.privateRow 13 13, 35014591085855381847166320⟩, ⟨.privateRow 14 4, 65627117087099187429810⟩, ⟨.privateRow 14 5, 385012420244315232921552⟩, ⟨.privateRow 14 6, 1762556858910663890972040⟩, ⟨.privateRow 14 7, 5532870794420054571005520⟩, ⟨.privateRow 14 8, 17106801854037188190037140⟩, ⟨.privateRow 14 9, 43719592183114804135058880⟩, ⟨.privateRow 14 10, 38221232991526566759121344⟩, ⟨.privateRow 15 3, 196881351261297562289430⟩, ⟨.privateRow 15 4, 840027098714869599101568⟩, ⟨.privateRow 15 5, 3000096781124534282505600⟩, ⟨.privateRow 15 6, 10581110570350761296375520⟩, ⟨.privateRow 15 7, 20650666176740544311246880⟩, ⟨.privateRow 16 1, 154416746087292205717200⟩, ⟨.privateRow 16 2, 492203378153243905723575⟩, ⟨.privateRow 16 3, 1925062101221576164607760⟩, ⟨.privateRow 16 4, 7125229855170768920950800⟩, ⟨.privateRow 16 5, 1009647955186141345074000⟩, ⟨.privateRow 17 0, 494133587479335058295040⟩, ⟨.privateRow 17 1, 1575050810090380498315440⟩, ⟨.privateRow 17 2, 1120036131619826132135424⟩, ⟨.hall 7 25, 5505044896775124515535280560⟩, ⟨.hall 6 26, 17851159199842864307018807200⟩, ⟨.hall 5 27, 41965353774369985543688332800⟩, ⟨.hall 4 28, 85840341566054936715915540480⟩, ⟨.hall 3 29, 159691251533443497963205830720⟩, ⟨.hall 2 30, 270978651268277199373664778240⟩, ⟨.assumptionRow 20, 115623649798648756324560⟩]
  caps := #[0, 17350525131414395454200066400, 198478164792706853025011040, 801986017364378152134388560, 51031491628874616650590800, 8217438550762911986163648, 17850238604673971051985000, 4250862348976998785423536, 0, 618447986392515321762720, 1128337884337359870336624, 1225884543423184289164800, 269218229436787784286408, 5755150224519526242996672, 0, 10640532703780396913387892, 22603014203410889723271225, 0, 195718437233423946030789600, 43844297009984079669780720, 6951504317583145555675440, 588927330615149526000000] }

theorem case_54_33_20_checked :
    (Witness.linear .conditional case_54_33_20).check 54 33 20 = true := by
  change case_54_33_20.check 54 33 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_33_21 : Certificate := {
  objectiveScale := 58454325619369680000000
  eta := 7916672805948214691003869248000
  rows := #[⟨.count 2, 661035614891364195177520425600⟩, ⟨.count 3, 88619471708375537585864208000⟩, ⟨.count 4, 17205651817064724256436793600⟩, ⟨.count 5, 3156876032267171235333312000⟩, ⟨.count 6, 533484951804806297816520000⟩, ⟨.count 7, 88914158634134382969420000⟩, ⟨.count 8, 12871382964179453534620800⟩, ⟨.count 9, 1406993279485203422812800⟩, ⟨.path 2, 182614032942592414967786062080⟩, ⟨.path 9, 334015263072173204121600⟩, ⟨.path 10, 98128296902262266640000⟩, ⟨.privateRow 2 31, 73193119225806462524621179200⟩, ⟨.privateRow 3 30, 115740830496318928231050720000⟩, ⟨.privateRow 6 21, 59457563222689862897238000⟩, ⟨.privateRow 6 22, 214029081855023479004961000⟩, ⟨.privateRow 6 26, 12067556630051338648585353000⟩, ⟨.privateRow 7 19, 27986789931982298639422200⟩, ⟨.privateRow 7 20, 85043066013328532282316000⟩, ⟨.privateRow 7 21, 206421981616325315128688400⟩, ⟨.privateRow 7 22, 338009291051438860057844640⟩, ⟨.privateRow 7 23, 691752154173565499502087600⟩, ⟨.privateRow 8 16, 618165102884934281596920⟩, ⟨.privateRow 8 17, 9126638505302682696332000⟩, ⟨.privateRow 8 18, 29828583217975082286645900⟩, ⟨.privateRow 8 19, 71953934089228749646545600⟩, ⟨.privateRow 8 20, 185421304148453575151149200⟩, ⟨.privateRow 8 21, 322851544008095950961153040⟩, ⟨.privateRow 8 22, 599239089118525677222000600⟩, ⟨.privateRow 8 25, 4770117590494689454333712400⟩, ⟨.privateRow 9 14, 355301333203334197680000⟩, ⟨.privateRow 9 15, 2813986558970406845625600⟩, ⟨.privateRow 9 16, 9889483626998878379276800⟩, ⟨.privateRow 9 17, 25215143448551955785686800⟩, ⟨.privateRow 9 18, 66523237806771311038387200⟩, ⟨.privateRow 9 19, 144842141493671219026228800⟩, ⟨.privateRow 9 20, 249506808228709406978803200⟩, ⟨.privateRow 9 21, 411845171707090146346120800⟩, ⟨.privateRow 9 22, 356403556894782763324358400⟩, ⟨.privateRow 10 12, 133534084395586435961400⟩, ⟨.privateRow 10 13, 881147306344268810246400⟩, ⟨.privateRow 10 14, 3243901172146441224818400⟩, ⟨.privateRow 10 15, 8871874290087254916069600⟩, ⟨.privateRow 10 16, 24788485764263618636639400⟩, ⟨.privateRow 10 17, 56519813365986961306087200⟩, ⟨.privateRow 10 18, 112285880332249706492810400⟩, ⟨.privateRow 10 19, 185621496710750698230753120⟩, ⟨.privateRow 10 20, 279327249124465246190085600⟩, ⟨.privateRow 10 21, 302672915391478991872312800⟩, ⟨.privateRow 11 10, 40996307677307792040000⟩, ⟨.privateRow 11 11, 281280222119306239830000⟩, ⟨.privateRow 11 12, 1088514084450214769256000⟩, ⟨.privateRow 11 14, 15893812971962483109552000⟩, ⟨.privateRow 11 15, 20167791925954257395811000⟩, ⟨.privateRow 11 16, 48859009048789928383824000⟩, ⟨.privateRow 11 18, 320702089375993513509921600⟩, ⟨.privateRow 11 19, 106785815694262093112724000⟩, ⟨.privateRow 11 20, 217266765253838861881320000⟩, ⟨.privateRow 12 8, 13958266661559557766000⟩, ⟨.privateRow 12 9, 90191876890077142488000⟩, ⟨.privateRow 12 10, 381060679860575927011800⟩, ⟨.privateRow 12 11, 1183153439567102878274400⟩, ⟨.privateRow 12 12, 644871919764051568789200⟩, ⟨.privateRow 12 13, 15911183259363535003660800⟩, ⟨.privateRow 12 14, 21065816045625684580447200⟩, ⟨.privateRow 12 16, 111191552225983437163956000⟩, ⟨.privateRow 12 18, 201112101886416264248304600⟩, ⟨.privateRow 12 20, 402986325132553680350632800⟩, ⟨.privateRow 13 6, 3474057480210378821760⟩, ⟨.privateRow 13 7, 29777635544660389900800⟩, ⟨.privateRow 13 8, 136289947300561015315200⟩, ⟨.privateRow 13 9, 438599756876560326247200⟩, ⟨.privateRow 13 10, 1492265599454003630256000⟩, ⟨.privateRow 13 11, 755607501945757393732800⟩, ⟨.privateRow 13 12, 15830121918158626164486400⟩, ⟨.privateRow 13 13, 21261231778887518389171200⟩, ⟨.privateRow 13 14, 3461650132066770325968000⟩, ⟨.privateRow 13 15, 64209267377988326573179200⟩, ⟨.privateRow 13 16, 37957552028778599006549760⟩, ⟨.privateRow 13 17, 37754319666186291845476800⟩, ⟨.privateRow 14 5, 11290686810683731170720⟩, ⟨.privateRow 14 6, 54437239980082275287400⟩, ⟨.privateRow 14 7, 195415733261833808724000⟩, ⟨.privateRow 14 8, 705667925667733198170000⟩, ⟨.privateRow 14 9, 2240174905847022116372400⟩, ⟨.privateRow 14 10, 1693603021602559675608000⟩, ⟨.privateRow 14 11, 19344710068971459405833600⟩, ⟨.privateRow 14 13, 78498500051278640964430800⟩, ⟨.privateRow 14 15, 138519791136873355867978320⟩, ⟨.privateRow 14 16, 34337801262991897422952200⟩, ⟨.privateRow 15 3, 10585018885015997972550⟩, ⟨.privateRow 15 4, 22581373621367462341440⟩, ⟨.privateRow 15 5, 96777315520146267177600⟩, ⟨.privateRow 15 6, 364776035422089776284800⟩, ⟨.privateRow 15 7, 1256088907688565092742600⟩, ⟨.privateRow 15 8, 3741323038631109101570400⟩, ⟨.privateRow 15 9, 3302525892124991367435600⟩, ⟨.privateRow 15 10, 25930944041870302588753600⟩, ⟨.privateRow 15 11, 11304800169197085834683400⟩, ⟨.privateRow 15 12, 78002516309237891345145600⟩, ⟨.privateRow 15 13, 64159327801710302377616400⟩, ⟨.privateRow 15 14, 88744798331974127001859200⟩, ⟨.privateRow 16 2, 26462547212539994931375⟩, ⟨.privateRow 16 3, 56453434053418655853600⟩, ⟨.privateRow 16 4, 211700377700319959451000⟩, ⟨.privateRow 16 5, 814232221924307536350000⟩, ⟨.privateRow 16 6, 2610971324970612833229000⟩, ⟨.privateRow 16 7, 7351776752865656773662000⟩, ⟨.privateRow 16 8, 7494193370591326564565400⟩, ⟨.privateRow 16 9, 41258051387373467653006000⟩, ⟨.privateRow 16 10, 36730015531005512964748500⟩, ⟨.privateRow 16 11, 102281525340354586123326000⟩, ⟨.privateRow 16 12, 156093745157702583435204000⟩, ⟨.privateRow 16 13, 165634375512730336274462400⟩, ⟨.privateRow 16 16, 795570019397802407616858000⟩, ⟨.privateRow 17 1, 84680151080127983780400⟩, ⟨.privateRow 17 2, 180650988970939698731520⟩, ⟨.privateRow 17 3, 677441208641023870243200⟩, ⟨.privateRow 17 4, 2188656212532538657708800⟩, ⟨.privateRow 17 5, 6661505218303401390724800⟩, ⟨.privateRow 17 6, 17859813682354265670048000⟩, ⟨.privateRow 17 7, 21000677467871739977539200⟩, ⟨.privateRow 17 8, 81744572509350213676012800⟩, ⟨.privateRow 17 9, 108051872778243307303790400⟩, ⟨.privateRow 17 10, 194135294933413411958265600⟩, ⟨.privateRow 17 11, 350011291131195666292320000⟩, ⟨.privateRow 17 16, 6278525121685009229413977600⟩, ⟨.privateRow 18 0, 359890642090543931066700⟩, ⟨.privateRow 18 1, 767766703126493719608960⟩, ⟨.privateRow 18 2, 2056517954803108177524000⟩, ⟨.privateRow 18 3, 7530019588355996096164800⟩, ⟨.privateRow 18 4, 21593438525432635864002000⟩, ⟨.privateRow 18 5, 55488593544142046099011200⟩, ⟨.privateRow 18 7, 364689183985084516814256000⟩, ⟨.privateRow 18 11, 3135943098920163597742797120⟩, ⟨.privateRow 19 0, 6909900328138443476480640⟩, ⟨.privateRow 19 1, 9871286183054919252115200⟩, ⟨.privateRow 19 2, 34549501640692217382403200⟩, ⟨.privateRow 19 3, 95011129511903597801608800⟩, ⟨.privateRow 19 4, 238705647699328047369331200⟩, ⟨.privateRow 19 5, 110558405250215095623690240⟩, ⟨.privateRow 19 9, 7289944846186057867687075200⟩, ⟨.privateRow 19 11, 10649883880743376008125786400⟩, ⟨.privateRow 20 0, 164110132793288032566415200⟩, ⟨.hall 19 5, 362485018587372467536807200⟩, ⟨.hall 12 9, 3700929637978004520000⟩, ⟨.hall 13 11, 3569009225388342445710⟩, ⟨.hall 14 11, 16368672531563994642000⟩, ⟨.hall 17 12, 1189616540009182576536960⟩, ⟨.hall 18 13, 154485628764809486295602880⟩, ⟨.hall 15 16, 1452845729315921290350000⟩, ⟨.hall 9 17, 2305761239939475661200⟩, ⟨.hall 8 18, 4217171683379454667296⟩, ⟨.hall 10 19, 6002606374615335513600⟩, ⟨.hall 5 24, 3627991312845414892886080⟩, ⟨.hall 4 28, 40160023010573822522387020800⟩, ⟨.hall 3 29, 55631607541842608429145632640⟩]
  caps := #[0, 704443707777287988404294400, 244364658230382010498457280, 0, 6843878973027847397687040, 1897514794968657568704000, 594392329790422713950400, 2526075132333664675661040, 0, 537563969681579773302656, 98128296902262266640000, 395929019626990391226000, 0, 0, 983562159592894527914840, 1277100190595587682984660, 15328228708471226679685125, 530662280102135365023840, 1631317927243850872532220, 613888756691314531520396160, 0, 642997581813066480000000] }

theorem case_54_33_21_checked :
    (Witness.linear .conditional case_54_33_21).check 54 33 21 = true := by
  change case_54_33_21.check 54 33 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_34_1_checked :
    (Witness.rising).check 54 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_34_2_checked :
    (Witness.rising).check 54 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_34_3_checked :
    (Witness.rising).check 54 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_34_4_checked :
    (Witness.rising).check 54 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_34_5_checked :
    (Witness.rising).check 54 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_34_6_checked :
    (Witness.rising).check 54 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_34_7_checked :
    (Witness.rising).check 54 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_34_8_checked :
    (Witness.rising).check 54 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_34_9_checked :
    (Witness.rising).check 54 34 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_34_10_checked :
    (Witness.rising).check 54 34 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_34_11_checked :
    (Witness.linear .positive case_54_34_11).check 54 34 11 = true := by
  change case_54_34_11.check 54 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_34_12_checked :
    (Witness.linear .positive case_54_34_12).check 54 34 12 = true := by
  change case_54_34_12.check 54 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_34_13_checked :
    (Witness.linear .positive case_54_34_13).check 54 34 13 = true := by
  change case_54_34_13.check 54 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_34_14_checked :
    (Witness.linear .positive case_54_34_14).check 54 34 14 = true := by
  change case_54_34_14.check 54 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_54_34_15_checked :
    (Witness.linear .positive case_54_34_15).check 54 34 15 = true := by
  change case_54_34_15.check 54 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_16 : Certificate := {
  objectiveScale := 196234042469963675777600000
  eta := 26831790998665257634386727454884800
  rows := #[⟨.count 2, 4857468678821663148835881473863680⟩, ⟨.count 3, 858103030778861087341311370340160⟩, ⟨.count 4, 147941227039007580633943995386880⟩, ⟨.count 5, 26958287578842905112220995201600⟩, ⟨.count 6, 4708551586168941797881133098560⟩, ⟨.count 7, 859981572085260095208859801680⟩, ⟨.count 8, 157639829907609051822245986560⟩, ⟨.count 9, 33779963551630511104766997120⟩, ⟨.count 10, 7677264443552388887447044800⟩, ⟨.count 11, 2814996962635875925397249760⟩, ⟨.path 9, 3602608318882585960195248000⟩, ⟨.path 10, 265069675799923794783984000⟩, ⟨.privateRow 2 32, 496447234336537806451208173174080⟩, ⟨.privateRow 3 31, 821467409197356626547780274296960⟩, ⟨.privateRow 5 28, 179074389696519709399856228420040⟩, ⟨.privateRow 6 21, 343840149831961261470918236310⟩, ⟨.privateRow 6 22, 1107433209848394712269970423440⟩, ⟨.privateRow 6 23, 2221788482333747219970249692520⟩, ⟨.privateRow 6 26, 32965282578814335753616844911680⟩, ⟨.privateRow 7 18, 13331021330197040989559832792⟩, ⟨.privateRow 7 19, 233220264229808799882713414640⟩, ⟨.privateRow 7 20, 550340284162464445426845057990⟩, ⟨.privateRow 7 22, 3887778900348967117347449275680⟩, ⟨.privateRow 7 23, 744968839040422878828343597200⟩, ⟨.privateRow 7 25, 14202910786259165544040412705760⟩, ⟨.privateRow 8 16, 18809297886703352774245259760⟩, ⟨.privateRow 8 17, 107063717812251147695942065872⟩, ⟨.privateRow 8 18, 244644087882410476257209131920⟩, ⟨.privateRow 8 20, 1090074061912140144063354049920⟩, ⟨.privateRow 8 21, 2020620458652046383005286973560⟩, ⟨.privateRow 8 23, 4315742218341127278124658538300⟩, ⟨.privateRow 9 14, 12667486331861441664287623920⟩, ⟨.privateRow 9 15, 47826514052055992995133071680⟩, ⟨.privateRow 9 16, 109190604406242698395131099024⟩, ⟨.privateRow 9 17, 161427912240044983623089199200⟩, ⟨.privateRow 9 18, 101183501934745095762890033040⟩, ⟨.privateRow 9 19, 799325089914177530625895253280⟩, ⟨.privateRow 9 20, 1263464470063068977849132267280⟩, ⟨.privateRow 9 21, 545171078430481304218600703520⟩, ⟨.privateRow 9 22, 1968777597923502334712554290480⟩, ⟨.privateRow 9 23, 1734142388130463861745646491040⟩, ⟨.privateRow 10 12, 6948908586087162249407196960⟩, ⟨.privateRow 10 13, 22946490392395473452480611680⟩, ⟨.privateRow 10 14, 51786638337417023222597338560⟩, ⟨.privateRow 10 15, 92075991559671650723448223968⟩, ⟨.privateRow 10 16, 131935211178085497917608473600⟩, ⟨.privateRow 10 17, 119029587476910162709126890420⟩, ⟨.privateRow 10 18, 576599118112896559680070431360⟩, ⟨.privateRow 10 19, 860109526492652635023650585760⟩, ⟨.privateRow 10 20, 616381971291342795810165070176⟩, ⟨.privateRow 10 21, 1060422151265673715078623063000⟩, ⟨.privateRow 10 24, 8603142535444806987273158402880⟩, ⟨.privateRow 11 10, 3601002608047191930540637680⟩, ⟨.privateRow 11 11, 12126140762123773217095845120⟩, ⟨.privateRow 11 12, 27360917447438097062762662440⟩, ⟨.privateRow 11 13, 50856060829107642751391636160⟩, ⟨.privateRow 11 14, 82095547783053545169767065728⟩, ⟨.privateRow 11 15, 131252787671991952238724291840⟩, ⟨.privateRow 11 16, 60938286520697086794110918100⟩, ⟨.privateRow 11 17, 544427724254200834818387576960⟩, ⟨.privateRow 11 18, 611963279089387087539389993280⟩, ⟨.privateRow 11 20, 1811066682234008538548757868320⟩, ⟨.privateRow 12 8, 1897516471110108957119627616⟩, ⟨.privateRow 12 9, 7059833652324895177980404160⟩, ⟨.privateRow 12 10, 16553144532422928518575280640⟩, ⟨.privateRow 12 11, 31616586256271458310248740360⟩, ⟨.privateRow 12 12, 53257467788050460689586351520⟩, ⟨.privateRow 12 13, 19861367458597569029191706640⟩, ⟨.privateRow 12 14, 285218272498180663206607762720⟩, ⟨.privateRow 12 16, 444635472622057164025841783520⟩, ⟨.privateRow 12 17, 599177316454384405305851643360⟩, ⟨.privateRow 12 18, 285002803594867793691330442368⟩, ⟨.privateRow 12 20, 2566130379309511635251944753440⟩, ⟨.privateRow 13 6, 1084946746015910512913523345⟩, ⟨.privateRow 13 7, 4535272884246688990917791280⟩, ⟨.privateRow 13 8, 11528082799365968075436356160⟩, ⟨.privateRow 13 9, 23061321270824675850369776880⟩, ⟨.privateRow 13 10, 14270470713362426566249946700⟩, ⟨.privateRow 13 11, 125864485405128331149201273360⟩, ⟨.privateRow 13 13, 324662983024004356729149472320⟩, ⟨.privateRow 13 15, 536726087542573676442408954240⟩, ⟨.privateRow 13 16, 601001851522759510072312823760⟩, ⟨.privateRow 13 17, 555117401031794732488337652672⟩, ⟨.privateRow 14 4, 666294799279359987944166960⟩, ⟨.privateRow 14 5, 3267407188773784556264664900⟩, ⟨.privateRow 14 6, 9235870986933897679041452784⟩, ⟨.privateRow 14 7, 19915624769668782057232243200⟩, ⟨.privateRow 14 8, 36393889302649538749778729040⟩, ⟨.privateRow 14 9, 24687076537401927758444134800⟩, ⟨.privateRow 14 10, 137429126606606453457434996400⟩, ⟨.privateRow 14 12, 635958454016444170373409888240⟩, ⟨.privateRow 14 14, 537099505507004966105982058800⟩, ⟨.privateRow 14 16, 892219989681161436164004495360⟩, ⟨.privateRow 14 18, 2572683811391838542168213483040⟩, ⟨.privateRow 15 2, 451789635978597370742768480⟩, ⟨.privateRow 15 3, 2631010233051831747266710560⟩, ⟨.privateRow 15 4, 8513410952971694204934043545⟩, ⟨.privateRow 15 5, 20330533619036881683424581600⟩, ⟨.privateRow 15 6, 39789758654400754151845252560⟩, ⟨.privateRow 15 7, 78976303673950963462533951600⟩, ⟨.privateRow 15 8, 49301544026164438082304610380⟩, ⟨.privateRow 15 9, 256164723599864709211149728160⟩, ⟨.privateRow 15 10, 45743700642832983787705308600⟩, ⟨.privateRow 15 11, 953953816368808348323355645520⟩, ⟨.privateRow 15 12, 424145757627156944120445333630⟩, ⟨.privateRow 15 13, 626470871660893625587811750160⟩, ⟨.privateRow 15 17, 8044114468598926186074992786400⟩, ⟨.privateRow 16 1, 3388422269839480280570763600⟩, ⟨.privateRow 16 2, 8969353067222153683863786000⟩, ⟨.privateRow 16 3, 24396640342844258020109497920⟩, ⟨.privateRow 16 4, 52859387409495892376903912160⟩, ⟨.privateRow 16 6, 417088716630548949613025839440⟩, ⟨.privateRow 16 8, 526191174667254565024634398320⟩, ⟨.privateRow 16 9, 131741857851358993308591288768⟩, ⟨.privateRow 16 10, 1549864346224578280333067270640⟩, ⟨.privateRow 16 13, 2049317788798917673689197825280⟩, ⟨.privateRow 16 18, 25634769840243604114630054939440⟩, ⟨.privateRow 17 0, 20330533619036881683424581600⟩, ⟨.privateRow 17 1, 33007219287377525556618732480⟩, ⟨.privateRow 17 2, 85388241199954903070383242720⟩, ⟨.privateRow 17 3, 198426008121799965230223916416⟩, ⟨.privateRow 17 6, 2919464627693696209739769917760⟩, ⟨.privateRow 17 7, 93150808581768985167690810240⟩, ⟨.privateRow 17 8, 856322076033833456505843376992⟩, ⟨.privateRow 17 9, 3651363837979023950343054855360⟩, ⟨.privateRow 17 10, 2323779992655915576415429676880⟩, ⟨.privateRow 17 13, 8270461076224203468817119794880⟩, ⟨.privateRow 18 0, 406610672380737633668491632000⟩, ⟨.privateRow 18 1, 328338117947445639187306992840⟩, ⟨.privateRow 18 2, 986166417414082340857315038144⟩, ⟨.privateRow 18 3, 69123814304725397723643577440⟩, ⟨.privateRow 18 6, 23766024154588314017347273625280⟩, ⟨.privateRow 19 2, 22929356687938910502042912402240⟩, ⟨.privateRow 19 12, 516354892856298720995617523476800⟩, ⟨.hall 15 6, 1621452222402841967962643820⟩, ⟨.hall 16 6, 6485532217837557279101506800⟩, ⟨.hall 16 16, 85467968782774655547573143040⟩, ⟨.hall 10 17, 6967247426547203139271200⟩, ⟨.hall 6 19, 17801371162662754848164984⟩, ⟨.hall 8 20, 36721427316667741081859040⟩, ⟨.hall 11 21, 3065342542316932084770522960⟩, ⟨.hall 5 22, 183246224702177933357061000⟩]
  caps := #[0, 0, 1252872212788478567659649795520, 0, 45011293727421199581145142400, 32314186842711647467310676960, 0, 1875823899956392691094737948, 7327695519983141323935919004, 0, 5417564962385264659441881676, 2749848804335133150837235160, 1332260311619897470551936888, 7353420271222472604304452844, 196234042469963675777600000, 74525562715755718967578508330, 78475546651639797989725203808, 0, 116523001256537099019856316256, 0, 0] }

theorem case_54_34_16_checked :
    (Witness.linear .positive case_54_34_16).check 54 34 16 = true := by
  change case_54_34_16.check 54 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_17 : Certificate := {
  objectiveScale := 3359881720048453600000
  eta := 262477255264226962850166756480
  rows := #[⟨.count 2, 48571854494942264214041913600⟩, ⟨.count 3, 9073054205440513856432504640⟩, ⟨.count 4, 1687089623913960997910699520⟩, ⟨.count 5, 328543388088083497118790000⟩, ⟨.count 6, 63698765125783718029619520⟩, ⟨.count 7, 12832518217087496593345680⟩, ⟨.count 8, 2568882238082390420910720⟩, ⟨.count 9, 570862719573864537980160⟩, ⟨.count 10, 129741527175878304086400⟩, ⟨.count 11, 71357839946733067247520⟩, ⟨.path 10, 18900225518854564684800⟩, ⟨.privateRow 2 32, 4194841979108650091212710720⟩, ⟨.privateRow 3 29, 631971459397877944680054720⟩, ⟨.privateRow 3 30, 1345713717608790004198563840⟩, ⟨.privateRow 4 26, 75201648925197088469919744⟩, ⟨.privateRow 4 27, 296384788218755794812574320⟩, ⟨.privateRow 4 28, 496809139006921554858844800⟩, ⟨.privateRow 4 29, 836742031215391946544419520⟩, ⟨.privateRow 5 23, 3931477181827150419303840⟩, ⟨.privateRow 5 24, 53752275102097425489395760⟩, ⟨.privateRow 5 25, 107947761676752893029806672⟩, ⟨.privateRow 5 26, 179346037732789109015433600⟩, ⟨.privateRow 5 27, 306176669589224165707095120⟩, ⟨.privateRow 5 28, 364721812941077162213282640⟩, ⟨.privateRow 6 21, 6416259108543748296672840⟩, ⟨.privateRow 6 22, 22278370697020519042721760⟩, ⟨.privateRow 6 23, 41203206082576118579838840⟩, ⟨.privateRow 6 24, 64657338775734832232977872⟩, ⟨.privateRow 6 25, 109243897552896469492949820⟩, ⟨.privateRow 6 26, 136674049444642734801416640⟩, ⟨.privateRow 6 27, 133478803944805687456888800⟩, ⟨.privateRow 7 18, 298173831205991745284280⟩, ⟨.privateRow 7 19, 3798955479068931865844160⟩, ⟨.privateRow 7 20, 8925888854527512152815530⟩, ⟨.privateRow 7 21, 16076144656026750711358800⟩, ⟨.privateRow 7 22, 24619587445749046820509440⟩, ⟨.privateRow 7 23, 40472128022359946226586272⟩, ⟨.privateRow 7 24, 50871768646311147209334660⟩, ⟨.privateRow 7 25, 52110478451259495632645280⟩, ⟨.privateRow 7 26, 33019990937256122903703600⟩, ⟨.privateRow 8 16, 340571508836680548226800⟩, ⟨.privateRow 8 17, 1732806213373167982993944⟩, ⟨.privateRow 8 18, 3801787139384278416131760⟩, ⟨.privateRow 8 19, 6570867761761669942375800⟩, ⟨.privateRow 8 20, 9986699600164213554307680⟩, ⟨.privateRow 8 21, 16196247505687663679985720⟩, ⟨.privateRow 8 22, 20448778334068805970897648⟩, ⟨.privateRow 8 23, 20304278708176671509721420⟩, ⟨.privateRow 9 14, 220680727242674485746960⟩, ⟨.privateRow 9 15, 787819384462416590924640⟩, ⟨.privateRow 9 16, 1712588158721593613940480⟩, ⟨.privateRow 9 17, 2936242969660016211555360⟩, ⟨.privateRow 9 18, 4408328778931509487735680⟩, ⟨.privateRow 9 19, 7141447315303999825327200⟩, ⟨.privateRow 9 20, 9214411443492031072536240⟩, ⟨.privateRow 9 21, 33300325308475431382176⟩, ⟨.privateRow 10 12, 118763397953303986048320⟩, ⟨.privateRow 10 13, 385981043348237954657040⟩, ⟨.privateRow 10 14, 833884179212236008991680⟩, ⟨.privateRow 10 15, 1453753812005716397288112⟩, ⟨.privateRow 10 16, 2199118885631137254264480⟩, ⟨.privateRow 10 17, 3473018505589292352512820⟩, ⟨.privateRow 11 10, 60237137617372069754400⟩, ⟨.privateRow 11 11, 207087437607651908445600⟩, ⟨.privateRow 11 12, 454095345115574064302400⟩, ⟨.privateRow 11 13, 809705076420367779593760⟩, ⟨.privateRow 11 14, 1032742556319991300527744⟩, ⟨.privateRow 12 8, 30657442347485317780416⟩, ⟨.privateRow 12 9, 120628729433763042251760⟩, ⟨.privateRow 12 10, 281771983379407496310720⟩, ⟨.privateRow 12 11, 294020729410150138195800⟩, ⟨.privateRow 13 6, 16352838321126327910890⟩, ⟨.privateRow 13 7, 76907894164812305811216⟩, ⟨.privateRow 13 8, 95993284690248054749640⟩, ⟨.privateRow 14 4, 9094626659877743864880⟩, ⟨.privateRow 14 5, 34510860093286081630125⟩, ⟨.privateRow 15 2, 5726246415478579470480⟩, ⟨.privateRow 15 3, 3031542219959247954960⟩, ⟨.hall 6 27, 7763563086585636923512920⟩, ⟨.hall 5 28, 94791098421194719330987200⟩, ⟨.hall 4 29, 307155857726271002796547200⟩, ⟨.hall 3 30, 750181134916996847098594560⟩, ⟨.hall 2 31, 1567151961180158281256628300⟩, ⟨.assumptionRow 17, 4216628245195813013424⟩]
  caps := #[0, 0, 0, 20817186812275124035007100, 0, 1634837466472713205951248, 0, 0, 87629968852583644708364, 0, 26155192487051897476752, 0, 21150245606520049120816, 9290003015538985440272, 42134380995172505910585, 0, 381901352038212414771792, 49541479275579444586576, 3359881720048453600000, 0, 0] }

theorem case_54_34_17_checked :
    (Witness.linear .conditional case_54_34_17).check 54 34 17 = true := by
  change case_54_34_17.check 54 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_18 : Certificate := {
  objectiveScale := 229852767333204947131200000
  eta := 22766541208630459209159141366455040
  rows := #[⟨.count 2, 3753667105826826518373714500269440⟩, ⟨.count 3, 619497719962733583922697724257280⟩, ⟨.count 4, 100372695597677164784172902691840⟩, ⟨.count 5, 16582272560921983831780157092800⟩, ⟨.count 6, 2677137979715115461998242229440⟩, ⟨.count 7, 479487399351960978268341891840⟩, ⟨.count 8, 104503663961324828596946309760⟩, ⟨.count 9, 36883646103996998328333991680⟩, ⟨.count 10, 12573970262726249430113860800⟩, ⟨.count 11, 4610455762999624791041748960⟩, ⟨.path 8, 8710668681476446196172460800⟩, ⟨.path 9, 651666223676160589764067200⟩, ⟨.privateRow 2 32, 332164895901070967695393845572160⟩, ⟨.privateRow 3 29, 49134139339149556911997589972160⟩, ⟨.privateRow 3 30, 103249619993788930653782954042880⟩, ⟨.privateRow 4 26, 5713891508944201657697740877760⟩, ⟨.privateRow 4 27, 21247285383783770849515900082160⟩, ⟨.privateRow 4 28, 37519888999290946549497753036480⟩, ⟨.privateRow 4 29, 66389026168606930449404171107680⟩, ⟨.privateRow 5 23, 329647587054473172559485050640⟩, ⟨.privateRow 5 24, 3492932513334771293079796142640⟩, ⟨.privateRow 5 25, 7482001294054557765062251603920⟩, ⟨.privateRow 5 26, 13258326058122712675138682832180⟩, ⟨.privateRow 5 27, 24314006875472354606357170098720⟩, ⟨.privateRow 5 28, 31326510090994783913531670266880⟩, ⟨.privateRow 6 21, 355453332505707183542677062180⟩, ⟨.privateRow 6 22, 1367109906485650646372236703520⟩, ⟨.privateRow 6 23, 2759272395344849518460874868320⟩, ⟨.privateRow 6 24, 4715625381682271787664067966832⟩, ⟨.privateRow 6 25, 8663238480999753300067073035380⟩, ⟨.privateRow 6 26, 11986075059263487509999592800880⟩, ⟨.privateRow 6 27, 13124302670456626360032427546440⟩, ⟨.privateRow 7 19, 189479974280950188171517381200⟩, ⟨.privateRow 7 20, 520336586275918963396113578310⟩, ⟨.privateRow 7 21, 1044801412278401366337267090000⟩, ⟨.privateRow 7 22, 1768823308026058430248838615880⟩, ⟨.privateRow 7 23, 3210567711494172050321772584112⟩, ⟨.privateRow 7 24, 4519454148058513149332853486480⟩, ⟨.privateRow 7 25, 5325735042802138008623368870080⟩, ⟨.privateRow 7 26, 4388879454484988061500849667720⟩, ⟨.privateRow 8 15, 64034107819439233208913180⟩, ⟨.privateRow 8 16, 1117686245575666616010120960⟩, ⟨.privateRow 8 17, 78608270759143602687261819768⟩, ⟨.privateRow 8 18, 209690358406057009014787693440⟩, ⟨.privateRow 8 19, 413884455890945483845810338930⟩, ⟨.privateRow 8 20, 703972685907537947260731811440⟩, ⟨.privateRow 8 21, 1274919086685035133189461413800⟩, ⟨.privateRow 8 22, 1822513163113751679898803363888⟩, ⟨.privateRow 8 23, 2195345352481654671334379463120⟩, ⟨.privateRow 8 24, 1846231396650071971879384805760⟩, ⟨.privateRow 9 15, 30736371753330831940278326400⟩, ⟨.privateRow 9 16, 88520750649592795988001580032⟩, ⟨.privateRow 9 17, 177132572030306572218789169920⟩, ⟨.privateRow 9 18, 301728716045197666880398904160⟩, ⟨.privateRow 9 19, 550181054384621891730982042560⟩, ⟨.privateRow 9 20, 806744379714508419454694183760⟩, ⟨.privateRow 9 21, 1005694083768984821085906839808⟩, ⟨.privateRow 9 22, 114749121212435105910372418560⟩, ⟨.privateRow 10 13, 11211790150930905741851525880⟩, ⟨.privateRow 10 14, 39017410754641452777080586240⟩, ⟨.privateRow 10 15, 82485244923484196261546926848⟩, ⟨.privateRow 10 16, 143110409693917646291629237920⟩, ⟨.privateRow 10 17, 262534020777171816226252318620⟩, ⟨.privateRow 10 18, 398894237572772731921040669760⟩, ⟨.privateRow 10 19, 151306775494805868142370124960⟩, ⟨.privateRow 11 11, 4062359623342326738959862720⟩, ⟨.privateRow 11 12, 17568630672642509620409088840⟩, ⟨.privateRow 11 13, 41684616567947020838013829440⟩, ⟨.privateRow 11 14, 76030606855284721554088478304⟩, ⟨.privateRow 11 15, 142365285530200535214289157280⟩, ⟨.privateRow 11 16, 86708003270049761695160165100⟩, ⟨.privateRow 12 9, 1500227668912576320894537360⟩, ⟨.privateRow 12 10, 8156960196076259245689248160⟩, ⟨.privateRow 12 11, 22411937736803731623119613000⟩, ⟨.privateRow 12 12, 45126582165117539621408633760⟩, ⟨.privateRow 12 13, 41135510863207763413405826832⟩, ⟨.privateRow 13 7, 563500148811065252238435984⟩, ⟨.privateRow 13 8, 3951819225428249820892927680⟩, ⟨.privateRow 13 9, 12767415959075884036730997120⟩, ⟨.privateRow 13 10, 18249720728540181464540256300⟩, ⟨.privateRow 14 5, 178380728925580721081972430⟩, ⟨.privateRow 14 6, 1997864163966504076118091216⟩, ⟨.privateRow 14 7, 7441024692324224365133707080⟩, ⟨.privateRow 15 4, 1040554252065887539644839175⟩, ⟨.privateRow 15 5, 1331909442644336050745394144⟩, ⟨.privateRow 16 2, 587607107048971787093556240⟩, ⟨.hall 6 27, 2249024230293721731401508397440⟩, ⟨.hall 5 28, 10416450399715014355484668684800⟩, ⟨.hall 4 29, 28337705301700893815659005807744⟩, ⟨.hall 3 30, 63325849274628609844956013833600⟩, ⟨.hall 2 31, 125835474367430259234297975239760⟩, ⟨.assumptionRow 18, 233898431430233057761761488⟩]
  caps := #[0, 5608290472469908070296266417600, 924116900550253171604217254880, 373713162028977698664710893920, 10622834656054658380751856448, 28338074529516433023867645120, 0, 7729607596731526154980584682, 726278382932409186827375428, 0, 950444462118533640782661368, 1484422558643002631489686080, 4461855296406273055601157000, 705740958387727283915845952, 10246923791901606874095972798, 15279497090617912452453195042, 0, 23610104409767659784424616192, 3213893078567841149206238512, 229852767333204947131200000, 0] }

theorem case_54_34_18_checked :
    (Witness.linear .conditional case_54_34_18).check 54 34 18 = true := by
  change case_54_34_18.check 54 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_19 : Certificate := {
  objectiveScale := 207231445404244800000
  eta := 48078088128203377164576495840
  rows := #[⟨.count 2, 3582668781115257316378896000⟩, ⟨.count 3, 427266425007078835508890560⟩, ⟨.count 4, 67958829747807204868421760⟩, ⟨.count 5, 11025097283933117558573400⟩, ⟨.count 6, 1756210186821204566852400⟩, ⟨.count 7, 318719626497181569539880⟩, ⟨.count 8, 76052406950661850188480⟩, ⟨.count 9, 24016549563366900059520⟩, ⟨.count 10, 8187460078420534111200⟩, ⟨.count 11, 3002068695420862507440⟩, ⟨.path 2, 1042399237089348769571740800⟩, ⟨.path 8, 7588054132344627177600⟩, ⟨.privateRow 2 32, 317132532846869073560946720⟩, ⟨.privateRow 3 29, 48751816609963446609710080⟩, ⟨.privateRow 3 30, 94874376981385517822626320⟩, ⟨.privateRow 4 26, 4818520394063512381941696⟩, ⟨.privateRow 4 27, 18349144211194881789224520⟩, ⟨.privateRow 4 28, 34161540374759134759662240⟩, ⟨.privateRow 4 29, 63353656369031601782008800⟩, ⟨.privateRow 5 23, 168187324769649749523960⟩, ⟨.privateRow 5 24, 2663585450012160259726140⟩, ⟨.privateRow 5 25, 6192267029088099065346240⟩, ⟨.privateRow 5 26, 11773112733875482466677200⟩, ⟨.privateRow 5 27, 23203656073284606511672080⟩, ⟨.privateRow 5 28, 32197186758388750392294000⟩, ⟨.privateRow 6 21, 180228360221620530394575⟩, ⟨.privateRow 6 22, 986513129634133429528200⟩, ⟨.privateRow 6 23, 2199599054975446954409580⟩, ⟨.privateRow 6 24, 4100425562118842070162048⟩, ⟨.privateRow 6 25, 8190769176868895743736610⟩, ⟨.privateRow 6 26, 12448133439427336403072320⟩, ⟨.privateRow 6 27, 15026437900943652161198220⟩, ⟨.privateRow 7 19, 88378360959373962917440⟩, ⟨.privateRow 7 20, 349615916820887946178950⟩, ⟨.privateRow 7 21, 800051307329659858232760⟩, ⟨.privateRow 7 22, 1498044191986023966063780⟩, ⟨.privateRow 7 23, 2997079543160377359749064⟩, ⟨.privateRow 7 24, 4685782497138957317193090⟩, ⟨.privateRow 7 25, 6205585730681275749010200⟩, ⟨.privateRow 7 26, 6047309997794920275701280⟩, ⟨.privateRow 8 17, 32572445345316358205724⟩, ⟨.privateRow 8 18, 127865888879036736428000⟩, ⟨.privateRow 8 19, 300331955737728786681810⟩, ⟨.privateRow 8 20, 575467977781746763033320⟩, ⟨.privateRow 8 21, 1163134837881394173715920⟩, ⟨.privateRow 8 22, 1866786383769206335876440⟩, ⟨.privateRow 8 23, 2547630546651529445376270⟩, ⟨.privateRow 8 24, 2807267793406886540290560⟩, ⟨.privateRow 8 25, 1755709842038634423101160⟩, ⟨.privateRow 9 15, 10097867430051992070480⟩, ⟨.privateRow 9 16, 47933030170219771368792⟩, ⟨.privateRow 9 17, 118748495063314116960960⟩, ⟨.privateRow 9 18, 234119662844279763601050⟩, ⟨.privateRow 9 19, 483618971267084660127120⟩, ⟨.privateRow 9 20, 802608625107240592961320⟩, ⟨.privateRow 9 21, 1137183621825422717818272⟩, ⟨.privateRow 9 22, 1335170052288428600183940⟩, ⟨.privateRow 9 23, 11674711593303354195600⟩, ⟨.privateRow 10 13, 2615438636162115063300⟩, ⟨.privateRow 10 14, 17913170232180683722080⟩, ⟨.privateRow 10 15, 49643299608823171827576⟩, ⟨.privateRow 10 16, 102525194537554910481360⟩, ⟨.privateRow 10 17, 217718209251999369573660⟩, ⟨.privateRow 10 18, 377558873330592630156480⟩, ⟨.privateRow 10 19, 561432331933025847414120⟩, ⟨.privateRow 10 20, 282467372705508426836400⟩, ⟨.privateRow 11 11, 461856722372440385760⟩, ⟨.privateRow 11 12, 6481739228749589504700⟩, ⟨.privateRow 11 13, 21585122024926862656800⟩, ⟨.privateRow 11 14, 48606221332223237506824⟩, ⟨.privateRow 11 15, 107195079174876252159600⟩, ⟨.privateRow 11 16, 198204762731763763275300⟩, ⟨.privateRow 11 17, 212873962038933886891200⟩, ⟨.privateRow 12 10, 2104013957474450646240⟩, ⟨.privateRow 12 11, 9506550868832731273560⟩, ⟨.privateRow 12 12, 24623028087694347030720⟩, ⟨.privateRow 12 13, 59340891212819048897064⟩, ⟨.privateRow 12 14, 114745736802752966951040⟩, ⟨.privateRow 13 8, 500344782570143751240⟩, ⟨.privateRow 13 9, 4002758260561150009920⟩, ⟨.privateRow 13 10, 12967268948276225552970⟩, ⟨.privateRow 13 11, 35751909009102998952240⟩, ⟨.privateRow 13 12, 18812963824637405046624⟩, ⟨.privateRow 14 6, 61947449270589226344⟩, ⟨.privateRow 14 7, 1460189875663888906680⟩, ⟨.privateRow 14 8, 6718915651656216088080⟩, ⟨.privateRow 14 9, 14635084890176704723770⟩, ⟨.privateRow 15 5, 433632144894124584408⟩, ⟨.privateRow 15 6, 3097372463529461317200⟩, ⟨.privateRow 15 7, 3335631883800958341600⟩, ⟨.privateRow 16 4, 1300896434682373753224⟩, ⟨.privateRow 16 5, 464605869529419197580⟩, ⟨.hall 6 27, 4009084048169358255917820⟩, ⟨.hall 5 28, 13034757983028646667002200⟩, ⟨.hall 4 29, 31155602346353063140545984⟩, ⟨.hall 3 30, 64419552157448772534650400⟩, ⟨.hall 2 31, 121661460692038946368700010⟩, ⟨.assumptionRow 19, 157894358525306098696⟩]
  caps := #[0, 0, 3594746833997532997487760, 0, 63598924382432244859872, 0, 11237984812254905612285, 4443535274580739774528, 5658947026213072936708, 615989599906497881064, 2031726281615261591416, 1059619768605531388248, 1864479965132076847632, 2841493871412894816888, 12410695853212578103578, 157894358525306098696, 157894358525306098696, 93944477635397745455176, 19183654944161867719560, 2743345877134121101304, 207231445404244800000] }

theorem case_54_34_19_checked :
    (Witness.linear .conditional case_54_34_19).check 54 34 19 = true := by
  change case_54_34_19.check 54 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_20 : Certificate := {
  objectiveScale := 7384350398808135945192000000
  eta := 2311991303305920182432171352666679680
  rows := #[⟨.count 2, 154923337705417296000457801937287680⟩, ⟨.count 3, 17564209478417094141831691471522560⟩, ⟨.count 4, 2909422986512287669248238968153600⟩, ⟨.count 5, 484665197310240834665614611574800⟩, ⟨.count 6, 72735574662807191731205974203840⟩, ⟨.count 7, 10595339616235693283679610415520⟩, ⟨.count 8, 1321663985393225773431968035200⟩, ⟨.count 9, 132166398539322577343196803520⟩, ⟨.path 2, 55605354557181328048149161960198400⟩, ⟨.path 8, 93911270580242261865545299200⟩, ⟨.path 9, 73169398480265806105744156800⟩, ⟨.privateRow 2 32, 14049420331128529294159163410979520⟩, ⟨.privateRow 3 29, 2080313798164330625446066931494080⟩, ⟨.privateRow 3 30, 4144400499619111090007219144333760⟩, ⟨.privateRow 4 26, 189570670971568350102591948515520⟩, ⟨.privateRow 4 27, 776609757817059464468624417483520⟩, ⟨.privateRow 4 28, 1481056662031648801707863380245120⟩, ⟨.privateRow 4 29, 2819219419509200010211507149751200⟩, ⟨.privateRow 5 23, 5461304396785579356645667916880⟩, ⟨.privateRow 5 24, 108172690271163057781350617147640⟩, ⟨.privateRow 5 25, 258297198212016090321054286345920⟩, ⟨.privateRow 5 26, 504316688693056360384331186298180⟩, ⟨.privateRow 5 27, 1026268413368991498553885868310480⟩, ⟨.privateRow 5 28, 1478479417260132011449671042576480⟩, ⟨.privateRow 6 21, 7660144182008237711849448070680⟩, ⟨.privateRow 6 22, 39804113693425982876526103993440⟩, ⟨.privateRow 6 23, 90179703625573614682489296757320⟩, ⟨.privateRow 6 24, 172646763638608094073795597824784⟩, ⟨.privateRow 6 25, 357747824001795936626763242216820⟩, ⟨.privateRow 6 26, 569364278566755595990404770512080⟩, ⟨.privateRow 6 27, 723275109073170332736588540729720⟩, ⟨.privateRow 7 19, 4179500118888339757333076695440⟩, ⟨.privateRow 7 20, 13937064731684547318855587928330⟩, ⟨.privateRow 7 21, 32078223471328031127477871798560⟩, ⟨.privateRow 7 22, 61680012765943500187134874918920⟩, ⟨.privateRow 7 23, 128575878045670980658706623691040⟩, ⟨.privateRow 7 24, 211804520706796532726838544117200⟩, ⟨.privateRow 7 25, 298449035406361005216542848596240⟩, ⟨.privateRow 7 26, 315548849922139073913755501699280⟩, ⟨.privateRow 8 16, 73092023434625364742828535280⟩, ⟨.privateRow 8 17, 1627849475342656410943707296688⟩, ⟨.privateRow 8 18, 5105539025056053635887195039680⟩, ⟨.privateRow 8 19, 11731144603682996682722707945770⟩, ⟨.privateRow 8 20, 23050449269060425691402775852000⟩, ⟨.privateRow 8 21, 48721674305981942331154577208720⟩, ⟨.privateRow 8 22, 82837493057829414059470983219552⟩, ⟨.privateRow 8 23, 121017612129203470766892556489740⟩, ⟨.privateRow 8 24, 145933731720502012483113137220000⟩, ⟨.privateRow 8 25, 111493371034463537537098436836080⟩, ⟨.privateRow 9 14, 38548532907302418391765734360⟩, ⟨.privateRow 9 15, 585403694540332829949412104480⟩, ⟨.privateRow 9 16, 1937706254140401564492757580496⟩, ⟨.privateRow 9 17, 4549950646011123542240793661920⟩, ⟨.privateRow 9 18, 9091029010638820337391419019900⟩, ⟨.privateRow 9 19, 19663423071572547895837835545920⟩, ⟨.privateRow 9 20, 34696127142471052896614034938880⟩, ⟨.privateRow 9 21, 52803413247538021261436971824096⟩, ⟨.privateRow 9 22, 67764649562189337016686849982560⟩, ⟨.privateRow 9 23, 37545047288763117341567388259200⟩, ⟨.privateRow 10 12, 11553006865325400117412308000⟩, ⟨.privateRow 10 13, 207761573461435112111464672200⟩, ⟨.privateRow 10 14, 761868289100640476833717111200⟩, ⟨.privateRow 10 15, 1889378742755315935201608850320⟩, ⟨.privateRow 10 16, 3878216037946788759414007214400⟩, ⟨.privateRow 10 17, 8554019578189906127933834027820⟩, ⟨.privateRow 10 18, 15777578381473417284917727505920⟩, ⟨.privateRow 10 19, 25205734218400807288163911604640⟩, ⟨.privateRow 10 20, 33571466741701928486784198974112⟩, ⟨.privateRow 11 10, 1287335050707687441654514320⟩, ⟨.privateRow 11 11, 73015003388856528742045786560⟩, ⟨.privateRow 11 12, 312393305638398819174828808320⟩, ⟨.privateRow 11 13, 842697326223862548927903586080⟩, ⟨.privateRow 11 14, 1814884954487697755244534288336⟩, ⟨.privateRow 11 15, 4109840988922268225767993531680⟩, ⟨.privateRow 11 16, 7899195149063262449278904410380⟩, ⟨.privateRow 11 17, 13353097369307272603135058869920⟩, ⟨.privateRow 11 18, 7145996866478372988624208990320⟩, ⟨.privateRow 12 9, 24125612431781105388043860960⟩, ⟨.privateRow 12 10, 133296025877265505354677118080⟩, ⟨.privateRow 12 11, 405065536264034936116649462640⟩, ⟨.privateRow 12 12, 937179916915196457524486424960⟩, ⟨.privateRow 12 13, 2049313435129162852027012659024⟩, ⟨.privateRow 12 14, 4802045813595386976802817194560⟩, ⟨.privateRow 12 15, 5084735054915604711675765913200⟩, ⟨.privateRow 13 7, 8076835466291935282084249104⟩, ⟨.privateRow 13 8, 58216151737558754305931925360⟩, ⟨.privateRow 13 9, 209263464353927414126728272240⟩, ⟨.privateRow 13 10, 536008171853919341447409258720⟩, ⟨.privateRow 13 11, 1357709366813041021798294436160⟩, ⟨.privateRow 13 12, 2684079277002742674878088418152⟩, ⟨.privateRow 14 5, 2556790447933323668841604830⟩, ⟨.privateRow 14 6, 25908809872391013177594928944⟩, ⟨.privateRow 14 7, 115420825935275754193421018040⟩, ⟨.privateRow 14 8, 338283043880408977723658485200⟩, ⟨.privateRow 14 9, 942603411804751992579604980660⟩, ⟨.privateRow 14 10, 260327754698665682645690673600⟩, ⟨.privateRow 15 3, 2807456178122865205002546480⟩, ⟨.privateRow 15 4, 11931688757022177121260822540⟩, ⟨.privateRow 15 5, 66817457039324191879060606224⟩, ⟨.privateRow 15 6, 231815667279288012641638837920⟩, ⟨.privateRow 15 7, 234962486292129026387905428480⟩, ⟨.privateRow 16 2, 8422368534368595615007639440⟩, ⟨.privateRow 16 3, 44743832838833164204728084525⟩, ⟨.privateRow 16 4, 104998861061795158667095238352⟩, ⟨.privateRow 17 1, 33689474137474382460030557760⟩, ⟨.hall 7 26, 27883030881965603246039735517920⟩, ⟨.hall 6 27, 230929313257337793769773748245600⟩, ⟨.hall 5 28, 658777336903228590326826848901600⟩, ⟨.hall 4 29, 1484722076817806014519514704929408⟩, ⟨.hall 3 30, 2961078731180108067541470338200320⟩, ⟨.hall 2 31, 5452913010535462188364529769827940⟩, ⟨.assumptionRow 20, 2779895947270508804130180480⟩]
  caps := #[0, 174057525871642882604177902984320, 31580536649761079531401685405760, 5745868895428419902940999664020, 852183671096511461354124360960, 347051707764104194716977930160, 354381384785259129276095933340, 0, 84190018661145286383259288250, 160253042781076750825251202656, 17634713126626443291979624320, 10900015574747322720922505280, 147257012483510531384931637104, 0, 68018941140530884924214927682, 0, 153243565913016690438628594755, 1843905843128167905791239550400, 2960004996959446900254941230080, 625672992630945111809457473280, 93216659237235258483365819520] }

theorem case_54_34_20_checked :
    (Witness.linear .conditional case_54_34_20).check 54 34 20 = true := by
  change case_54_34_20.check 54 34 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_21 : Certificate := {
  objectiveScale := 4078974506008303664963200000
  eta := 2003984780661948578675605077887513280
  rows := #[⟨.count 2, 117711359531076867059171369119017600⟩, ⟨.count 3, 11887971049416447864288522886213440⟩, ⟨.count 4, 1990778405731636208328125719153920⟩, ⟨.count 5, 340769030900553378583209091742400⟩, ⟨.count 6, 52117616490672869665667272854720⟩, ⟨.count 7, 7445373784381838523666753264960⟩, ⟨.count 8, 881109323595483848954645356800⟩, ⟨.count 9, 66083199269661288671598401760⟩, ⟨.path 2, 52548622386312576811688482399718400⟩, ⟨.path 8, 14347034955019061146591084800⟩, ⟨.path 9, 63553816115286535070595763200⟩, ⟨.privateRow 2 32, 11391421890104212941210132495388800⟩, ⟨.privateRow 5 24, 55243718945012680071437608360200⟩, ⟨.privateRow 5 28, 3483361079102568433135127053972680⟩, ⟨.privateRow 6 21, 3388599606994298302438073601360⟩, ⟨.privateRow 6 22, 23311110777290756330051858436720⟩, ⟨.privateRow 6 23, 46819946682555023023827467646960⟩, ⟨.privateRow 6 26, 843968118080035328377182180996000⟩, ⟨.privateRow 6 27, 321320378226607229875553951002200⟩, ⟨.privateRow 7 19, 2188612623430925060528413734480⟩, ⟨.privateRow 7 20, 8243092404137035508345333971920⟩, ⟨.privateRow 7 21, 19539723114663011855478641712240⟩, ⟨.privateRow 7 22, 38634808195237809518642543384520⟩, ⟨.privateRow 7 23, 51115354635083006787481363761360⟩, ⟨.privateRow 7 24, 91451280741679120987126521559440⟩, ⟨.privateRow 7 25, 317471556338984933312724388531440⟩, ⟨.privateRow 7 26, 302120586489593258004999393132120⟩, ⟨.privateRow 8 16, 59074375104697212600368268240⟩, ⟨.privateRow 8 17, 895427350103910461500158343848⟩, ⟨.privateRow 8 18, 2962730100589814442109995012240⟩, ⟨.privateRow 8 19, 7171403854076367764382418224330⟩, ⟨.privateRow 8 20, 14807356864923390183057441880080⟩, ⟨.privateRow 8 21, 33032421412709858045705923324200⟩, ⟨.privateRow 8 22, 48108569068313418152923636481280⟩, ⟨.privateRow 8 23, 79734886852118816556339438256920⟩, ⟨.privateRow 8 24, 159087959664012923444798530192560⟩, ⟨.privateRow 9 14, 40384177331459676410421245520⟩, ⟨.privateRow 9 15, 331083503411636355364775831040⟩, ⟨.privateRow 9 17, 4901578533483024967147693799680⟩, ⟨.privateRow 9 18, 4587275415968987788620122388840⟩, ⟨.privateRow 9 19, 13144263016636914418155548769120⟩, ⟨.privateRow 9 20, 25079797885785897222884030475360⟩, ⟨.privateRow 9 21, 37071206274740657138351778978432⟩, ⟨.privateRow 9 22, 54579215663467752668684313320280⟩, ⟨.privateRow 9 23, 79686548215616008761848176463040⟩, ⟨.privateRow 9 24, 17677255804634394719652572470800⟩, ⟨.privateRow 10 11, 429111683569229147218171440⟩, ⟨.privateRow 10 12, 18484810984520640187859692800⟩, ⟨.privateRow 10 13, 125157574374358501271966670000⟩, ⟨.privateRow 10 14, 227741273516105432859971351520⟩, ⟨.privateRow 10 15, 681858465191505114929674418160⟩, ⟨.privateRow 10 16, 3726691934570898733874079565920⟩, ⟨.privateRow 10 17, 4685899584575982287622432124800⟩, ⟨.privateRow 10 18, 10986975546106543085374061549760⟩, ⟨.privateRow 10 20, 66239395922480488081185816164160⟩, ⟨.privateRow 10 21, 16884257413398459255593391649680⟩, ⟨.privateRow 11 10, 7724010304246124649927085920⟩, ⟨.privateRow 11 11, 50371109932818744511917662880⟩, ⟨.privateRow 11 12, 138674592406789219409339070360⟩, ⟨.privateRow 11 13, 290547619929419880770994625920⟩, ⟨.privateRow 11 14, 720306872039308046520422579184⟩, ⟨.privateRow 11 15, 3762069808927384070233622144640⟩, ⟨.privateRow 11 16, 4565748313176598126401344121600⟩, ⟨.privateRow 11 17, 9559750086555286941726423340320⟩, ⟨.privateRow 11 18, 4180262984103573942483686778000⟩, ⟨.privateRow 11 19, 35103395452044076542353071014912⟩, ⟨.privateRow 11 20, 7236110320027911109540024992720⟩, ⟨.privateRow 12 8, 3426536258426881634823620832⟩, ⟨.privateRow 12 9, 22552202925360598514910565680⟩, ⟨.privateRow 12 10, 73425776966290320746220446400⟩, ⟨.privateRow 12 11, 171326812921344081741181041600⟩, ⟨.privateRow 12 12, 340428602298255123459749342400⟩, ⟨.privateRow 12 13, 925164789775258041402377624640⟩, ⟨.privateRow 12 14, 4021285051853833232868006447840⟩, ⟨.privateRow 12 15, 4929623101074316409099375220180⟩, ⟨.privateRow 12 16, 9097453766123370740456713308960⟩, ⟨.privateRow 12 17, 6621781319409948759296647257840⟩, ⟨.privateRow 12 18, 20289010691325341428595633749248⟩, ⟨.privateRow 13 6, 2065099977176915270987450055⟩, ⟨.privateRow 13 7, 11748124314606451319395271424⟩, ⟨.privateRow 13 8, 41695351920143432138032324920⟩, ⟨.privateRow 13 9, 107597003939063893093499961840⟩, ⟨.privateRow 13 10, 227619908595499994313283383840⟩, ⟨.privateRow 13 11, 83104629384574044844585868880⟩, ⟨.privateRow 13 12, 2086026323612308012400122882224⟩, ⟨.privateRow 13 13, 4368833729494274084400116560800⟩, ⟨.privateRow 13 15, 22336121353145515571000259794880⟩, ⟨.privateRow 13 18, 20728096837583757546658032018720⟩, ⟨.privateRow 14 4, 1203195504909799373572519920⟩, ⟨.privateRow 14 5, 7670371343799971006524814490⟩, ⟨.privateRow 14 6, 27272431444622119134310451520⟩, ⟨.privateRow 14 7, 74512178768342575491955340760⟩, ⟨.privateRow 14 8, 173075045706255756044662480800⟩, ⟨.privateRow 14 9, 402268363808176257231079159920⟩, ⟨.privateRow 14 10, 159915620743466062196638556640⟩, ⟨.privateRow 14 11, 3043603349219828495389046389632⟩, ⟨.privateRow 14 12, 6290840853226168813647610817280⟩, ⟨.privateRow 14 13, 1948274321325192635657302880460⟩, ⟨.privateRow 14 14, 22336121353145515571000259794880⟩, ⟨.privateRow 14 17, 39783659369842516287175371154800⟩, ⟨.privateRow 15 3, 5614912356245730410005092960⟩, ⟨.privateRow 15 4, 20880455324788809962206439445⟩, ⟨.privateRow 15 5, 60453889702245697414388167536⟩, ⟨.privateRow 15 6, 149998372945421655238707483360⟩, ⟨.privateRow 15 8, 1571005686341253320966008301100⟩, ⟨.privateRow 15 10, 5154489543033580516384675337280⟩, ⟨.privateRow 15 11, 10987759602022200442334410801280⟩, ⟨.privateRow 15 12, 6795096747124129870558038436530⟩, ⟨.privateRow 15 14, 8948766567766632840945616905000⟩, ⟨.privateRow 15 17, 173407209935388974162323954248000⟩, ⟨.privateRow 16 1, 7954459171348118080840548360⟩, ⟨.privateRow 16 2, 16844737068737191230015278880⟩, ⟨.privateRow 16 3, 62641365974366429886619318335⟩, ⟨.privateRow 16 4, 162270967095501608849147186544⟩, ⟨.privateRow 16 5, 419313633461065081690023192120⟩, ⟨.privateRow 16 7, 3770413647219007970318419922640⟩, ⟨.privateRow 16 10, 46215407785532566049683585971600⟩, ⟨.privateRow 16 12, 28165603574433493535959118807280⟩, ⟨.privateRow 16 14, 12657135433449125490233480550432⟩, ⟨.privateRow 16 16, 101085267149491884571321688558880⟩, ⟨.privateRow 16 17, 378210670220088970389725552872920⟩, ⟨.privateRow 17 0, 31817836685392472323362193440⟩, ⟨.privateRow 17 1, 67378948274948764920061115520⟩, ⟨.privateRow 17 2, 214770397626399188182694805720⟩, ⟨.privateRow 17 3, 610902464359535468608554114048⟩, ⟨.privateRow 17 4, 1472711298009594433252764382080⟩, ⟨.privateRow 17 5, 132166398539322577343196803520⟩, ⟨.privateRow 17 6, 11311240941657023910955259767920⟩, ⟨.privateRow 17 8, 5841754815438057918569298715584⟩, ⟨.privateRow 17 10, 17682762737906866493708539004280⟩, ⟨.privateRow 17 12, 50972174369998740662026233890880⟩, ⟨.privateRow 17 17, 4384179716880228761436076634097600⟩, ⟨.privateRow 18 0, 763628080449419335760692642560⟩, ⟨.privateRow 18 1, 811354835477508044245735932720⟩, ⟨.privateRow 18 2, 3029058052449363365184080815488⟩, ⟨.privateRow 18 3, 7186285685657928391890803975520⟩, ⟨.privateRow 18 4, 1497885850112322543222897106560⟩, ⟨.privateRow 18 7, 138579405899558373957171697308576⟩, ⟨.privateRow 18 10, 47290396124974754578894322935680⟩, ⟨.privateRow 18 11, 101689806046514341545465570234240⟩, ⟨.privateRow 19 14, 13100135173619844882391652369697120⟩, ⟨.hall 15 6, 654369485126382115451721360⟩, ⟨.hall 17 12, 373422522857133631223635413120⟩, ⟨.hall 14 19, 1546346862910074154915402601184⟩, ⟨.hall 6 22, 6807846494809309086578917476⟩, ⟨.hall 5 23, 13711319400858270862663982990⟩, ⟨.hall 4 27, 3703220018711482094037506758464⟩, ⟨.hall 3 30, 8410242497193565319540251666984320⟩, ⟨.hall 2 31, 10798118666661285183855438094587300⟩]
  caps := #[0, 0, 0, 0, 688319732196995106011370228480, 121751742836561519761957878000, 161769633414369337465141455240, 23386856022340916383892799692, 0, 47169364989431847235344803840, 0, 1319030416018973761324874576, 73142639265255712625330517660, 59681106849417975122890543316, 0, 257377843348799373918595403526, 467666058564591804491450501625, 4578341196534314566787350752832, 0, 848426697249727162312345600000, 314081036962639382202166400000] }

theorem case_54_34_21_checked :
    (Witness.linear .conditional case_54_34_21).check 54 34 21 = true := by
  change case_54_34_21.check 54 34 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_34_22 : Certificate := {
  objectiveScale := 1691395446266386958697600000
  eta := 747315002321096075349563407924396800
  rows := #[⟨.count 2, 41493487693941713842428043470643200⟩, ⟨.count 3, 3596719729422775046609276089531200⟩, ⟨.count 4, 535134265894089563444012465395200⟩, ⟨.count 5, 77939521192153881553638693348000⟩, ⟨.count 6, 9534349194379989393940267341600⟩, ⟨.count 7, 983702694658252873977964090800⟩, ⟨.count 8, 46565808031159899359903625600⟩, ⟨.path 2, 19780343057310600366121480440480000⟩, ⟨.path 7, 16845780985951033139135112000⟩, ⟨.path 8, 61865816736405273146100000000⟩, ⟨.privateRow 2 32, 4445730824350897911688718943283200⟩, ⟨.privateRow 4 29, 1939559036113872128138705813491200⟩, ⟨.privateRow 6 21, 731471234489470085778486118800⟩, ⟨.privateRow 6 22, 3736628917071825019469409385200⟩, ⟨.privateRow 6 23, 10715633199503788785341155843800⟩, ⟨.privateRow 6 27, 619593970331606480072607664319400⟩, ⟨.privateRow 7 19, 422787971330531149743886886400⟩, ⟨.privateRow 7 20, 1570140839550672856541750375700⟩, ⟨.privateRow 7 21, 4371840390231575959547278400400⟩, ⟨.privateRow 7 22, 10548679994915880177913882329000⟩, ⟨.privateRow 8 16, 8995667460564980558163200400⟩, ⟨.privateRow 8 17, 154831311703606665371679555120⟩, ⟨.privateRow 8 19, 2656433830027574883797002141650⟩, ⟨.privateRow 8 20, 3138202848385668931862076482400⟩, ⟨.privateRow 8 21, 9911726263632514411669486307400⟩, ⟨.privateRow 8 23, 45806203287651603501595197707400⟩, ⟨.privateRow 9 14, 4527231336362767993323963600⟩, ⟨.privateRow 9 15, 51151834579683222781712316000⟩, ⟨.privateRow 9 16, 97788196865435788655797613760⟩, ⟨.privateRow 9 17, 382443256700359543816986258400⟩, ⟨.privateRow 9 18, 1794723851200954454496285570000⟩, ⟨.privateRow 9 19, 2986309617426885450616676560800⟩, ⟨.privateRow 9 20, 7432420359640132825611284241600⟩, ⟨.privateRow 9 21, 5365157181990139737916896062880⟩, ⟨.privateRow 9 22, 22005254657724999941264457072600⟩, ⟨.privateRow 10 12, 1953810127181534238877075200⟩, ⟨.privateRow 10 13, 17462178011684962259963859600⟩, ⟨.privateRow 10 14, 51087694348235344132456250400⟩, ⟨.privateRow 10 15, 130490093869136717979002659920⟩, ⟨.privateRow 10 16, 385931772621885832573746715200⟩, ⟨.privateRow 10 17, 1711690312827210050618730146700⟩, ⟨.privateRow 10 18, 2914596257223053700844876929600⟩, ⟨.privateRow 10 19, 6590120150228015757139088104800⟩, ⟨.privateRow 10 20, 8379305492443445890272112410240⟩, ⟨.privateRow 10 21, 17965406232567156172364636281200⟩, ⟨.privateRow 10 23, 66227691315407721865766568968400⟩, ⟨.privateRow 11 10, 680344597857855672466124400⟩, ⟨.privateRow 11 11, 6349882913339986276350494400⟩, ⟨.privateRow 11 12, 22224590196689951967226730400⟩, ⟨.privateRow 11 13, 58014839344606238252111335200⟩, ⟨.privateRow 11 14, 139697424093479698079710876800⟩, ⟨.privateRow 11 15, 455074942122699016471785432000⟩, ⟨.privateRow 11 16, 1645016542237140194717049955500⟩, ⟨.privateRow 11 17, 2814812382870568202216512017600⟩, ⟨.privateRow 11 18, 5664624715608712757361003546000⟩, ⟨.privateRow 11 19, 7877029753998252975812788303200⟩, ⟨.privateRow 11 20, 12206856165531956117999281672200⟩, ⟨.privateRow 11 22, 17532026723731702109003715038400⟩, ⟨.privateRow 12 8, 258698933506443885332797920⟩, ⟨.privateRow 12 9, 2494596858812137465709122800⟩, ⟨.privateRow 12 10, 10148958160637413963055918400⟩, ⟨.privateRow 12 11, 28133509018825772529941773800⟩, ⟨.privateRow 12 12, 66320999317106523330771830400⟩, ⟨.privateRow 12 13, 183934941723081602471619321120⟩, ⟨.privateRow 12 14, 535506792358338842638891694400⟩, ⟨.privateRow 12 15, 1700137053637660908921481330500⟩, ⟨.privateRow 12 16, 2925884937957880343113944475200⟩, ⟨.privateRow 12 17, 5338899240239235683555617074000⟩, ⟨.privateRow 12 18, 7743117778781371931895974543520⟩, ⟨.privateRow 12 19, 10578199391078490471258106948800⟩, ⟨.privateRow 12 21, 17215767277520074459184369581200⟩, ⟨.privateRow 13 6, 363795375243436713749247075⟩, ⟨.privateRow 13 7, 1164145200778997483997590640⟩, ⟨.privateRow 13 8, 4989193717624274931418245600⟩, ⟨.privateRow 13 9, 15223437240956120944583877600⟩, ⟨.privateRow 13 10, 36864598024668253659923703600⟩, ⟨.privateRow 13 11, 98423185156769787283432663200⟩, ⟨.privateRow 13 12, 253201581169431952769475964200⟩, ⟨.privateRow 13 14, 3320724185222090323103127300600⟩, ⟨.privateRow 13 15, 2715784446960146987668665021600⟩, ⟨.privateRow 13 17, 19760200638022703293375103523360⟩, ⟨.privateRow 13 19, 12956936084670241996893183823200⟩, ⟨.privateRow 14 5, 675619982594953896962887425⟩, ⟨.privateRow 14 6, 2882645259071803293708319680⟩, ⟨.privateRow 14 7, 9265645475587939158348170400⟩, ⟨.privateRow 14 8, 24114436301850662168521520400⟩, ⟨.privateRow 14 9, 64859518329115574108437192800⟩, ⟨.privateRow 14 10, 161166075848105365966419691200⟩, ⟨.privateRow 14 11, 393481077863301149591185636320⟩, ⟨.privateRow 14 12, 111702503789032377631197387600⟩, ⟨.privateRow 14 13, 3867248780373516106215567620700⟩, ⟨.privateRow 14 14, 4720846369812055001178392818800⟩, ⟨.privateRow 14 15, 2064694666810179109118583970800⟩, ⟨.privateRow 14 16, 14221530385630741549509995141280⟩, ⟨.privateRow 15 4, 1576446626054892426246737325⟩, ⟨.privateRow 15 5, 6726172271167541018652745920⟩, ⟨.privateRow 15 6, 19818186156118647644244697800⟩, ⟨.privateRow 15 7, 52386534035054886779891578800⟩, ⟨.privateRow 15 8, 130319587753871107236396952200⟩, ⟨.privateRow 15 9, 311849805299585992682990947200⟩, ⟨.privateRow 15 11, 1838487087452461211765083884800⟩, ⟨.privateRow 15 12, 4543319176290199972443096970650⟩, ⟨.privateRow 15 14, 24319316617940140495566334467000⟩, ⟨.privateRow 15 17, 30158474920847462042384249518800⟩, ⟨.privateRow 16 3, 4729339878164677278740211975⟩, ⟨.privateRow 16 4, 20178516813502623055958237760⟩, ⟨.privateRow 16 5, 54049598607596311757030994000⟩, ⟨.privateRow 16 6, 133876698089584710659722923600⟩, ⟨.privateRow 16 7, 327900898219417624659321363600⟩, ⟨.privateRow 16 8, 742936300860778394333007844800⟩, ⟨.privateRow 16 9, 196740538931650574795592818160⟩, ⟨.privateRow 16 11, 15767619153801034047319866724650⟩, ⟨.privateRow 16 12, 2129554185139294683227021163600⟩, ⟨.privateRow 16 13, 29082287357460655479399810171600⟩, ⟨.privateRow 16 15, 60970649709299019477518812781700⟩, ⟨.privateRow 17 1, 17804573658972902696433739200⟩, ⟨.privateRow 17 2, 18917359512658709114960847900⟩, ⟨.privateRow 17 3, 80714067254010492223832951040⟩, ⟨.privateRow 17 4, 194578554987346722325311578400⟩, ⟨.privateRow 17 5, 442375176296019043919084443200⟩, ⟨.privateRow 17 6, 1034148986692009431617859685200⟩, ⟨.privateRow 17 7, 2228808902582335182999023534400⟩, ⟨.privateRow 17 8, 1119907683149395579605682195680⟩, ⟨.privateRow 17 10, 227008314151904509379530174800⟩, ⟨.privateRow 17 11, 92273474742888423431603312956800⟩, ⟨.privateRow 17 17, 1280326891816741432900550185872000⟩, ⟨.privateRow 18 0, 100892584067513115279791188800⟩, ⟨.privateRow 18 1, 107198370571732684984778138100⟩, ⟨.privateRow 18 2, 343034785829544591951290041920⟩, ⟨.privateRow 18 3, 612562117552758199913017932000⟩, ⟨.privateRow 18 5, 9719318931837096771953217854400⟩, ⟨.privateRow 18 7, 19724500185198814037199177410400⟩, ⟨.privateRow 18 11, 6860695716590891839025800838400⟩, ⟨.privateRow 18 13, 927480302186631190488300450841200⟩, ⟨.privateRow 19 0, 2894356005436782494589009728700⟩, ⟨.privateRow 19 3, 3562284314383732301032627358400⟩, ⟨.privateRow 19 6, 254703328478436859523832856125600⟩, ⟨.privateRow 19 11, 33960443797124914603177714150080⟩, ⟨.privateRow 19 14, 12804630968052325756061779039768800⟩, ⟨.privateRow 20 1, 167596995362434643496201706195200⟩, ⟨.hall 18 2, 1929570670291188329726006485800⟩, ⟨.hall 16 6, 3603306573839754117135399600⟩, ⟨.hall 15 13, 4769082230082027507973323000⟩, ⟨.hall 12 14, 127911441440316717016153320⟩, ⟨.hall 8 15, 32225988367744962812904960⟩, ⟨.hall 11 15, 79802688439822397859359550⟩, ⟨.hall 10 16, 125966614190947569342576000⟩, ⟨.hall 17 16, 13015143344709191871093063355200⟩, ⟨.hall 9 23, 169324919453305184047449558588⟩, ⟨.hall 5 24, 34027193219485508287049444640⟩, ⟨.hall 6 27, 806965912171273694163648443519400⟩, ⟨.hall 3 28, 2544333650624475349422916573440⟩, ⟨.hall 4 29, 2226497545201879427994431954438400⟩, ⟨.hall 2 30, 131428660332898198652143957895700⟩]
  caps := #[0, 67518433884636728702770501440000, 0, 1468170277812694440919002868800, 802499904276385977482037235200, 465790889587648204519304274000, 15069371998095323705784951600, 6924337455971399166884831130, 15300008705245373786196374400, 19688310444593420093188293800, 0, 9528260453837544342164459400, 47433602046822610403112372660, 0, 0, 363505985330911677653962492930, 1579522977656682782563827862875, 60122862218758303898547754140, 2897227445201022783069116676780, 0, 0] }

theorem case_54_34_22_checked :
    (Witness.linear .conditional case_54_34_22).check 54 34 22 = true := by
  change case_54_34_22.check 54 34 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_35_1_checked :
    (Witness.rising).check 54 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_35_2_checked :
    (Witness.rising).check 54 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_35_3_checked :
    (Witness.rising).check 54 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_35_4_checked :
    (Witness.rising).check 54 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_35_5_checked :
    (Witness.rising).check 54 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_35_6_checked :
    (Witness.rising).check 54 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_35_7_checked :
    (Witness.rising).check 54 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_35_8_checked :
    (Witness.rising).check 54 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_35_9_checked :
    (Witness.rising).check 54 35 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_35_10_checked :
    (Witness.rising).check 54 35 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_35_11_checked :
    (Witness.linear .positive case_54_35_11).check 54 35 11 = true := by
  change case_54_35_11.check 54 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_35_12_checked :
    (Witness.linear .positive case_54_35_12).check 54 35 12 = true := by
  change case_54_35_12.check 54 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_35_13_checked :
    (Witness.linear .positive case_54_35_13).check 54 35 13 = true := by
  change case_54_35_13.check 54 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_54_35_14_checked :
    (Witness.linear .positive case_54_35_14).check 54 35 14 = true := by
  change case_54_35_14.check 54 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_54_35_15_checked :
    (Witness.linear .positive case_54_35_15).check 54 35 15 = true := by
  change case_54_35_15.check 54 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_16 : Certificate := {
  objectiveScale := 787
  eta := 3942458865
  rows := #[⟨.assumptionRow 16, 2753⟩]
  caps := #[0, 0, 1109744020, 315405624, 90661578, 26411710, 7819422, 2361216, 730873, 233541, 77850, 27524, 10626, 941248, 361123, 81483, 11413, 787, 0, 0] }

theorem case_54_35_16_checked :
    (Witness.linear .conditional case_54_35_16).check 54 35 16 = true := by
  change case_54_35_16.check 54 35 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_17 : Certificate := {
  objectiveScale := 4073648209488000000
  eta := 1413839593490604770874384000
  rows := #[⟨.count 2, 213557423769636624149472000⟩, ⟨.count 3, 32122403994176324987558400⟩, ⟨.count 4, 4863742373811095890315200⟩, ⟨.count 5, 731698903429999212708000⟩, ⟨.count 6, 107112263230844186515200⟩, ⟨.count 7, 16695636171609316521600⟩, ⟨.count 8, 3035570213019875731200⟩, ⟨.count 9, 827882785369057017600⟩, ⟨.count 10, 206970696342264254400⟩, ⟨.path 8, 532796679949072226688⟩, ⟨.privateRow 2 33, 18504583054384744134417600⟩, ⟨.privateRow 3 29, 69059222346202172884800⟩, ⟨.privateRow 4 27, 535455613262874704760360⟩, ⟨.privateRow 4 28, 1027564232499517152790350⟩, ⟨.privateRow 4 29, 1821436989381082309836600⟩, ⟨.privateRow 4 31, 10637586642113213273290800⟩, ⟨.privateRow 5 24, 76810767711592212698400⟩, ⟨.privateRow 5 25, 242200558371323334903120⟩, ⟨.privateRow 5 26, 418630428793882695630240⟩, ⟨.privateRow 5 27, 671025443797264446530640⟩, ⟨.privateRow 5 30, 8602805983698327822220800⟩, ⟨.privateRow 6 21, 9108718291316915471200⟩, ⟨.privateRow 6 22, 43573080766056132891600⟩, ⟨.privateRow 6 23, 93001766147958854300400⟩, ⟨.privateRow 6 24, 158319441705238994980800⟩, ⟨.privateRow 6 25, 243609930255939705778320⟩, ⟨.privateRow 6 26, 427010319124497534125700⟩, ⟨.privateRow 6 27, 335117314786559296992000⟩, ⟨.privateRow 6 29, 2016576271571923993932000⟩, ⟨.privateRow 7 18, 517426740855660636000⟩, ⟨.privateRow 7 19, 6775826368347936900000⟩, ⟨.privateRow 7 20, 19303576453826789124000⟩, ⟨.privateRow 7 21, 37178959283125129770300⟩, ⟨.privateRow 7 22, 61431577805833352488800⟩, ⟨.privateRow 7 23, 92765580200262154785600⟩, ⟨.privateRow 7 24, 158391717186501372974400⟩, ⟨.privateRow 7 25, 71823759504488131140000⟩, ⟨.privateRow 7 26, 511439374282902277212000⟩, ⟨.privateRow 8 16, 542818979064318056100⟩, ⟨.privateRow 8 17, 3578868290918319399000⟩, ⟨.privateRow 8 18, 8648213054801416796700⟩, ⟨.privateRow 8 19, 15985931098657910390000⟩, ⟨.privateRow 8 20, 25770726287616653343000⟩, ⟨.privateRow 8 21, 38184040194430073743800⟩, ⟨.privateRow 8 22, 63999938657835713332800⟩, ⟨.privateRow 8 23, 88366713721930674150120⟩, ⟨.privateRow 8 24, 61999940574778347291150⟩, ⟨.privateRow 8 25, 161359529135837769336600⟩, ⟨.privateRow 8 27, 259730976351513117250800⟩, ⟨.privateRow 9 14, 359103003055381569600⟩, ⟨.privateRow 9 15, 1818659174340822013200⟩, ⟨.privateRow 9 16, 4197951093487541644800⟩, ⟨.privateRow 9 17, 7595824555761098136480⟩, ⟨.privateRow 9 18, 12080956201311424627200⟩, ⟨.privateRow 9 19, 17650001049187535028000⟩, ⟨.privateRow 9 20, 29018605726844764430400⟩, ⟨.privateRow 9 21, 40336289042703500246400⟩, ⟨.privateRow 9 22, 50882595858543765476160⟩, ⟨.privateRow 9 23, 40054578928237640566800⟩, ⟨.privateRow 9 24, 52409579662668915086400⟩, ⟨.privateRow 10 12, 212884144809186090240⟩, ⟨.privateRow 10 13, 975946437367753753440⟩, ⟨.privateRow 10 14, 2271503392356350192040⟩, ⟨.privateRow 10 15, 4107427546501480612320⟩, ⟨.privateRow 10 16, 6507158693000788158336⟩, ⟨.privateRow 10 17, 9451661799630067617600⟩, ⟨.privateRow 10 18, 15258914587833432155640⟩, ⟨.privateRow 10 19, 21276587583984765352320⟩, ⟨.privateRow 10 20, 27185600964556409815440⟩, ⟨.privateRow 10 21, 31339502840145653401248⟩, ⟨.privateRow 10 22, 24479459109881304689160⟩, ⟨.privateRow 11 10, 127248650343762467520⟩, ⟨.privateRow 11 11, 578203850099023948800⟩, ⟨.privateRow 11 12, 1397494445387938128000⟩, ⟨.privateRow 11 13, 2587133704278303180000⟩, ⟨.privateRow 11 14, 4147776379222750310400⟩, ⟨.privateRow 11 15, 6071140426039751462400⟩, ⟨.privateRow 11 16, 9763395441034465630400⟩, ⟨.privateRow 11 17, 13829666945869907332200⟩, ⟨.privateRow 11 18, 18361257489792300283200⟩, ⟨.privateRow 11 19, 22709284737553994580000⟩, ⟨.privateRow 11 20, 26027714902241631458880⟩, ⟨.privateRow 11 22, 51758005248258083174400⟩, ⟨.privateRow 12 8, 83003873012262227025⟩, ⟨.privateRow 12 9, 387878416108095232320⟩, ⟨.privateRow 12 10, 991529258568248099700⟩, ⟨.privateRow 12 11, 1916690166554216407200⟩, ⟨.privateRow 12 12, 3154147174465964626950⟩, ⟨.privateRow 12 13, 4676962818734221415400⟩, ⟨.privateRow 12 14, 7481415754171902062520⟩, ⟨.privateRow 12 15, 10599902005417783658600⟩, ⟨.privateRow 12 16, 14106705846703042297725⟩, ⟨.privateRow 12 17, 17544873076442257946400⟩, ⟨.privateRow 12 18, 20126462922782821905300⟩, ⟨.privateRow 12 19, 20806304168407064907600⟩, ⟨.privateRow 13 6, 60583859293463906400⟩, ⟨.privateRow 13 7, 298136360207309223600⟩, ⟨.privateRow 13 8, 827554260454228026720⟩, ⟨.privateRow 13 9, 1699764443259853885200⟩, ⟨.privateRow 13 10, 2939666209037104932000⟩, ⟨.privateRow 13 11, 4535286449214219098400⟩, ⟨.privateRow 13 12, 7396738457374729663200⟩, ⟨.privateRow 13 13, 10792536239504593894320⟩, ⟨.privateRow 13 14, 14942955750996650176800⟩, ⟨.privateRow 13 15, 19724430558260844315900⟩, ⟨.privateRow 13 16, 24842115416754493228800⟩, ⟨.privateRow 13 18, 90438309703613583391680⟩, ⟨.privateRow 14 4, 52198958689495217600⟩, ⟨.privateRow 14 5, 269438742647247373200⟩, ⟨.privateRow 14 6, 814793120793839412225⟩, ⟨.privateRow 14 7, 1808693918591009289840⟩, ⟨.privateRow 14 8, 3330479989242257365800⟩, ⟨.privateRow 14 9, 5393557789204957772400⟩, ⟨.privateRow 14 10, 9063044202463607155800⟩, ⟨.privateRow 14 11, 13549188799834656368400⟩, ⟨.privateRow 14 12, 19190947162192916750640⟩, ⟨.privateRow 14 13, 25968981948023870756000⟩, ⟨.privateRow 14 14, 33707477573741536765200⟩, ⟨.privateRow 14 15, 42046261224388397776800⟩, ⟨.privateRow 14 16, 20631638422022984756400⟩, ⟨.privateRow 14 17, 75565822546847751758640⟩, ⟨.privateRow 14 21, 535913659125375025294800⟩, ⟨.privateRow 15 2, 51924227327971558560⟩, ⟨.privateRow 15 3, 292314168661173218560⟩, ⟨.privateRow 15 4, 909183039291737290080⟩, ⟨.privateRow 15 5, 2034780658414885451070⟩, ⟨.privateRow 15 6, 3836623463677898493600⟩, ⟨.privateRow 15 7, 6342173480773668938400⟩, ⟨.privateRow 15 8, 2327270496648571393920⟩, ⟨.privateRow 15 9, 34803655706220936334800⟩, ⟨.privateRow 15 10, 15904548176701106482560⟩, ⟨.privateRow 15 11, 33970560325536592661904⟩, ⟨.privateRow 15 13, 146093140606191977638440⟩, ⟨.privateRow 15 15, 94161701579980423028640⟩, ⟨.privateRow 16 1, 519242273279715585600⟩, ⟨.privateRow 16 2, 1370222665599249462000⟩, ⟨.privateRow 16 3, 3481977597287504515200⟩, ⟨.privateRow 16 4, 7399202394235947094800⟩, ⟨.privateRow 16 6, 52675274187536861460600⟩, ⟨.privateRow 16 8, 115715304109856617065900⟩, ⟨.privateRow 16 9, 78364279902589803322200⟩, ⟨.privateRow 16 14, 1805405384193571091131200⟩, ⟨.privateRow 17 12, 6445527418978869469248000⟩, ⟨.privateRow 17 15, 5011726421695814832211200⟩, ⟨.hall 14 5, 81853785065725472800⟩, ⟨.hall 11 10, 134268915419238600⟩, ⟨.hall 9 14, 15140747482921368⟩, ⟨.hall 12 15, 323151947114396400⟩, ⟨.hall 14 16, 11829609213842259840⟩, ⟨.hall 15 16, 126247140954283789440⟩, ⟨.hall 8 19, 66443584130686840⟩, ⟨.hall 6 27, 4475450005521320568600⟩, ⟨.hall 7 27, 22685466681228892741200⟩, ⟨.assumptionRow 17, 6648359369842926450⟩]
  caps := #[0, 372102768577959543409428, 38267164257975611861760, 0, 6433976618905914485550, 0, 304046212241021028064, 119120385080075171364, 105189236472135892868, 27463041281375483850, 344094098041206692856, 209689249892516995560, 917095284862407583240, 27221659680914405850, 224084919323486017940, 1266597035291170902176, 0, 34088122725037073550, 4073648209488000000, 0] }

theorem case_54_35_17_checked :
    (Witness.linear .conditional case_54_35_17).check 54 35 17 = true := by
  change case_54_35_17.check 54 35 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_18 : Certificate := {
  objectiveScale := 7688405567722655529600000
  eta := 1776945502552937157282218522745600
  rows := #[⟨.count 2, 262102502258835015328075353628800⟩, ⟨.count 3, 38455055265217366108595742480000⟩, ⟨.count 4, 5714600073133464405440158010400⟩, ⟨.count 5, 834683370097741279876496736000⟩, ⟨.count 6, 120092199167124000472026571200⟩, ⟨.count 7, 19261923925332491074073001600⟩, ⟨.count 8, 4127555126856962373015643200⟩, ⟨.count 9, 1500929137038895408369324800⟩, ⟨.count 10, 375232284259723852092331200⟩, ⟨.path 7, 758497515185883664426435200⟩, ⟨.path 8, 452530268892475737645217536⟩, ⟨.privateRow 2 33, 21385780346718556935121384228800⟩, ⟨.privateRow 3 29, 163955661983484894261454716000⟩, ⟨.privateRow 3 30, 3899163743170877121708777609600⟩, ⟨.privateRow 3 31, 6713239105214690579578109462400⟩, ⟨.privateRow 4 27, 670727708114256385615042020000⟩, ⟨.privateRow 4 28, 1519757198635552593739416043650⟩, ⟨.privateRow 4 29, 2458589676743257573493359582200⟩, ⟨.privateRow 4 30, 4072435067767060021325996798100⟩, ⟨.privateRow 5 24, 85001428914035285440484055360⟩, ⟨.privateRow 5 25, 300585380303055639479333646000⟩, ⟨.privateRow 5 26, 543259633452187038731045589888⟩, ⟨.privateRow 5 27, 870455514530501620442632310400⟩, ⟨.privateRow 5 28, 1493288295932006661188570589120⟩, ⟨.privateRow 5 29, 1757306595259351730311410092400⟩, ⟨.privateRow 6 21, 7192283007644936198482284800⟩, ⟨.privateRow 6 22, 49772254530700771472227324500⟩, ⟨.privateRow 6 23, 115103566780242456379470249600⟩, ⟨.privateRow 6 24, 203205653791652490160409026800⟩, ⟨.privateRow 6 25, 315774346391568958687970576400⟩, ⟨.privateRow 6 26, 538498531371731555308076593200⟩, ⟨.privateRow 6 27, 677541449910972640960972605600⟩, ⟨.privateRow 6 28, 650286482724107619577250263200⟩, ⟨.privateRow 7 19, 5758922153186142739493254560⟩, ⟨.privateRow 7 20, 21937191137184225945472029600⟩, ⟨.privateRow 7 21, 45894482005766700671388223200⟩, ⟨.privateRow 7 22, 79364180721504790117882418400⟩, ⟨.privateRow 7 23, 122188735104575155963082136000⟩, ⟨.privateRow 7 24, 205296730000099866600706634400⟩, ⟨.privateRow 7 25, 263156208117648357008158061400⟩, ⟨.privateRow 7 26, 270682444549357778478002061600⟩, ⟨.privateRow 7 27, 141467038216918984189429009200⟩, ⟨.privateRow 8 17, 3080031666631899952591218600⟩, ⟨.privateRow 8 18, 9562169377218629497486240080⟩, ⟨.privateRow 8 19, 19580408117219602368287171600⟩, ⟨.privateRow 8 20, 33428896990950919218954818625⟩, ⟨.privateRow 8 21, 51103063475371915094479392000⟩, ⟨.privateRow 8 22, 85446123841393089124719669300⟩, ⟨.privateRow 8 23, 111753555059652256249398539640⟩, ⟨.privateRow 8 24, 95148744747233934702954358350⟩, ⟨.privateRow 9 15, 1448813542002822651134278800⟩, ⟨.privateRow 9 16, 4445934034713697762669742400⟩, ⟨.privateRow 9 17, 9105636764702632144107237120⟩, ⟨.privateRow 9 18, 15579088542783349562796417600⟩, ⟨.privateRow 9 19, 22680706959698863948692019200⟩, ⟨.privateRow 9 20, 41799685252932412602920323200⟩, ⟨.privateRow 9 21, 48363272193475518714122688000⟩, ⟨.privateRow 10 13, 666758905107663152564065440⟩, ⟨.privateRow 10 14, 2242012898451850016251678920⟩, ⟨.privateRow 10 15, 4727926781672520536363373120⟩, ⟨.privateRow 10 16, 8198825411074966168217436720⟩, ⟨.privateRow 10 17, 12628650989141150533196346720⟩, ⟨.privateRow 10 18, 20225020121599115627776651680⟩, ⟨.privateRow 11 11, 315671604218497843823707200⟩, ⟨.privateRow 11 12, 1231531599621657770969702400⟩, ⟨.privateRow 11 13, 2779498401923880385869120000⟩, ⟨.privateRow 11 14, 4980355772901789309589123200⟩, ⟨.privateRow 11 15, 6537380241324966667564170240⟩, ⟨.privateRow 12 9, 160516032711104092283941680⟩, ⟨.privateRow 12 10, 741158212263006140392689900⟩, ⟨.privateRow 12 11, 1856517850861945682734600200⟩, ⟨.privateRow 12 12, 2159322820994614574772072600⟩, ⟨.privateRow 13 7, 92132926938771481540527750⟩, ⟨.privateRow 13 8, 491375610340114568216148000⟩, ⟨.privateRow 13 9, 842358189154482116941968000⟩, ⟨.privateRow 14 5, 62626303278642052811862000⟩, ⟨.privateRow 14 6, 319394146721074469340496200⟩, ⟨.privateRow 15 3, 33122355956259574598273680⟩, ⟨.privateRow 15 4, 35070729836039549574642720⟩, ⟨.hall 5 29, 345101826708268507739413471920⟩, ⟨.hall 4 30, 1246543839467398641824772717600⟩, ⟨.hall 3 31, 3175895697921003985887223964700⟩, ⟨.hall 2 32, 6996525582338772468505890172800⟩, ⟨.assumptionRow 18, 8229123935255969857013760⟩]
  caps := #[0, 0, 17293756141749733751716573248, 0, 4534661625585026668345230816, 2911625550459646874137993632, 224918143901967870634965696, 0, 581337564353163249255582101, 0, 142234950994411527375534600, 823622676809211810641915520, 79513716559698047052312810, 547862770591297800878174760, 8229123935255969857013760, 3736505874631284828357970400, 4884520804883771694354708480, 898039644743207008926766080, 114785365148306518616586240, 7688405567722655529600000] }

theorem case_54_35_18_checked :
    (Witness.linear .conditional case_54_35_18).check 54 35 18 = true := by
  change case_54_35_18.check 54 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_19 : Certificate := {
  objectiveScale := 92932344092924336000000
  eta := 23704082255937685614389368992000
  rows := #[⟨.count 2, 3233598244483956788597154796800⟩, ⟨.count 3, 429502907342451838955444985600⟩, ⟨.count 4, 56232311921020057114427335200⟩, ⟨.count 5, 6926554258748071389157716000⟩, ⟨.count 6, 872382343958940769713158400⟩, ⟨.count 7, 150057219420287888807498400⟩, ⟨.count 8, 43494846208779098205072000⟩, ⟨.count 9, 14234676941054977594387200⟩, ⟨.count 10, 3558669235263744398596800⟩, ⟨.path 6, 20452245588509568137904600⟩, ⟨.path 7, 26277975957421529030289600⟩, ⟨.privateRow 2 33, 276835997149637204255642265600⟩, ⟨.privateRow 3 29, 2063830452606568209830666400⟩, ⟨.privateRow 3 30, 46855547992510763193050563200⟩, ⟨.privateRow 3 31, 84814950107119241499890400000⟩, ⟨.privateRow 4 27, 7319530194244390541440541520⟩, ⟨.privateRow 4 28, 17853546997548600335726929200⟩, ⟨.privateRow 4 29, 30738351501321798440251945800⟩, ⟨.privateRow 4 30, 53952910136891227499117780700⟩, ⟨.privateRow 5 24, 775450972407947350856140800⟩, ⟨.privateRow 5 25, 3173963910675306726351454080⟩, ⟨.privateRow 5 26, 6235595131875406635071942208⟩, ⟨.privateRow 5 27, 10767257916098787708411086280⟩, ⟨.privateRow 5 28, 19890048188453985678852075360⟩, ⟨.privateRow 5 29, 25472756682171478863800416800⟩, ⟨.privateRow 6 21, 38368667905601561630902800⟩, ⟨.privateRow 6 22, 439977553680681065280681450⟩, ⟨.privateRow 6 23, 1172696504032107879921954000⟩, ⟨.privateRow 6 24, 2277550664186015504879993400⟩, ⟨.privateRow 6 25, 3864330679166270965099768320⟩, ⟨.privateRow 6 26, 7178979705495450084097866000⟩, ⟨.privateRow 6 27, 10000759632868814055268822800⟩, ⟨.privateRow 6 28, 10836119577971472616390759200⟩, ⟨.privateRow 7 19, 26096907725267458923043200⟩, ⟨.privateRow 7 20, 184645978072031266903912800⟩, ⟨.privateRow 7 21, 448307593423344562213706400⟩, ⟨.privateRow 7 22, 866124412004412348440796000⟩, ⟨.privateRow 7 23, 1470902495539033146085095600⟩, ⟨.privateRow 7 24, 2723957947066666980303073440⟩, ⟨.privateRow 7 25, 3904516810288453653334240200⟩, ⟨.privateRow 7 26, 4621948764628618885691829600⟩, ⟨.privateRow 7 27, 3692712443125345437610612800⟩, ⟨.privateRow 8 17, 11021989436997430567876200⟩, ⟨.privateRow 8 18, 73941238554924466948622400⟩, ⟨.privateRow 8 19, 181953439973392560824551200⟩, ⟨.privateRow 8 20, 351696608016299739392574375⟩, ⟨.privateRow 8 21, 599219175894162040450233000⟩, ⟨.privateRow 8 22, 1114374205574094478595782200⟩, ⟨.privateRow 8 23, 1641604233034845114004929960⟩, ⟨.privateRow 8 24, 2024685091018667021446101600⟩, ⟨.privateRow 8 25, 1246127343881521163575312800⟩, ⟨.privateRow 9 15, 3789323722734542646654000⟩, ⟨.privateRow 9 16, 30050984653338286032595200⟩, ⟨.privateRow 9 17, 78923375484293709106657920⟩, ⟨.privateRow 9 18, 155746696777900912259576000⟩, ⟨.privateRow 9 19, 267097896491184371250237600⟩, ⟨.privateRow 9 20, 499399916015345463936417600⟩, ⟨.privateRow 9 21, 761225709935768732373919200⟩, ⟨.privateRow 9 22, 924779511937205044382021760⟩, ⟨.privateRow 10 13, 1067600770579123319579040⟩, ⟨.privateRow 10 14, 12514653477344167801732080⟩, ⟨.privateRow 10 15, 36783699277226158010950560⟩, ⟨.privateRow 10 16, 76226695019349405017943456⟩, ⟨.privateRow 10 17, 133371014783828998405188960⟩, ⟨.privateRow 10 18, 251286531375061151345916540⟩, ⟨.privateRow 10 19, 396740781599975161237848960⟩, ⟨.privateRow 10 20, 106285587826543832704757760⟩, ⟨.privateRow 11 11, 197703846403541355477600⟩, ⟨.privateRow 11 12, 5322795864710728801320000⟩, ⟨.privateRow 11 13, 18452358997663859844576000⟩, ⟨.privateRow 11 14, 41517807744743684650296000⟩, ⟨.privateRow 11 15, 75878736249679172232302880⟩, ⟨.privateRow 11 16, 145685767705365141058604800⟩, ⟨.privateRow 11 17, 76560814519771389908700600⟩, ⟨.privateRow 12 10, 2252411678668917585619800⟩, ⟨.privateRow 12 11, 9911806299500621417886600⟩, ⟨.privateRow 12 12, 25190765095917894377104200⟩, ⟨.privateRow 12 13, 49524813524087109547138800⟩, ⟨.privateRow 12 14, 37786147643876841565656300⟩, ⟨.privateRow 13 8, 932032418759552104394400⟩, ⟨.privateRow 13 9, 5592194512557312626366400⟩, ⟨.privateRow 13 10, 16919973140558022818236800⟩, ⟨.privateRow 13 11, 17087261010591788580564000⟩, ⟨.privateRow 14 6, 378638170121068042410225⟩, ⟨.privateRow 14 7, 3365672623298382599202000⟩, ⟨.privateRow 14 8, 8510343633197338857982200⟩, ⟨.privateRow 15 4, 332607647478898986274080⟩, ⟨.privateRow 15 5, 2120373752677981037497260⟩, ⟨.privateRow 15 6, 1130866001428256553331872⟩, ⟨.privateRow 16 3, 1247278678045871198527800⟩, ⟨.hall 6 28, 924190490822402769447081600⟩, ⟨.hall 5 29, 6730537485167173586580191520⟩, ⟨.hall 4 30, 19570365745684643046732775200⟩, ⟨.hall 3 31, 45036738506880317236441802400⟩, ⟨.hall 2 32, 93036003250835567170930281600⟩, ⟨.assumptionRow 19, 77351636119829893712352⟩]
  caps := #[0, 0, 349824359703890114501294760, 355568948512687173992703360, 39488809053284329528625220, 9299108388202764420921016, 7204422640273171258041030, 1464946715072605838570640, 4704586618808080082503425, 0, 2221715572473485293013004, 2963756877134719332760016, 970697138552989800094296, 293825836506225132561760, 23115003482916660486649797, 0, 0, 51171673257431799116832480, 9821322769140717684602368, 1316633525274035146287648] }

theorem case_54_35_19_checked :
    (Witness.linear .conditional case_54_35_19).check 54 35 19 = true := by
  change case_54_35_19.check 54 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_20 : Certificate := {
  objectiveScale := 162631602162617588000000
  eta := 47252444263478700301384939209600
  rows := #[⟨.count 2, 6436436933729064998943682675200⟩, ⟨.count 3, 845774682468193076236907068800⟩, ⟨.count 4, 106442762384434648082362452000⟩, ⟨.count 5, 12128537865318051534484327200⟩, ⟨.count 6, 1138943615724172671569956800⟩, ⟨.count 7, 91339177038436106230651200⟩, ⟨.count 8, 17397938483511639282028800⟩, ⟨.count 9, 7117338470527488797193600⟩, ⟨.count 10, 3558669235263744398596800⟩, ⟨.path 6, 24521417987783903541154800⟩, ⟨.path 7, 57238620405385824920314800⟩, ⟨.privateRow 2 33, 569051771918698697636597990400⟩, ⟨.privateRow 3 29, 2855436653606347797162976800⟩, ⟨.privateRow 3 30, 92881794250640804913657753600⟩, ⟨.privateRow 3 31, 172739781718166188521443448000⟩, ⟨.privateRow 4 27, 13752744159869385009207228360⟩, ⟨.privateRow 4 28, 34911953837842957782392385900⟩, ⟨.privateRow 4 29, 61999728528304165536419882400⟩, ⟨.privateRow 4 30, 112528235054620453659979588200⟩, ⟨.privateRow 5 24, 1518591487632230228759942400⟩, ⟨.privateRow 5 25, 5890869479106693095731276560⟩, ⟨.privateRow 5 26, 11954384501098100025271218912⟩, ⟨.privateRow 5 27, 21415774902047608478722326000⟩, ⟨.privateRow 5 28, 41291687265483740950657752960⟩, ⟨.privateRow 5 29, 55590545465209521520411497840⟩, ⟨.privateRow 6 21, 119593567214535861691644400⟩, ⟨.privateRow 6 22, 802208069763169492519796700⟩, ⟨.privateRow 6 23, 2131336229222438626534660800⟩, ⟨.privateRow 6 24, 4264307213719050753188934000⟩, ⟨.privateRow 6 25, 7546915036674429269842628640⟩, ⟨.privateRow 6 26, 14744675195407884328844041800⟩, ⟨.privateRow 6 27, 21845907863305141774900341600⟩, ⟨.privateRow 6 28, 25403087258869202343996935400⟩, ⟨.privateRow 7 18, 1186223078421248132865600⟩, ⟨.privateRow 7 19, 77824706966422600716932400⟩, ⟨.privateRow 7 20, 325589991620003535135110400⟩, ⟨.privateRow 7 21, 791295523526859736630845600⟩, ⟨.privateRow 7 22, 1578729769890287043114914400⟩, ⟨.privateRow 7 23, 2806349612885011386331538400⟩, ⟨.privateRow 7 24, 5504956278161418549395084160⟩, ⟨.privateRow 7 25, 8457262167824175795274785600⟩, ⟨.privateRow 7 26, 10883653231328209773714873600⟩, ⟨.privateRow 7 27, 9925679243579850135748162800⟩, ⟨.privateRow 8 15, 83643935016882881163600⟩, ⟨.privateRow 8 17, 35586692352637443985968000⟩, ⟨.privateRow 8 18, 129669010259922686523870900⟩, ⟨.privateRow 8 19, 311048559901393856469327400⟩, ⟨.privateRow 8 20, 621500575905132582945911625⟩, ⟨.privateRow 8 21, 1111603998107225809841054400⟩, ⟨.privateRow 8 22, 2199933075534872804630704200⟩, ⟨.privateRow 8 23, 3494049733066746906558946440⟩, ⟨.privateRow 8 24, 4706006438395495991106899550⟩, ⟨.privateRow 8 25, 4983603232896735089755312200⟩, ⟨.privateRow 8 26, 422171851013962121952980100⟩, ⟨.privateRow 9 15, 14168775658920463809228000⟩, ⟨.privateRow 9 16, 54278692376244990322032000⟩, ⟨.privateRow 9 17, 131828924781881375832463680⟩, ⟨.privateRow 9 18, 266021508882987312759304000⟩, ⟨.privateRow 9 19, 479036419835780704322224800⟩, ⟨.privateRow 9 20, 955700393514718912378718400⟩, ⟨.privateRow 9 21, 1574052123782861758527492000⟩, ⟨.privateRow 9 22, 2228438675122156742401316160⟩, ⟨.privateRow 9 23, 1494838782657176188766133600⟩, ⟨.privateRow 10 13, 5502250125292404800907360⟩, ⟨.privateRow 10 14, 24228606376753993113779880⟩, ⟨.privateRow 10 15, 61532626231560380419373760⟩, ⟨.privateRow 10 16, 126475104621273475926130272⟩, ⟨.privateRow 10 17, 230245899521564262589212960⟩, ⟨.privateRow 10 18, 462271133660760397377724320⟩, ⟨.privateRow 10 19, 788092721215122366672108480⟩, ⟨.privateRow 10 20, 1090020386761284909290199840⟩, ⟨.privateRow 11 11, 2231229123697109583247200⟩, ⟨.privateRow 11 12, 11618902973254276583452800⟩, ⟨.privateRow 11 13, 32060973758440956479950800⟩, ⟨.privateRow 11 14, 68333638547842203047803200⟩, ⟨.privateRow 11 15, 126570002467547175776759520⟩, ⟨.privateRow 11 16, 256092382374720569128651200⟩, ⟨.privateRow 11 17, 449825676529657469050409400⟩, ⟨.privateRow 11 18, 119074202348190050670508800⟩, ⟨.privateRow 12 9, 1014879744871512291451680⟩, ⟨.privateRow 12 10, 6097045406052070016246700⟩, ⟨.privateRow 12 11, 18778063411290206821228200⟩, ⟨.privateRow 12 12, 42588703579429533659133000⟩, ⟨.privateRow 12 13, 81552836641460809134510000⟩, ⟨.privateRow 12 14, 166965840883950763234720140⟩, ⟨.privateRow 12 15, 73760010029054554039434600⟩, ⟨.privateRow 13 7, 524268235552248058721850⟩, ⟨.privateRow 13 8, 3603858685870268136991680⟩, ⟨.privateRow 13 9, 12449290164859731680125200⟩, ⟨.privateRow 13 10, 30828764620508261914584000⟩, ⟨.privateRow 13 11, 62446172056889990994424800⟩, ⟨.privateRow 13 12, 26774749484365314998966400⟩, ⟨.privateRow 14 5, 356365336584534628150800⟩, ⟨.privateRow 14 6, 2524254467473786949401500⟩, ⟨.privateRow 14 7, 9558510250167406581733680⟩, ⟨.privateRow 14 8, 26108003349300310733809800⟩, ⟨.privateRow 14 9, 6990243140696640782958000⟩, ⟨.privateRow 15 3, 314129444841182375925520⟩, ⟨.privateRow 15 4, 1995645884873393917644480⟩, ⟨.privateRow 15 5, 8834890636158254322905250⟩, ⟨.privateRow 15 6, 3015642670475350808884992⟩, ⟨.privateRow 16 2, 2355970836308867819441400⟩, ⟨.privateRow 16 3, 1247278678045871198527800⟩, ⟨.hall 6 28, 3774891991220799738677388000⟩, ⟨.hall 5 29, 17101521106598809727761234320⟩, ⟨.hall 4 30, 44858900708268615601038806400⟩, ⟨.hall 3 31, 97844646817325434975311062700⟩, ⟨.hall 2 32, 195160056913149123370454880000⟩, ⟨.assumptionRow 20, 82385452361818353107360⟩]
  caps := #[0, 4061712014594628857866603200, 0, 382132809506489031464073600, 0, 135541599174257170654760, 11145732061784894182560380, 15892721789858337102410160, 0, 0, 0, 7583745303557612616748720, 82385452361818353107360, 24300450064446346374850200, 145185877867773367024400, 0, 57495011378695776963757680, 310323760337028299361820320, 78667722745407583852224160, 15677904839484953855389600] }

theorem case_54_35_20_checked :
    (Witness.linear .conditional case_54_35_20).check 54 35 20 = true := by
  change case_54_35_20.check 54 35 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_21 : Certificate := {
  objectiveScale := 1982983949127640659200000
  eta := 897260071261617883643068538092800
  rows := #[⟨.count 2, 122603742237645576834717568377600⟩, ⟨.count 3, 16097199010730375082747198796800⟩, ⟨.count 4, 1995356516220087275526421550400⟩, ⟨.count 5, 221367019779581220314713944000⟩, ⟨.count 6, 20064793911055637703402643200⟩, ⟨.count 7, 1174360847637035651536944000⟩, ⟨.path 6, 106277208545753230531946400⟩, ⟨.path 7, 1178263560711640421717899200⟩, ⟨.privateRow 2 33, 11281066883847716073417422323200⟩, ⟨.privateRow 3 29, 30024492337920211490961201600⟩, ⟨.privateRow 4 27, 250755399991698037494425967600⟩, ⟨.privateRow 4 30, 5537801333606609855441968914600⟩, ⟨.privateRow 5 24, 29617380577406039131761727680⟩, ⟨.privateRow 5 25, 107138244975313025862661553280⟩, ⟨.privateRow 5 26, 176360814654739466005212102144⟩, ⟨.privateRow 5 27, 311491385763406126332497483040⟩, ⟨.privateRow 5 28, 521679795118869030617525872320⟩, ⟨.privateRow 5 29, 1323367666521381525122789911200⟩, ⟨.privateRow 6 21, 3029105360968544339281800000⟩, ⟨.privateRow 6 22, 15048595433291728277551982400⟩, ⟨.privateRow 6 23, 38473099918998762873838039200⟩, ⟨.privateRow 6 25, 278558952278956112275825753440⟩, ⟨.privateRow 6 26, 183618308771191220758584152400⟩, ⟨.privateRow 6 27, 391324063372804306103137178400⟩, ⟨.privateRow 7 18, 251648753065079068186488000⟩, ⟨.privateRow 7 19, 1771607221578156640032875520⟩, ⟨.privateRow 7 20, 6071259175799722408025121600⟩, ⟨.privateRow 7 21, 14146854068141861616550400400⟩, ⟨.privateRow 7 22, 22181040091593397867294728000⟩, ⟨.privateRow 7 23, 27096978510596458331058391200⟩, ⟨.privateRow 7 24, 156998624062241529060186133440⟩, ⟨.privateRow 7 25, 138088059098577720682865515200⟩, ⟨.privateRow 7 26, 217748869929956639045454883200⟩, ⟨.privateRow 7 27, 173528591821909689452462575200⟩, ⟨.privateRow 8 14, 2097072942208992234887400⟩, ⟨.privateRow 8 15, 12797522057583080818030800⟩, ⟨.privateRow 8 16, 162290144916507010177674900⟩, ⟨.privateRow 8 17, 820273258728293083876562400⟩, ⟨.privateRow 8 18, 2442670563085034155196843520⟩, ⟨.privateRow 8 19, 5527107581980603904409524400⟩, ⟨.privateRow 8 20, 10406549719633606549609148550⟩, ⟨.privateRow 8 21, 17249123973983030796027160800⟩, ⟨.privateRow 8 22, 28494561122526406711597794000⟩, ⟨.privateRow 8 23, 90075434281840029532302833040⟩, ⟨.privateRow 8 24, 93486463227205769335162848300⟩, ⟨.privateRow 8 25, 111825249602771061485240112000⟩, ⟨.privateRow 8 26, 50898756404668520197030381200⟩, ⟨.privateRow 9 12, 1423467694105497759438720⟩, ⟨.privateRow 9 13, 9150863747821057024963200⟩, ⟨.privateRow 9 14, 87050524370297747596444800⟩, ⟨.privateRow 9 15, 377218938937956906251260800⟩, ⟨.privateRow 9 16, 1054013124408116295511670400⟩, ⟨.privateRow 9 17, 2352280364509335047472484800⟩, ⟨.privateRow 9 18, 4574076190392332800329753600⟩, ⟨.privateRow 9 19, 8066613489034092615519296400⟩, ⟨.privateRow 9 20, 15517831391027219146109817600⟩, ⟨.privateRow 9 21, 23112370459959598620753350400⟩, ⟨.privateRow 9 22, 54131629471443868795935644160⟩, ⟨.privateRow 9 23, 60970680007773732781158974400⟩, ⟨.privateRow 10 10, 1201050866901513734526420⟩, ⟨.privateRow 10 11, 5551524007011441261811008⟩, ⟨.privateRow 10 12, 47126948301278443678560480⟩, ⟨.privateRow 10 13, 187240750532338551433862400⟩, ⟨.privateRow 10 14, 506576565639794015140254480⟩, ⟨.privateRow 10 15, 1119233826028950011035044480⟩, ⟨.privateRow 10 16, 2183030055680191363875220992⟩, ⟨.privateRow 10 17, 3898878014154958363102654080⟩, ⟨.privateRow 10 18, 7803627832548101904462992880⟩, ⟨.privateRow 10 20, 44797595934270593612856097440⟩, ⟨.privateRow 10 21, 21531799381347990758597910336⟩, ⟨.privateRow 11 8, 837333937709116329081600⟩, ⟨.privateRow 11 9, 4003502889671712448421400⟩, ⟨.privateRow 11 10, 28469353882109955188774400⟩, ⟨.privateRow 11 11, 106251695738588939900961600⟩, ⟨.privateRow 11 12, 282503588522475709180915200⟩, ⟨.privateRow 11 13, 620987781553523397555141600⟩, ⟨.privateRow 11 14, 1209300509219625141995894400⟩, ⟨.privateRow 11 15, 2165806096581514840986012480⟩, ⟨.privateRow 11 16, 4351857067034752316772931200⟩, ⟨.privateRow 11 17, 7719643238595877536656108400⟩, ⟨.privateRow 11 18, 1996921822302283999669747200⟩, ⟨.privateRow 11 19, 29471712383375909861045832000⟩, ⟨.privateRow 12 6, 543685577609738727563400⟩, ⟨.privateRow 12 7, 3454002493050104857461600⟩, ⟨.privateRow 12 8, 19572680793950594192282400⟩, ⟨.privateRow 12 9, 71114073551353825565292720⟩, ⟨.privateRow 12 10, 187338516170669972983274400⟩, ⟨.privateRow 12 11, 411026296672962478037930400⟩, ⟨.privateRow 12 12, 799217799086315929518198000⟩, ⟨.privateRow 12 13, 1428805697958393376036615200⟩, ⟨.privateRow 12 14, 2848803689559508984686703320⟩, ⟨.privateRow 12 15, 5144352935343347840204890800⟩, ⟨.privateRow 12 16, 8618096012086371005289344250⟩, ⟨.privateRow 12 17, 4031972243553822403610174400⟩, ⟨.privateRow 12 23, 68024852099375290115277481200⟩, ⟨.privateRow 13 4, 882978080930101993636800⟩, ⟨.privateRow 13 5, 2796097256278656313183200⟩, ⟨.privateRow 13 6, 16776583537671937879099200⟩, ⟨.privateRow 13 7, 57669505910747286459403500⟩, ⟨.privateRow 13 8, 152107690741558903437166080⟩, ⟨.privateRow 13 9, 334333343357890762019191200⟩, ⟨.privateRow 13 10, 650415238691281283928153600⟩, ⟨.privateRow 13 11, 1163176458611921026284211200⟩, ⟨.privateRow 13 12, 2292291368829174784753281600⟩, ⟨.privateRow 13 13, 4153882083927571818864961920⟩, ⟨.privateRow 13 14, 7143096457373207328078681600⟩, ⟨.privateRow 13 15, 9092908277418190330471766400⟩, ⟨.privateRow 14 2, 1817463216581126603569080⟩, ⟨.privateRow 14 3, 3826238350697108639092800⟩, ⟨.privateRow 14 4, 16155228591832236476169600⟩, ⟨.privateRow 14 5, 57731184526694609760429600⟩, ⟨.privateRow 14 6, 152212544388669353048910450⟩, ⟨.privateRow 14 7, 339259800428476965999561600⟩, ⟨.privateRow 14 8, 667268638087642195881790800⟩, ⟨.privateRow 14 9, 1199525722943543558355592800⟩, ⟨.privateRow 14 10, 2341498444028684774264831400⟩, ⟨.privateRow 14 11, 4233037055346223962130893600⟩, ⟨.privateRow 14 12, 7349821247854075984833359520⟩, ⟨.privateRow 14 14, 27134725823556220191286364400⟩, ⟨.privateRow 15 1, 10177794012854308979986848⟩, ⟨.privateRow 15 2, 21426934763903808378919680⟩, ⟨.privateRow 15 3, 73506290092836675966571680⟩, ⟨.privateRow 15 4, 197568942602465997846803520⟩, ⟨.privateRow 15 5, 438917366804342074761932820⟩, ⟨.privateRow 15 6, 882075481114040111598860160⟩, ⟨.privateRow 15 7, 1599367630591391411140790400⟩, ⟨.privateRow 15 8, 3123799854714514833088271040⟩, ⟨.privateRow 15 9, 5631712687112717635592722560⟩, ⟨.privateRow 15 10, 9798439872375193827096429120⟩, ⟨.privateRow 15 11, 16406603948721146075738798976⟩, ⟨.privateRow 15 13, 52135749830846197749982628880⟩, ⟨.privateRow 16 0, 76333455096407317349901360⟩, ⟨.privateRow 16 1, 100438756705799101776186000⟩, ⟨.privateRow 16 2, 318056062901697155624589000⟩, ⟨.privateRow 16 3, 763334550964073173499013600⟩, ⟨.privateRow 16 4, 1550523306645773633669871375⟩, ⟨.privateRow 16 5, 2849782323599206514396317440⟩, ⟨.privateRow 16 7, 21373367426994048857972380800⟩, ⟨.privateRow 16 8, 12086130390264491913734382000⟩, ⟨.privateRow 16 9, 29770047487598853766461530400⟩, ⟨.privateRow 16 12, 254953740022000439948670542400⟩, ⟨.privateRow 17 0, 1821289454931823712208172800⟩, ⟨.privateRow 17 2, 6226415160804989023050777600⟩, ⟨.privateRow 17 3, 5979453982551906525742273200⟩, ⟨.privateRow 17 7, 5937046507498346904992328000⟩, ⟨.privateRow 17 11, 1691040475235743437024814795200⟩, ⟨.privateRow 18 0, 35565735744918668602287374400⟩, ⟨.privateRow 18 3, 111887882181311703386655415680⟩, ⟨.privateRow 18 7, 11010522613906025169258499200⟩, ⟨.privateRow 18 11, 145833248498469598670382979200⟩, ⟨.privateRow 18 13, 20091372493134920098853237425920⟩, ⟨.privateRow 19 4, 3737285961520102257451170585600⟩, ⟨.privateRow 19 11, 1453388985035595322342121894400⟩, ⟨.privateRow 19 12, 100470704265532082354478969242880⟩, ⟨.privateRow 19 13, 241054944518046595605600502771200⟩, ⟨.hall 9 11, 2163898763068467542040⟩, ⟨.hall 14 11, 159282320481508594930560⟩, ⟨.hall 14 17, 14327136935388062348603040⟩, ⟨.hall 15 17, 134811131222894794384036320⟩, ⟨.hall 16 18, 2249828150209899879786566400⟩, ⟨.hall 4 26, 52023789514298470076208000⟩, ⟨.hall 3 30, 53119466453782156565507970600⟩, ⟨.hall 2 32, 10149604607618706439357429881600⟩]
  caps := #[0, 0, 0, 4156682326604042319207723600, 0, 0, 0, 104456002396101236673867360, 72672633879421879576821240, 8819757157429337791427840, 5064782991907471036823920, 0, 291457580330323769042270590, 15010338820883325361762320, 505396358635587714432873450, 0, 164616168159725145484646025, 1625304945666239362889844480, 134222833336907267710511033280, 0] }

theorem case_54_35_21_checked :
    (Witness.linear .conditional case_54_35_21).check 54 35 21 = true := by
  change case_54_35_21.check 54 35 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_35_22 : Certificate := {
  objectiveScale := 3857664305655265651171267356000000
  eta := 1797974431635301736795890343928623448921600
  rows := #[⟨.count 2, 221277131616782079370835819670276336614400⟩, ⟨.count 3, 25423183226185053912332051407762470393600⟩, ⟨.count 4, 2613034096856876301030058201001366529600⟩, ⟨.count 5, 221346122616039026599905920216837428800⟩, ⟨.count 6, 13551803425471777138769750217357393600⟩, ⟨.count 7, 331687496427630908990868012312943200⟩, ⟨.path 5, 2235702634816976212475166641990928000⟩, ⟨.path 6, 8581895051586357895523150142345424200⟩, ⟨.path 7, 248805451857976485325885299625156800⟩, ⟨.path 8, 3849062333322865125912445149012864⟩, ⟨.privateRow 3 32, 37467861846460424320820438494886481129600⟩, ⟨.privateRow 4 27, 352932080573820668711733108501587211960⟩, ⟨.privateRow 5 24, 35398953190171733010968256628369919040⟩, ⟨.privateRow 5 29, 7659438230005662160720121096334588688800⟩, ⟨.privateRow 6 21, 2908846694861366305038961536553986000⟩, ⟨.privateRow 6 22, 16914087987473297603123608699315383300⟩, ⟨.privateRow 6 23, 28936913591402398587438005604811837200⟩, ⟨.privateRow 6 24, 67536575909516545917581065792815192600⟩, ⟨.privateRow 6 25, 157591047409842256878875504421542418000⟩, ⟨.privateRow 6 27, 1342792077799650483260220856133003560800⟩, ⟨.privateRow 7 17, 11845982015272532463959571868319400⟩, ⟨.privateRow 7 18, 159382303478212254969637876046479200⟩, ⟨.privateRow 7 19, 1563669626015974285242663486618160800⟩, ⟨.privateRow 7 20, 6417889811829874254918541381102821600⟩, ⟨.privateRow 7 21, 13883490921899408047760618229670336800⟩, ⟨.privateRow 7 22, 29777414220105068747976089513564023200⟩, ⟨.privateRow 7 23, 62333557364364065825355267171096682800⟩, ⟨.privateRow 7 24, 145089587723057977618576836243176011200⟩, ⟨.privateRow 7 26, 769372839927920438469246273703608391200⟩, ⟨.privateRow 8 15, 10631009500885606057399615779261000⟩, ⟨.privateRow 8 16, 96742186458059015122336503591275100⟩, ⟨.privateRow 8 17, 675938913174490261504117388728649400⟩, ⟨.privateRow 8 18, 2413026536511014862908564789576661780⟩, ⟨.privateRow 8 19, 5690897508151852540371096544591516200⟩, ⟨.privateRow 8 21, 49129236078006949638861664395209991600⟩, ⟨.privateRow 8 22, 47523447404825561904858255764171139600⟩, ⟨.privateRow 8 23, 119855276834124428963850156249282025320⟩, ⟨.privateRow 9 13, 5743506431647288467374337875548800⟩, ⟨.privateRow 9 14, 49482516949576639103532757081651200⟩, ⟨.privateRow 9 15, 289807762030202763916263465303733200⟩, ⟨.privateRow 9 16, 964909080516744462518888763092198400⟩, ⟨.privateRow 9 17, 2353976111010641178353372378293675680⟩, ⟨.privateRow 9 19, 11350245616390975878119324330436094200⟩, ⟨.privateRow 9 20, 35497741500796066372607095239829358400⟩, ⟨.privateRow 9 21, 42911651052980774569242803047516934400⟩, ⟨.privateRow 9 22, 90476308116453405768854469685945136640⟩, ⟨.privateRow 9 23, 73669803183827901437835366552961126800⟩, ⟨.privateRow 9 24, 69473453797205601301359990942638284800⟩, ⟨.privateRow 10 11, 3618409051937791734445832861595744⟩, ⟨.privateRow 10 12, 25845778942412798103184520439969600⟩, ⟨.privateRow 10 13, 134994491553063768554325302913379680⟩, ⟨.privateRow 10 14, 431193745355920181688128416006826160⟩, ⟨.privateRow 10 15, 1057562281998181856931213877275483360⟩, ⟨.privateRow 10 16, 1763974412819673470542343520027925200⟩, ⟨.privateRow 10 17, 983001125776433421191117927400177120⟩, ⟨.privateRow 10 18, 11465833683327877558525232880181513800⟩, ⟨.privateRow 10 19, 29963011527939156841021814546056757280⟩, ⟨.privateRow 10 20, 39015495602519239376662192830156109680⟩, ⟨.privateRow 10 21, 70023451973100145644995757537600837888⟩, ⟨.privateRow 10 22, 79351710508995772736397114654794665920⟩, ⟨.privateRow 10 23, 73501949208363009432376351528548213120⟩, ⟨.privateRow 11 9, 2512784063845688704476272820552600⟩, ⟨.privateRow 11 10, 16081818008612407708648146051536640⟩, ⟨.privateRow 11 11, 71793830395591105842179223444360000⟩, ⟨.privateRow 11 12, 219578668963746336021926609549827200⟩, ⟨.privateRow 11 13, 531035032159388879545985656076782800⟩, ⟨.privateRow 11 14, 1059938005113090508069991444305824000⟩, ⟨.privateRow 11 15, 1704672708912915217116703481462883840⟩, ⟨.privateRow 11 16, 1344618672386759644528636655975702400⟩, ⟨.privateRow 11 17, 10973328006814122572447883407353204200⟩, ⟨.privateRow 11 18, 25952033811398272939830945690667252800⟩, ⟨.privateRow 11 19, 34468696598459260522202526370460198400⟩, ⟨.privateRow 11 20, 52808669885780993813273349596733441600⟩, ⟨.privateRow 11 21, 62136124330776190284289274306624692800⟩, ⟨.privateRow 12 7, 1625919100135445632308176530945800⟩, ⟨.privateRow 12 8, 10365234263363465905964625384779475⟩, ⟨.privateRow 12 9, 46067707837170959582065001710131000⟩, ⟨.privateRow 12 10, 136228793175634123335535076485673100⟩, ⟨.privateRow 12 11, 329561294527453787779388089157091000⟩, ⟨.privateRow 12 12, 688712232165705845751871775566458450⟩, ⟨.privateRow 12 13, 1286545440688992616691851684122931200⟩, ⟨.privateRow 12 14, 2404734349100324090183793089268838200⟩, ⟨.privateRow 12 15, 2183609351481903484189881081060209400⟩, ⟨.privateRow 12 17, 53330611032756941152745992551173938800⟩, ⟨.privateRow 12 18, 27631411160735141557322588025736573800⟩, ⟨.privateRow 12 19, 57138699384599884588826862921109681920⟩, ⟨.privateRow 12 21, 142247868259616488997500312280542501800⟩, ⟨.privateRow 13 5, 2632440447838340547546571526293200⟩, ⟨.privateRow 13 6, 8361869657839434680442050730578400⟩, ⟨.privateRow 13 7, 35537946045817597391878715604958200⟩, ⟨.privateRow 13 8, 104244641734398285682844232441210720⟩, ⟨.privateRow 13 9, 250457905465762114952288090930181600⟩, ⟨.privateRow 13 10, 524868126215152207633901030473228800⟩, ⟨.privateRow 13 11, 1002959810626407748615243751517709200⟩, ⟨.privateRow 13 12, 2080585204864230247306353895417552800⟩, ⟨.privateRow 13 13, 3586963354224522830086958361727114320⟩, ⟨.privateRow 13 14, 3464291629355256160571288128601851200⟩, ⟨.privateRow 13 15, 1172752219511980713931997614963620600⟩, ⟨.privateRow 13 16, 54119214978345084028203872621264916000⟩, ⟨.privateRow 13 17, 54949561908177520589487134039844256800⟩, ⟨.privateRow 14 4, 11407241940632809039368476613937200⟩, ⟨.privateRow 14 5, 36234768517304216948582219832506400⟩, ⟨.privateRow 14 6, 96248603874089326269671521430095125⟩, ⟨.privateRow 14 7, 239552080753288989826738008892681200⟩, ⟨.privateRow 14 8, 505992660366641029531987426946785800⟩, ⟨.privateRow 14 9, 971370525252347662044684893202190800⟩, ⟨.privateRow 14 10, 2027637254947481806747746718127337300⟩, ⟨.privateRow 14 13, 1380276274816569893763585670286401200⟩, ⟨.privateRow 14 14, 48727459854655622912792368916009491950⟩, ⟨.privateRow 14 15, 34495499628473614535050273280546092800⟩, ⟨.privateRow 14 16, 99790552496655813476395433418722625600⟩, ⟨.privateRow 15 2, 15129605100207725673267663719537760⟩, ⟨.privateRow 15 3, 47910416150657797965347601778536240⟩, ⟨.privateRow 15 5, 538992181694900227110160520008532700⟩, ⟨.privateRow 15 6, 498268327966841098839615058496776896⟩, ⟨.privateRow 15 7, 1211449094095204319980932216400130640⟩, ⟨.privateRow 15 8, 2520824972849994908330596893578368320⟩, ⟨.privateRow 15 9, 4862907239291766493482781580521428360⟩, ⟨.privateRow 15 10, 418127268223922600424851797339952640⟩, ⟨.privateRow 15 12, 2427461084966661763577611823445836160⟩, ⟨.privateRow 15 13, 78872522588020399900453489427915285100⟩, ⟨.privateRow 15 14, 96464200746767286360515585638098538080⟩, ⟨.privateRow 15 16, 324775129002079080847498322936341463712⟩, ⟨.privateRow 16 1, 113472038251557942549507477896533200⟩, ⟨.privateRow 16 2, 59888020188322247456684502223170300⟩, ⟨.privateRow 16 3, 253643379621129518640075538827544800⟩, ⟨.privateRow 16 4, 1751724590508425738108021690027731275⟩, ⟨.privateRow 16 5, 1652909357197694029804492261359500280⟩, ⟨.privateRow 16 6, 4234938570459930355865546942924185500⟩, ⟨.privateRow 16 7, 8209265536583864997523983304745344200⟩, ⟨.privateRow 16 8, 15181613117739689730269521313573671050⟩, ⟨.privateRow 16 9, 3429950247149365081610112400054299000⟩, ⟨.privateRow 16 11, 4910817655442424291448129182299964600⟩, ⟨.privateRow 16 12, 10510347543050554428648130140166387650⟩, ⟨.privateRow 16 13, 139829971708276973204578786333642197600⟩, ⟨.privateRow 16 15, 1623228854392361523964959422057697079320⟩, ⟨.privateRow 17 0, 907776306012463540396059823172265600⟩, ⟨.privateRow 17 1, 319402774337718653102317345190241600⟩, ⟨.privateRow 17 3, 5389921816949002271101605200085327000⟩, ⟨.privateRow 17 4, 19164166460263119186139040711414496000⟩, ⟨.privateRow 17 5, 13551803425471777138769750217357393600⟩, ⟨.privateRow 17 6, 36706749604657820594989393362632380800⟩, ⟨.privateRow 17 7, 66116374287907761192179690454380011200⟩, ⟨.privateRow 17 8, 26655613349275065777084302080421980800⟩, ⟨.privateRow 17 12, 266108139991082169270387822449927001600⟩, ⟨.privateRow 17 13, 199307331186736439535846023398710758400⟩, ⟨.privateRow 17 14, 2369840824476137318557953774373516575360⟩, ⟨.privateRow 18 5, 71423374230749855736033578651387102400⟩, ⟨.privateRow 18 8, 1861894592446863344529338500317475358880⟩, ⟨.privateRow 18 12, 1677822773596036084746473014284339124800⟩, ⟨.privateRow 18 13, 6724322727577123260032466604821118356480⟩, ⟨.privateRow 18 14, 12779145299864954451297165822388971295200⟩, ⟨.privateRow 19 3, 2764567898796242536309029044340908294400⟩, ⟨.privateRow 19 8, 43590813030514490900791862002183412601600⟩, ⟨.privateRow 19 13, 313370054437414992041847326332960911780000⟩, ⟨.hall 17 2, 25552221947017492248185387615219328000⟩, ⟨.hall 15 7, 3615530630564346208685287285918950⟩, ⟨.hall 14 8, 330562800508740224794083408998304⟩, ⟨.hall 16 8, 202564798299915402050838554475259200⟩, ⟨.hall 17 8, 1917533438943576669149226859061695200⟩, ⟨.hall 10 11, 68171120220920591298718248226272⟩, ⟨.hall 18 11, 74345383127850413743810273045572554400⟩, ⟨.hall 13 14, 540985158175240169753331919349400⟩, ⟨.hall 16 14, 952275144542486262964494128229729600⟩, ⟨.hall 17 16, 123289470894359400097494495243433257600⟩, ⟨.hall 6 20, 537644742490806776393715683833440⟩, ⟨.hall 14 20, 20533035493139056270863257905086960000⟩, ⟨.hall 8 22, 4315128468327261522145534221873824⟩, ⟨.hall 9 23, 58312053567766720643569383423408336⟩, ⟨.hall 6 27, 13588216690385718322304286044184148800⟩, ⟨.hall 4 28, 5736139857574973777755532558210199840⟩, ⟨.hall 5 29, 3650055054437864337990007041497783444400⟩, ⟨.hall 3 31, 14070929895327065328937850535342754666200⟩]
  caps := #[0, 163467074177473133147261225280958934784, 41641456840489286791159819582478060352, 2279456775875467421714130015001470120, 0, 755004562879662242272629688915274544, 0, 531644480402756157863325013053945456, 3849062333322865125912445149012864, 1723051929494186540212301362664640, 340254257585477966860989977077422168, 0, 42076336997456936588603190166879230, 986448530184511587825590071979057280, 118920686426839083651753819526422255, 2335535634748712620579930894393643712, 5381169195134953405850382602740241100, 0, 332801803546227737712270848891459616480, 0] }

theorem case_54_35_22_checked :
    (Witness.linear .conditional case_54_35_22).check 54 35 22 = true := by
  change case_54_35_22.check 54 35 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_36_1_checked :
    (Witness.rising).check 54 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_36_2_checked :
    (Witness.rising).check 54 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_36_3_checked :
    (Witness.rising).check 54 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_36_4_checked :
    (Witness.rising).check 54 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_36_5_checked :
    (Witness.rising).check 54 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_36_6_checked :
    (Witness.rising).check 54 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_36_7_checked :
    (Witness.rising).check 54 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_36_8_checked :
    (Witness.rising).check 54 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_36_9_checked :
    (Witness.rising).check 54 36 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_36_10_checked :
    (Witness.linear .positive case_54_36_10).check 54 36 10 = true := by
  change case_54_36_10.check 54 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_36_11_checked :
    (Witness.linear .positive case_54_36_11).check 54 36 11 = true := by
  change case_54_36_11.check 54 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_36_12_checked :
    (Witness.linear .positive case_54_36_12).check 54 36 12 = true := by
  change case_54_36_12.check 54 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_54_36_13_checked :
    (Witness.linear .positive case_54_36_13).check 54 36 13 = true := by
  change case_54_36_13.check 54 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_54_36_14_checked :
    (Witness.linear .positive case_54_36_14).check 54 36 14 = true := by
  change case_54_36_14.check 54 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_54_36_15_checked :
    (Witness.linear .positive case_54_36_15).check 54 36 15 = true := by
  change case_54_36_15.check 54 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_54_36_16_checked :
    (Witness.linear .positive case_54_36_16).check 54 36 16 = true := by
  change case_54_36_16.check 54 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_17 : Certificate := {
  objectiveScale := 1018190316000000
  eta := 1157521629450399895281600
  rows := #[⟨.count 2, 139011384253375704470400⟩, ⟨.count 3, 15889831619261036837400⟩, ⟨.count 4, 1710686518422532691040⟩, ⟨.count 5, 179322064825907203200⟩, ⟨.count 6, 22547892766571172000⟩, ⟨.count 7, 4951694097756806400⟩, ⟨.count 8, 1463000528882692800⟩, ⟨.count 9, 405138607998284160⟩, ⟨.count 10, 112538502221745600⟩, ⟨.path 6, 5433015206809990800⟩, ⟨.privateRow 2 34, 12970962689073954364800⟩, ⟨.privateRow 3 33, 23278532915316966487200⟩, ⟨.privateRow 4 28, 394037247446620065288⟩, ⟨.privateRow 5 24, 5819345853725353950⟩, ⟨.privateRow 5 25, 38508263920948021200⟩, ⟨.privateRow 5 26, 142346468125693431600⟩, ⟨.privateRow 6 22, 5973472244912972800⟩, ⟨.privateRow 6 23, 20574952149496194450⟩, ⟨.privateRow 6 24, 50464331429945004000⟩, ⟨.privateRow 6 25, 73103805273579280200⟩, ⟨.privateRow 6 26, 96009811631148935520⟩, ⟨.privateRow 7 20, 3417553158541081560⟩, ⟨.privateRow 7 21, 9205828114281999200⟩, ⟨.privateRow 7 22, 19513874842834021650⟩, ⟨.privateRow 7 23, 33780785563587090600⟩, ⟨.privateRow 7 24, 52103316912557110200⟩, ⟨.privateRow 7 25, 88538058930069468720⟩, ⟨.privateRow 7 26, 81515053506599212500⟩, ⟨.privateRow 7 28, 450891537999757054200⟩, ⟨.privateRow 8 18, 1693192919790808800⟩, ⟨.privateRow 8 19, 4235667877370950020⟩, ⟨.privateRow 8 20, 8390370554532366400⟩, ⟨.privateRow 8 21, 14651106257993505300⟩, ⟨.privateRow 8 22, 23428104623234110800⟩, ⟨.privateRow 8 23, 42232417510839656100⟩, ⟨.privateRow 8 24, 62937157367511226800⟩, ⟨.privateRow 8 25, 73730303096215515750⟩, ⟨.privateRow 9 16, 822468887070590760⟩, ⟨.privateRow 9 17, 2128000769283916800⟩, ⟨.privateRow 9 18, 4093025325804887472⟩, ⟨.privateRow 9 19, 7009898260612287040⟩, ⟨.privateRow 9 20, 11158192495286076240⟩, ⟨.privateRow 9 21, 20345353508802722400⟩, ⟨.privateRow 9 22, 31653329391569645760⟩, ⟨.privateRow 9 23, 45458802587451917664⟩, ⟨.privateRow 9 24, 56764420520648480640⟩, ⟨.privateRow 9 27, 236319600815443585440⟩, ⟨.privateRow 10 14, 413795415861495360⟩, ⟨.privateRow 10 15, 1188219019291263960⟩, ⟨.privateRow 10 16, 2318293145767959360⟩, ⟨.privateRow 10 17, 3919716032383399248⟩, ⟨.privateRow 10 18, 6152104788122092800⟩, ⟨.privateRow 10 19, 11049874186897646100⟩, ⟨.privateRow 10 20, 17578514047036662720⟩, ⟨.privateRow 10 22, 88115396469582369888⟩, ⟨.privateRow 10 25, 119521516284604914480⟩, ⟨.privateRow 11 12, 224072196387939900⟩, ⟨.privateRow 11 13, 742321274270360400⟩, ⟨.privateRow 11 14, 1542715301289762600⟩, ⟨.privateRow 11 15, 2640818262362553000⟩, ⟨.privateRow 11 16, 4110468793649258040⟩, ⟨.privateRow 11 17, 2083525325855373400⟩, ⟨.privateRow 11 18, 21596841941991866550⟩, ⟨.privateRow 11 20, 28350324351361412400⟩, ⟨.privateRow 11 22, 91170254112391654200⟩, ⟨.privateRow 12 10, 134108381814246840⟩, ⟨.privateRow 12 11, 522643732894611900⟩, ⟨.privateRow 12 12, 1207315525208562000⟩, ⟨.privateRow 12 13, 2181103352583355200⟩, ⟨.privateRow 12 14, 622980994441806000⟩, ⟨.privateRow 12 15, 11647534018339559340⟩, ⟨.privateRow 12 18, 57159223960075380000⟩, ⟨.privateRow 12 20, 18117895011256600560⟩, ⟨.privateRow 13 8, 91186331041280475⟩, ⟨.privateRow 13 9, 421483485701918640⟩, ⟨.privateRow 13 10, 1108446829281019800⟩, ⟨.privateRow 13 11, 2186771500589029200⟩, ⟨.privateRow 13 12, 3651137537854907100⟩, ⟨.privateRow 13 13, 1165577344439508000⟩, ⟨.privateRow 13 16, 62371450432235844900⟩, ⟨.privateRow 13 19, 108627789269539940400⟩, ⟨.privateRow 14 6, 74379438653279760⟩, ⟨.privateRow 14 7, 402325145442740520⟩, ⟨.privateRow 14 8, 1203143768276385936⟩, ⟨.privateRow 14 9, 2660272390274447520⟩, ⟨.privateRow 14 10, 4819059434424034800⟩, ⟨.privateRow 14 11, 8774519838703578960⟩, ⟨.privateRow 14 12, 2570700929322445920⟩, ⟨.privateRow 14 13, 241395087265644312⟩, ⟨.privateRow 14 15, 99791004824994032550⟩, ⟨.privateRow 14 16, 49888318034899824480⟩, ⟨.privateRow 14 19, 291915630529097014440⟩, ⟨.privateRow 15 4, 67054190907123420⟩, ⟨.privateRow 15 5, 473323700520871200⟩, ⟨.privateRow 15 6, 1609300581770962080⟩, ⟨.privateRow 15 7, 3996429778064555832⟩, ⟨.privateRow 15 8, 7960290377688508860⟩, ⟨.privateRow 15 9, 15659732584155900240⟩, ⟨.privateRow 15 11, 45682191514362082680⟩, ⟨.privateRow 15 16, 749062366623475724820⟩, ⟨.privateRow 16 2, 105875038274405400⟩, ⟨.privateRow 16 3, 670541909071234200⟩, ⟨.privateRow 16 4, 2839942203125227200⟩, ⟨.privateRow 16 5, 7795049692953097575⟩, ⟨.privateRow 16 6, 17299981254037842360⟩, ⟨.privateRow 16 7, 37215075953453498100⟩, ⟨.privateRow 16 8, 67776312963046287600⟩, ⟨.privateRow 16 12, 350916932413945898000⟩, ⟨.privateRow 16 15, 1369246578323460236400⟩, ⟨.privateRow 16 20, 13815845494503709456800⟩, ⟨.privateRow 17 1, 1694000612390486400⟩, ⟨.privateRow 17 2, 7152447030093164800⟩, ⟨.privateRow 17 10, 3624144910148206604160⟩, ⟨.privateRow 17 19, 62360397543624780600000⟩, ⟨.hall 13 8, 7971017374320⟩, ⟨.hall 10 13, 12443443412400⟩, ⟨.hall 12 14, 8881733160300⟩, ⟨.hall 14 14, 6623008930201664⟩, ⟨.hall 10 20, 603434743485840⟩, ⟨.hall 6 27, 233558970374489760⟩, ⟨.hall 4 31, 4406667318034336915560⟩, ⟨.hall 3 32, 6972294770522693211600⟩]
  caps := #[0, 0, 9200195131073403600, 1767364000950525120, 688885572619504260, 59605640288594400, 217871292724792850, 3215385777764160, 0, 168078235914437888, 147651225949268844, 134750712315672740, 14254664424000000, 1485434827453145580, 11080309748367288, 3409522193852194563, 1018190316000000, 0, 0] }

theorem case_54_36_17_checked :
    (Witness.linear .positive case_54_36_17).check 54 36 17 = true := by
  change case_54_36_17.check 54 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_18 : Certificate := {
  objectiveScale := 230043815142261120000
  eta := 156272855910072116770402848000
  rows := #[⟨.count 2, 18450039494552186335281667200⟩, ⟨.count 3, 2080504264845545672244111000⟩, ⟨.count 4, 222384723650993891660793120⟩, ⟨.count 5, 22550195658019064469033600⟩, ⟨.count 6, 2295834399572076699336000⟩, ⟨.count 7, 401771019925113422383800⟩, ⟨.count 8, 129865380177814439558400⟩, ⟨.count 9, 58439421080016497801280⟩, ⟨.count 10, 32466345044453609889600⟩, ⟨.path 6, 663470173954844653597200⟩, ⟨.path 7, 25831651713283375759800⟩, ⟨.privateRow 2 34, 1267453644190424476480094400⟩, ⟨.privateRow 3 30, 82262616329666973233083050⟩, ⟨.privateRow 3 31, 247803436844922734183608200⟩, ⟨.privateRow 3 32, 389115232797472349578710300⟩, ⟨.privateRow 4 27, 20447168832559198285095540⟩, ⟨.privateRow 4 28, 54946204684958511645208488⟩, ⟨.privateRow 4 29, 93753267499525217113259730⟩, ⟨.privateRow 4 30, 139125863995994090885910240⟩, ⟨.privateRow 4 31, 216639398066064769720704780⟩, ⟨.privateRow 5 24, 3328641013490681758940070⟩, ⟨.privateRow 5 25, 11521444504265202686699520⟩, ⟨.privateRow 5 26, 21378469805200426805446560⟩, ⟨.privateRow 5 27, 33739072150689112045286448⟩, ⟨.privateRow 5 28, 49038385043081899387622700⟩, ⟨.privateRow 5 29, 78428254016492775690094800⟩, ⟨.privateRow 5 30, 82623253649933086947937080⟩, ⟨.privateRow 6 21, 346926087046447145677440⟩, ⟨.privateRow 6 22, 2061999414430476294774000⟩, ⟨.privateRow 6 23, 4857921816316748404775550⟩, ⟨.privateRow 6 24, 8281402655599276665462000⟩, ⟨.privateRow 6 25, 12763138643546989354456800⟩, ⟨.privateRow 6 26, 18109031558402413876206960⟩, ⟨.privateRow 6 27, 28586326933560649457704500⟩, ⟨.privateRow 6 28, 32060902235505611832764400⟩, ⟨.privateRow 6 29, 24948067142016566799451200⟩, ⟨.privateRow 7 19, 266108078132217981059400⟩, ⟨.privateRow 7 20, 1009529404034054837513580⟩, ⟨.privateRow 7 21, 2067668141342999940945200⟩, ⟨.privateRow 7 22, 3447737422968483237718125⟩, ⟨.privateRow 7 23, 5199336078713429255202600⟩, ⟨.privateRow 7 24, 7259513402350594377993000⟩, ⟨.privateRow 7 25, 11277648756120167875293840⟩, ⟨.privateRow 7 26, 12965087039805644249305800⟩, ⟨.privateRow 7 27, 5739585998930191748340000⟩, ⟨.privateRow 8 17, 155229712243793822284650⟩, ⟨.privateRow 8 18, 492898147493068441051200⟩, ⟨.privateRow 8 19, 962627130568049533226640⟩, ⟨.privateRow 8 20, 1582734320917113482118000⟩, ⟨.privateRow 8 21, 2354824589005525892305050⟩, ⟨.privateRow 8 22, 3244315479799328588253600⟩, ⟨.privateRow 8 23, 4984936728700481351799000⟩, ⟨.privateRow 8 24, 3431692671198746565330720⟩, ⟨.privateRow 9 15, 86909908272845048012160⟩, ⟨.privateRow 9 16, 261083524732481112862200⟩, ⟨.privateRow 9 17, 506179834102163099642400⟩, ⟨.privateRow 9 18, 826268481381344371690320⟩, ⟨.privateRow 9 19, 1221456048005776923179840⟩, ⟨.privateRow 9 20, 1673234257728527919685260⟩, ⟨.privateRow 9 21, 1254128528574322302021120⟩, ⟨.privateRow 10 13, 50786639748109575470160⟩, ⟨.privateRow 10 14, 156088197329103893700000⟩, ⟨.privateRow 10 15, 307889172171568400453040⟩, ⟨.privateRow 10 16, 505589536919536670371680⟩, ⟨.privateRow 10 17, 748024589824211171856384⟩, ⟨.privateRow 10 18, 124815059837566100242240⟩, ⟨.privateRow 11 11, 32195792169083163140520⟩, ⟨.privateRow 11 12, 107254889878998532671000⟩, ⟨.privateRow 11 13, 221020887418011113479200⟩, ⟨.privateRow 11 14, 238762912514419256063100⟩, ⟨.privateRow 12 9, 23117776940135494541925⟩, ⟨.privateRow 12 10, 85456058206293966030840⟩, ⟨.privateRow 12 11, 72428109034119086348100⟩, ⟨.privateRow 13 7, 19507089669566664765600⟩, ⟨.privateRow 13 8, 31886588882945509713000⟩, ⟨.privateRow 14 5, 12896353725991295039480⟩, ⟨.hall 5 30, 4781754012872164050122400⟩, ⟨.hall 4 31, 42654689948716208343080100⟩, ⟨.hall 3 32, 134163112603073986167535800⟩, ⟨.hall 2 33, 342739565494286299931592000⟩, ⟨.assumptionRow 18, 256711960406879309376⟩]
  caps := #[0, 0, 0, 289847856335635898938440, 513608154340678923385134, 0, 94517558181922445019450, 16016487685308618723072, 7260195353734223252352, 8212822714634439954880, 0, 6696268036482199934715, 68220492992703020492523, 796804026485256117504, 256711960406879309376, 783336563831520687098880, 174900591115978581406080, 30345844614299862671232, 3654032897011559730624] }

theorem case_54_36_18_checked :
    (Witness.linear .conditional case_54_36_18).check 54 36 18 = true := by
  change case_54_36_18.check 54 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_19 : Certificate := {
  objectiveScale := 4845335495000000
  eta := 3147550542856736184168000
  rows := #[⟨.count 2, 370782854040029663232000⟩, ⟨.count 3, 41429431851966205047000⟩, ⟨.count 4, 4296832553328468753600⟩, ⟨.count 5, 399451394403863802000⟩, ⟨.count 6, 41116745633159196000⟩, ⟨.count 7, 8510724230519511000⟩, ⟨.count 8, 2813462555543640000⟩, ⟨.count 9, 1012846519995710400⟩, ⟨.count 10, 562692511108728000⟩, ⟨.path 6, 15351060362942304000⟩, ⟨.privateRow 2 34, 28162760180991836400000⟩, ⟨.privateRow 3 30, 1249722483031512740250⟩, ⟨.privateRow 3 31, 5143056442576366314000⟩, ⟨.privateRow 3 32, 8629874369746784154000⟩, ⟨.privateRow 4 27, 271904744128385468100⟩, ⟨.privateRow 4 28, 1002996587588752116360⟩, ⟨.privateRow 4 29, 1950774048965488096350⟩, ⟨.privateRow 4 30, 3113996625726811624800⟩, ⟨.privateRow 4 31, 5170883931802822533300⟩, ⟨.privateRow 5 24, 34341324914576780100⟩, ⟨.privateRow 5 25, 177926242892738511600⟩, ⟨.privateRow 5 26, 399259811001272020800⟩, ⟨.privateRow 5 27, 696942101948381649360⟩, ⟨.privateRow 5 28, 1105532024655873414600⟩, ⟨.privateRow 5 29, 1913918191891894188000⟩, ⟨.privateRow 5 30, 2232617182103322214200⟩, ⟨.privateRow 6 21, 1171606192772815800⟩, ⟨.privateRow 6 22, 24684784564710270000⟩, ⟨.privateRow 6 23, 77066265840645831750⟩, ⟨.privateRow 6 24, 152656181559670932000⟩, ⟨.privateRow 6 25, 261916617120187029000⟩, ⟨.privateRow 6 26, 408514763064936528000⟩, ⟨.privateRow 6 27, 707163813335893914000⟩, ⟨.privateRow 6 28, 893662887166585536000⟩, ⟨.privateRow 6 29, 834272032363133364000⟩, ⟨.privateRow 7 19, 783750283330014000⟩, ⟨.privateRow 7 20, 12335023689947758800⟩, ⟨.privateRow 7 21, 32213029807579621000⟩, ⟨.privateRow 7 22, 62020521218834553375⟩, ⟨.privateRow 7 23, 104955072282492003000⟩, ⟨.privateRow 7 24, 162422198139589888500⟩, ⟨.privateRow 7 25, 279394918310483375400⟩, ⟨.privateRow 7 26, 365049278601926168250⟩, ⟨.privateRow 7 27, 374398180218784722000⟩, ⟨.privateRow 7 28, 74551733681628703500⟩, ⟨.privateRow 8 17, 293069016202462500⟩, ⟨.privateRow 8 18, 5754809772702900000⟩, ⟨.privateRow 8 19, 14369760002439141300⟩, ⟨.privateRow 8 20, 27462520611612086000⟩, ⟨.privateRow 8 21, 46114409699457474375⟩, ⟨.privateRow 8 22, 70869112158033189000⟩, ⟨.privateRow 8 23, 121494691356892854000⟩, ⟨.privateRow 8 24, 164151472803193675800⟩, ⟨.privateRow 8 25, 102251779753039166250⟩, ⟨.privateRow 9 15, 73582866837295200⟩, ⟨.privateRow 9 16, 2710302261840373200⟩, ⟨.privateRow 9 17, 7079694867040723200⟩, ⟨.privateRow 9 18, 13594651068386868480⟩, ⟨.privateRow 9 19, 22801550977928122400⟩, ⟨.privateRow 9 20, 34943204939852008800⟩, ⟨.privateRow 9 21, 59669521570858399200⟩, ⟨.privateRow 9 22, 62074362183811177200⟩, ⟨.privateRow 10 14, 1328820007002919200⟩, ⟨.privateRow 10 15, 3896645639427941400⟩, ⟨.privateRow 10 16, 7724233561583448000⟩, ⟨.privateRow 10 17, 13054466257722489600⟩, ⟨.privateRow 10 18, 20075618368556951200⟩, ⟨.privateRow 10 19, 26221471017666724800⟩, ⟨.privateRow 11 12, 668197356941614500⟩, ⟨.privateRow 11 13, 2396853677126601000⟩, ⟨.privateRow 11 14, 5116985022894995250⟩, ⟨.privateRow 11 15, 8881589749204809000⟩, ⟨.privateRow 11 16, 7821425904411319200⟩, ⟨.privateRow 12 10, 375798212776186200⟩, ⟨.privateRow 12 11, 1642143450786696000⟩, ⟨.privateRow 12 12, 3953533233957615000⟩, ⟨.privateRow 12 13, 2311895867814282750⟩, ⟨.privateRow 13 8, 248689993748946750⟩, ⟨.privateRow 13 9, 1267397894068706400⟩, ⟨.privateRow 13 10, 1105288861106430000⟩, ⟨.privateRow 14 6, 202853014508944800⟩, ⟨.privateRow 14 7, 574750207775343600⟩, ⟨.privateRow 15 4, 223513969690411400⟩, ⟨.hall 5 30, 294605832308071284000⟩, ⟨.hall 4 31, 1296241327973329612875⟩, ⟨.hall 3 32, 3476455006757498766000⟩, ⟨.hall 2 33, 8055969382865227824000⟩, ⟨.assumptionRow 19, 4333809827400768⟩]
  caps := #[0, 342061067154566760000, 0, 11766356453186559510, 1605149915179031936, 989657705259069990, 73118123428580516, 0, 0, 0, 0, 1314028705216442500, 66145924739172564, 1735461047360976936, 682006968369334608, 0, 13834848672944270400, 3207838631245083264, 580445524759186944] }

theorem case_54_36_19_checked :
    (Witness.linear .conditional case_54_36_19).check 54 36 19 = true := by
  change case_54_36_19.check 54 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_20 : Certificate := {
  objectiveScale := 3192221032000000
  eta := 2216006901098614784160000
  rows := #[⟨.count 2, 260449206153812503027200⟩, ⟨.count 3, 28738085138974955343600⟩, ⟨.count 4, 2867773636715854426560⟩, ⟨.count 5, 240245586850093624800⟩, ⟨.count 6, 16446698253263678400⟩, ⟨.count 7, 2166366167768602800⟩, ⟨.count 8, 675231013330473600⟩, ⟨.count 9, 202569303999142080⟩, ⟨.path 6, 10844754956826991200⟩, ⟨.privateRow 2 34, 20856535539751668556800⟩, ⟨.privateRow 3 30, 752348021977924772400⟩, ⟨.privateRow 3 31, 3641042566256801706000⟩, ⟨.privateRow 3 32, 6352714046540872810800⟩, ⟨.privateRow 4 27, 159588974358953739600⟩, ⟨.privateRow 4 28, 657399287653438009680⟩, ⟨.privateRow 4 29, 1368307819650760508520⟩, ⟨.privateRow 4 30, 2284938609351137659920⟩, ⟨.privateRow 4 31, 3963707332901879603040⟩, ⟨.privateRow 5 24, 20633532459134835240⟩, ⟨.privateRow 5 25, 107855981847670193280⟩, ⟨.privateRow 5 26, 260515110844304075760⟩, ⟨.privateRow 5 27, 480675093766675359552⟩, ⟨.privateRow 5 28, 804535340843925971280⟩, ⟨.privateRow 5 29, 1471820332071099890880⟩, ⟨.privateRow 5 30, 1836326913842222802000⟩, ⟨.privateRow 6 21, 1290977389772310240⟩, ⟨.privateRow 6 22, 14167347001915307200⟩, ⟨.privateRow 6 23, 46090545508138131000⟩, ⟨.privateRow 6 24, 97379106631651072800⟩, ⟨.privateRow 6 25, 177140961473323848000⟩, ⟨.privateRow 6 26, 293352506048535373440⟩, ⟨.privateRow 6 27, 541591541942150700000⟩, ⟨.privateRow 6 28, 741516191139081758400⟩, ⟨.privateRow 6 29, 768308393132301621600⟩, ⟨.privateRow 7 19, 876192624440733600⟩, ⟨.privateRow 7 20, 6808579384415608800⟩, ⟨.privateRow 7 21, 18755523874241554400⟩, ⟨.privateRow 7 22, 38403261479142910350⟩, ⟨.privateRow 7 23, 69235294259706775200⟩, ⟨.privateRow 7 24, 114382659939700752600⟩, ⟨.privateRow 7 25, 211428495663326781840⟩, ⟨.privateRow 7 26, 301467536866778782500⟩, ⟨.privateRow 7 27, 347311234529269810800⟩, ⟨.privateRow 7 28, 221323041547951543200⟩, ⟨.privateRow 8 17, 405607518424208100⟩, ⟨.privateRow 8 18, 3094808811098004000⟩, ⟨.privateRow 8 19, 8083077922076877720⟩, ⟨.privateRow 8 20, 16427495254868698000⟩, ⟨.privateRow 8 21, 29460469784736340350⟩, ⟨.privateRow 8 22, 48532229083127790000⟩, ⟨.privateRow 8 23, 89890128649619298000⟩, ⟨.privateRow 8 24, 133043017326547648320⟩, ⟨.privateRow 8 25, 163462174477085484000⟩, ⟨.privateRow 8 26, 25958881179149318400⟩, ⟨.privateRow 9 15, 173136157264224000⟩, ⟨.privateRow 9 16, 1451746678660518240⟩, ⟨.privateRow 9 17, 3844724466811999680⟩, ⟨.privateRow 9 18, 7825927444500189024⟩, ⟨.privateRow 9 19, 14019796521224574080⟩, ⟨.privateRow 9 20, 23039444867346867960⟩, ⟨.privateRow 9 21, 42613507712708412480⟩, ⟨.privateRow 9 22, 65418631341500717280⟩, ⟨.privateRow 9 23, 45172954791808683840⟩, ⟨.privateRow 10 13, 77169258666339840⟩, ⟨.privateRow 10 14, 730634583655025280⟩, ⟨.privateRow 10 15, 2065081515769031760⟩, ⟨.privateRow 10 16, 4274416929840482880⟩, ⟨.privateRow 10 17, 7681878161656354656⟩, ⟨.privateRow 10 18, 12629320804884784000⟩, ⟨.privateRow 10 19, 23258894946679271880⟩, ⟨.privateRow 10 20, 26401532621221517760⟩, ⟨.privateRow 11 11, 39388475777610960⟩, ⟨.privateRow 11 12, 407952070553827800⟩, ⟨.privateRow 11 13, 1268222351960440800⟩, ⟨.privateRow 11 14, 2740781439525429300⟩, ⟨.privateRow 11 15, 4995174882706117200⟩, ⟨.privateRow 11 16, 8251885675409496120⟩, ⟨.privateRow 11 17, 10600501695387203600⟩, ⟨.privateRow 12 9, 24868999374894675⟩, ⟨.privateRow 12 10, 259374452739642240⟩, ⟨.privateRow 12 11, 900020929758093000⟩, ⟨.privateRow 12 12, 2088145725290301600⟩, ⟨.privateRow 12 13, 3945881234149955100⟩, ⟨.privateRow 12 14, 2809443323321434800⟩, ⟨.privateRow 13 7, 20805437385532800⟩, ⟨.privateRow 13 8, 193425550693625250⟩, ⟨.privateRow 13 9, 754543862515322880⟩, ⟨.privateRow 13 10, 1907412777452239200⟩, ⟨.privateRow 13 11, 544142208544704000⟩, ⟨.privateRow 14 5, 12772226839452080⟩, ⟨.privateRow 14 6, 175805945907752160⟩, ⟨.privateRow 14 7, 761544025302330270⟩, ⟨.privateRow 14 8, 153266722073424960⟩, ⟨.privateRow 15 3, 42350015309762160⟩, ⟨.privateRow 15 4, 223513969690411400⟩, ⟨.privateRow 15 5, 94664740104174240⟩, ⟨.hall 5 30, 332687668655508566400⟩, ⟨.hall 4 31, 1146324920652728426610⟩, ⟨.hall 3 32, 2814081517305859600800⟩, ⟨.hall 2 33, 6170247759990076963200⟩, ⟨.assumptionRow 20, 1953406695480240⟩]
  caps := #[0, 222509464566060672000, 14263127572000507200, 9888162350963496600, 1430511779917702482, 387839986082508960, 432639594263419400, 55698704927605740, 21018221851529140, 12996398498410488, 87147246555457760, 16779861790016325, 10969253275085105, 0, 4185009646907199110, 0, 26788512173333710800, 7720967997030768480, 1852732640326167600] }

theorem case_54_36_20_checked :
    (Witness.linear .conditional case_54_36_20).check 54 36 20 = true := by
  change case_54_36_20.check 54 36 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_21 : Certificate := {
  objectiveScale := 133986093048808000000
  eta := 152664824604789066455357472000
  rows := #[⟨.count 2, 17899549424077015055596435200⟩, ⟨.count 3, 1959877299101362808999832000⟩, ⟨.count 4, 192207255932174261268409920⟩, ⟨.count 5, 15870410809740307977156000⟩, ⟨.count 6, 896468670309096615931200⟩, ⟨.count 7, 12754635553178203885200⟩, ⟨.path 6, 707362030076136254820000⟩, ⟨.path 7, 11384704365632894696400⟩, ⟨.privateRow 2 34, 1421988808552731594753177600⟩, ⟨.privateRow 3 30, 55795153227378052895807400⟩, ⟨.privateRow 3 31, 247167830839856020356662400⟩, ⟨.privateRow 3 32, 430692156041944999693491000⟩, ⟨.privateRow 4 27, 12944254468402119849626640⟩, ⟨.privateRow 4 28, 45325893272618319582757536⟩, ⟨.privateRow 4 29, 92082729107947701859395660⟩, ⟨.privateRow 4 30, 153695059033871113910511360⟩, ⟨.privateRow 4 31, 268330747304207735516449080⟩, ⟨.privateRow 5 24, 2052494174125369680926220⟩, ⟨.privateRow 5 25, 7907457565074872426656320⟩, ⟨.privateRow 5 26, 17643791042510294629727760⟩, ⟨.privateRow 5 27, 32051597425187769447834816⟩, ⟨.privateRow 5 28, 53568558277951800731848200⟩, ⟨.privateRow 5 29, 98942931312944152897182720⟩, ⟨.privateRow 5 30, 125343083344510169689430880⟩, ⟨.privateRow 6 20, 27497006517241322661600⟩, ⟨.privateRow 6 21, 221566240466638513205760⟩, ⟨.privateRow 6 22, 1230923558147991740032000⟩, ⟨.privateRow 6 23, 3282952086848404121451300⟩, ⟨.privateRow 6 24, 6544950129573729765091200⟩, ⟨.privateRow 6 25, 11678994621526842024214800⟩, ⟨.privateRow 6 26, 19315620081733071963746880⟩, ⟨.privateRow 6 27, 36058265754231437969452200⟩, ⟨.privateRow 6 28, 50396601888595935503731200⟩, ⟨.privateRow 6 29, 53779009764579241095954000⟩, ⟨.privateRow 7 17, 6587559021971160248400⟩, ⟨.privateRow 7 18, 26268475603569396096900⟩, ⟨.privateRow 7 19, 148914511198794873932400⟩, ⟨.privateRow 7 20, 572318718179039120048760⟩, ⟨.privateRow 7 21, 1332758188040827240893200⟩, ⟨.privateRow 7 22, 2568009211822933014386250⟩, ⟨.privateRow 7 23, 4521127855574535169021200⟩, ⟨.privateRow 7 24, 7442329845279481967014200⟩, ⟨.privateRow 7 25, 13920044824580029485910560⟩, ⟨.privateRow 7 26, 20314490254626256445156400⟩, ⟨.privateRow 7 27, 24257494731351632617666800⟩, ⟨.privateRow 7 28, 18221818978508375421991800⟩, ⟨.privateRow 8 14, 695707393809720211920⟩, ⟨.privateRow 8 15, 3809826204196086874800⟩, ⟨.privateRow 8 16, 18106230890176051669200⟩, ⟨.privateRow 8 17, 81745618772642124900600⟩, ⟨.privateRow 8 18, 264790450492426844294400⟩, ⟨.privateRow 8 19, 582307088618735817377040⟩, ⟨.privateRow 8 20, 1100377194542374135186800⟩, ⟨.privateRow 8 21, 1912905454895976532691700⟩, ⟨.privateRow 8 22, 3125713933616528666412000⟩, ⟨.privateRow 8 23, 5846067880593846147442200⟩, ⟨.privateRow 8 24, 8860993172489803099154400⟩, ⟨.privateRow 8 25, 11295679172743069790786100⟩, ⟨.privateRow 8 26, 4077618335940304575420000⟩, ⟨.privateRow 9 11, 54565285788997663680⟩, ⟨.privateRow 9 12, 463804929206480141280⟩, ⟨.privateRow 9 13, 2782829575238880847680⟩, ⟨.privateRow 9 14, 11661381077191500695040⟩, ⟨.privateRow 9 15, 45952365293688186305280⟩, ⟨.privateRow 9 16, 133498518789931867331760⟩, ⟨.privateRow 9 17, 286125477235924930793280⟩, ⟨.privateRow 9 18, 531798731828150129991648⟩, ⟨.privateRow 9 19, 912252761868123495659840⟩, ⟨.privateRow 9 20, 1475595382270416569482320⟩, ⟨.privateRow 9 21, 2636267217609633123035520⟩, ⟨.privateRow 9 22, 4504473472453335132111360⟩, ⟨.privateRow 9 23, 4191683428196484924832128⟩, ⟨.privateRow 10 9, 51533881022942237920⟩, ⟨.privateRow 10 10, 381957000522983645760⟩, ⟨.privateRow 10 11, 2145097797579970653420⟩, ⟨.privateRow 10 12, 8162966754034050486528⟩, ⟨.privateRow 10 13, 28822163457831265922400⟩, ⟨.privateRow 10 14, 77491100479728835912320⟩, ⟨.privateRow 10 15, 163568538366818663158080⟩, ⟨.privateRow 10 16, 300208281450012600537600⟩, ⟨.privateRow 10 17, 507866397481095754701600⟩, ⟨.privateRow 10 18, 712507439023199381481920⟩, ⟨.privateRow 10 19, 1684423551645634253093640⟩, ⟨.privateRow 10 20, 2201350709708013744840960⟩, ⟨.privateRow 11 7, 61026964369273702800⟩, ⟨.privateRow 11 8, 386504107672066784400⟩, ⟨.privateRow 11 9, 1909785002614918228800⟩, ⟨.privateRow 11 10, 6667195857343152030900⟩, ⟨.privateRow 11 11, 21180425100429259785120⟩, ⟨.privateRow 11 12, 53834500711466444970000⟩, ⟨.privateRow 11 13, 112115922310104911074800⟩, ⟨.privateRow 11 14, 204460672958523328947600⟩, ⟨.privateRow 11 15, 342266955712145686076400⟩, ⟨.privateRow 11 16, 540332742525549364591200⟩, ⟨.privateRow 11 17, 858039119031988261368000⟩, ⟨.privateRow 12 5, 91104539665558599180⟩, ⟨.privateRow 12 6, 479497577187150522000⟩, ⟨.privateRow 12 7, 2024545325901302204000⟩, ⟨.privateRow 12 8, 6538090493645970058800⟩, ⟨.privateRow 12 9, 19018072655185357578825⟩, ⟨.privateRow 12 10, 46038160710995612118960⟩, ⟨.privateRow 12 11, 94748721252180943147200⟩, ⟨.privateRow 12 12, 172537982043542516293200⟩, ⟨.privateRow 12 13, 287586663544279978078200⟩, ⟨.privateRow 12 14, 148583221963647388117200⟩, ⟨.privateRow 13 3, 173532456505825903200⟩, ⟨.privateRow 13 4, 546627237993351595080⟩, ⟨.privateRow 13 5, 2685186432248042923200⟩, ⟨.privateRow 13 6, 7895726771015078595600⟩, ⟨.privateRow 13 7, 21221998651506591338400⟩, ⟨.privateRow 13 8, 49651974117729436553100⟩, ⟨.privateRow 13 9, 101308248108101162288160⟩, ⟨.privateRow 13 10, 90063344926523643760800⟩, ⟨.privateRow 14 2, 1804737547660589393280⟩, ⟨.privateRow 14 3, 3789948850087237725888⟩, ⟨.privateRow 14 4, 11968259526591277029120⟩, ⟨.privateRow 14 5, 31056525299325975809360⟩, ⟨.privateRow 14 6, 44030288111307614756640⟩, ⟨.privateRow 15 0, 3014732039842120918320⟩, ⟨.privateRow 15 1, 9474872125218094314720⟩, ⟨.privateRow 15 2, 18239128841044831555836⟩, ⟨.privateRow 16 0, 7895726771015078595600⟩, ⟨.hall 5 30, 24332082899632660915963200⟩, ⟨.hall 4 31, 79758881370578091810418290⟩, ⟨.hall 3 32, 192596156365313894866873200⟩, ⟨.hall 2 33, 420104683123787692391961600⟩, ⟨.assumptionRow 21, 5791315457347740320⟩]
  caps := #[0, 0, 0, 473264575294391481400800, 0, 44686168060269486021414, 1766313626269444151900, 1627406222545046723780, 2943674948064559315320, 0, 85198428688084071360, 9789918823209457647400, 221253882044928026580, 38107009339517304483440, 82616397793976899705424, 0, 519722654987369054741520, 1021824839279849734889760, 296825150653303600167840] }

theorem case_54_36_21_checked :
    (Witness.linear .conditional case_54_36_21).check 54 36 21 = true := by
  change case_54_36_21.check 54 36 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_22 : Certificate := {
  objectiveScale := 1205874837439272000000
  eta := 1139912390512863708909648480000
  rows := #[⟨.count 2, 145568145383000713813632192000⟩, ⟨.count 3, 17631434230113656031725646000⟩, ⟨.count 4, 1967836191686546008224196800⟩, ⟨.count 5, 192576775945057766946684000⟩, ⟨.count 6, 15086911768616504024208000⟩, ⟨.count 7, 765278133190692233112000⟩, ⟨.path 6, 2280420523182280503024000⟩, ⟨.path 7, 716191792657250123214000⟩, ⟨.privateRow 2 34, 14962718060144414541805824000⟩, ⟨.privateRow 3 33, 25938528365898620222156406000⟩, ⟨.privateRow 4 28, 291096496303075511631142560⟩, ⟨.privateRow 5 24, 195419237582623195241100⟩, ⟨.privateRow 5 25, 32140119801900521357575200⟩, ⟨.privateRow 5 26, 122960153005017818969278800⟩, ⟨.privateRow 5 27, 207698671856905845472977120⟩, ⟨.privateRow 6 22, 3146143436450623625016000⟩, ⟨.privateRow 6 23, 16262160330302209953630000⟩, ⟨.privateRow 6 24, 44073773303349662894736000⟩, ⟨.privateRow 6 25, 87888549415364380628946000⟩, ⟨.privateRow 6 26, 161386225745157124931419200⟩, ⟨.privateRow 6 27, 221438694111106731166908000⟩, ⟨.privateRow 6 28, 380926301249633614891416000⟩, ⟨.privateRow 6 29, 496118881202765907694608000⟩, ⟨.privateRow 7 18, 6832840474916894938500⟩, ⟨.privateRow 7 19, 226104902988159068874000⟩, ⟨.privateRow 7 21, 10322144344107789287094000⟩, ⟨.privateRow 7 22, 14458290444924149689866000⟩, ⟨.privateRow 7 24, 128821819087099859240520000⟩, ⟨.privateRow 7 25, 99611881579528461171428400⟩, ⟨.privateRow 7 29, 3188749992834216529899180000⟩, ⟨.privateRow 8 15, 1242334631803071807000⟩, ⟨.privateRow 8 16, 13378988342494619460000⟩, ⟨.privateRow 8 17, 150736601992106045916000⟩, ⟨.privateRow 8 18, 203968758639667971222000⟩, ⟨.privateRow 8 19, 3408966229667629038408000⟩, ⟨.privateRow 8 20, 7105878019550947831194000⟩, ⟨.privateRow 8 21, 9381179388402945982608750⟩, ⟨.privateRow 8 22, 9178368259761094510116000⟩, ⟨.privateRow 8 23, 88679502464279003012736000⟩, ⟨.privateRow 8 24, 78246210581779232234642400⟩, ⟨.privateRow 8 25, 59739524272198412447305500⟩, ⟨.privateRow 8 26, 57268313633770135444548000⟩, ⟨.privateRow 9 13, 927609858412960282560⟩, ⟨.privateRow 9 14, 9938677054424574456000⟩, ⟨.privateRow 9 15, 85625525391965564544000⟩, ⟨.privateRow 9 16, 154215138961154646975600⟩, ⟨.privateRow 9 17, 1235829315912902994628800⟩, ⟨.privateRow 9 18, 3243387869940915627971040⟩, ⟨.privateRow 9 19, 5690886481363511333505600⟩, ⟨.privateRow 9 20, 8397188243283322957874400⟩, ⟨.privateRow 9 21, 12105308652289131687408000⟩, ⟨.privateRow 9 22, 63497213833013163741938400⟩, ⟨.privateRow 9 23, 63952206468564720760534080⟩, ⟨.privateRow 9 24, 58724661111478483088167200⟩, ⟨.privateRow 10 11, 869634242262150264900⟩, ⟨.privateRow 10 12, 6493269008890721977920⟩, ⟨.privateRow 10 13, 51681120683007787171200⟩, ⟨.privateRow 10 14, 105961587672557386123200⟩, ⟨.privateRow 10 15, 515982983742209157174000⟩, ⟨.privateRow 10 16, 1521701808641988027163200⟩, ⟨.privateRow 10 17, 3107029220754210466434720⟩, ⟨.privateRow 10 18, 5155964796345370903896000⟩, ⟨.privateRow 10 19, 8952014889846574826880600⟩, ⟨.privateRow 10 20, 12037725648319044581107200⟩, ⟨.privateRow 10 21, 47516814997203890474136000⟩, ⟨.privateRow 10 22, 53655737040180861624118080⟩, ⟨.privateRow 11 9, 1023099108543706194000⟩, ⟨.privateRow 11 10, 5435214014138439155625⟩, ⟨.privateRow 11 11, 34785369690486010596000⟩, ⟨.privateRow 11 12, 79509416435396595648000⟩, ⟨.privateRow 11 13, 267579766849892389200000⟩, ⟨.privateRow 11 14, 798614112477407993266500⟩, ⟨.privateRow 11 15, 1816744989744019371582000⟩, ⟨.privateRow 11 16, 3356788175131900022514000⟩, ⟨.privateRow 11 17, 6357992571205498603380000⟩, ⟨.privateRow 11 18, 10020360556465626427310250⟩, ⟨.privateRow 11 19, 13377459315255477217776000⟩, ⟨.privateRow 11 20, 40777149619672225921161000⟩, ⟨.privateRow 12 7, 1518408994425976653000⟩, ⟨.privateRow 12 8, 4823181511706043486000⟩, ⟨.privateRow 12 9, 27331361899667579754000⟩, ⟨.privateRow 12 10, 71061540939135707360400⟩, ⟨.privateRow 12 11, 185462812890601434045000⟩, ⟨.privateRow 12 12, 502476576463119350862000⟩, ⟨.privateRow 12 13, 1198024696602095579217000⟩, ⟨.privateRow 12 14, 2410129185697959305580000⟩, ⟨.privateRow 12 15, 4968841593359565999277200⟩, ⟨.privateRow 12 16, 8527384912696284883248000⟩, ⟨.privateRow 12 17, 12996062583291934173027000⟩, ⟨.privateRow 12 18, 17269516240318529321706000⟩, ⟨.privateRow 12 19, 42199622773086743140176000⟩, ⟨.privateRow 12 20, 25330706208611912916007200⟩, ⟨.privateRow 13 6, 6073635977703906612000⟩, ⟨.privateRow 13 7, 25723634729098898592000⟩, ⟨.privateRow 13 8, 75161245224085844323500⟩, ⟨.privateRow 13 9, 174920716157872510425600⟩, ⟨.privateRow 13 10, 413874908766394779132000⟩, ⟨.privateRow 13 11, 958700078942185874448000⟩, ⟨.privateRow 13 12, 2013410326608845041878000⟩, ⟨.privateRow 13 13, 4442588643327784781832000⟩, ⟨.privateRow 13 14, 803542039850226844767600⟩, ⟨.privateRow 13 15, 28497500007386729823504000⟩, ⟨.privateRow 13 16, 12230784450101241939915000⟩, ⟨.privateRow 13 17, 25246369434750081527052000⟩, ⟨.privateRow 13 18, 50125717723990341268836000⟩, ⟨.privateRow 14 4, 7480162204119548143200⟩, ⟨.privateRow 14 5, 31582907084060314382400⟩, ⟨.privateRow 14 6, 100322175443485704508800⟩, ⟨.privateRow 14 7, 222067315434799085501250⟩, ⟨.privateRow 14 8, 483218478386122810050720⟩, ⟨.privateRow 14 10, 4165299553509339154509600⟩, ⟨.privateRow 14 11, 3825479620556805579568200⟩, ⟨.privateRow 14 12, 9832333209942231509320800⟩, ⟨.privateRow 14 13, 2657701631123675455278960⟩, ⟨.privateRow 14 14, 4942724958655439200845600⟩, ⟨.privateRow 14 15, 131641504589748897885141000⟩, ⟨.privateRow 14 18, 206362714887250094174601600⟩, ⟨.privateRow 15 2, 24871539328697497576140⟩, ⟨.privateRow 15 3, 52361135428836837002400⟩, ⟨.privateRow 15 4, 165810262191316650507600⟩, ⟨.privateRow 15 5, 380388248556549962929200⟩, ⟨.privateRow 15 6, 808325028182668671224550⟩, ⟨.privateRow 15 7, 1326482097530533204060800⟩, ⟨.privateRow 15 9, 13545422957475252526082400⟩, ⟨.privateRow 15 11, 50918824152933422310424800⟩, ⟨.privateRow 15 13, 12933200450922698739592800⟩, ⟨.privateRow 15 14, 267804299721750305151087450⟩, ⟨.privateRow 15 17, 742365705882962907652626720⟩, ⟨.privateRow 16 1, 248715393286974975761400⟩, ⟨.privateRow 16 2, 392708515716276277518000⟩, ⟨.privateRow 16 3, 967226529449347127961000⟩, ⟨.privateRow 16 4, 1901941242782749814646000⟩, ⟨.privateRow 16 5, 3575283778500265276570125⟩, ⟨.privateRow 16 6, 5803359176696082767766000⟩, ⟨.privateRow 16 9, 207262827739145813134500⟩, ⟨.privateRow 16 11, 248715393286974975761400⟩, ⟨.privateRow 16 12, 820484447410031892261774000⟩, ⟨.privateRow 16 15, 2040709801919629676122287000⟩, ⟨.privateRow 16 17, 2176259691261031037912250000⟩, ⟨.privateRow 17 4, 98242580348355115425753000⟩, ⟨.privateRow 17 11, 3689831034630766529295792000⟩, ⟨.privateRow 17 13, 4900403863162798379573184000⟩, ⟨.privateRow 17 15, 16204305303432993620806732800⟩, ⟨.privateRow 18 3, 1564419823775072597539206000⟩, ⟨.privateRow 18 10, 33223954936148088317709504000⟩, ⟨.privateRow 18 11, 25791786283859304986457180000⟩, ⟨.privateRow 18 12, 34260190117576107232596048000⟩, ⟨.privateRow 18 13, 44085632511427271036960688000⟩, ⟨.hall 16 7, 7956839207323244838600⟩, ⟨.hall 14 8, 258227821782142452240⟩, ⟨.hall 17 8, 268518643224804292320000⟩, ⟨.hall 12 11, 147729752270027284500⟩, ⟨.hall 16 13, 522841337590885475362200⟩, ⟨.hall 9 14, 16268307682730399296⟩, ⟨.hall 10 15, 52548412451011559775⟩, ⟨.hall 7 16, 3273049869854965200⟩, ⟨.hall 8 17, 16978176433275774640⟩, ⟨.hall 11 18, 216854200718394319080⟩, ⟨.hall 13 19, 27565939370517352318800⟩, ⟨.hall 14 19, 346263508576152174047040⟩, ⟨.hall 15 19, 5080900177148203076268600⟩, ⟨.hall 7 23, 1388787077174139300350⟩, ⟨.hall 5 26, 19687665767189141893600⟩, ⟨.hall 3 32, 8369725193912684252508858000⟩]
  caps := #[0, 60388879822969300739136000, 10903183827824980980288000, 1682213492459030785254000, 447573189382432005372480, 98984131512838331760000, 209003386704477657864000, 2014769457274890196650, 16052190692418445976250, 122014288646406644599440, 11049390912759265766700, 15772953407542315018650, 0, 164742592480405451334900, 3919074455226294369295290, 635956790451122701180620, 0, 0, 0] }

theorem case_54_36_22_checked :
    (Witness.linear .conditional case_54_36_22).check 54 36 22 = true := by
  change case_54_36_22.check 54 36 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_36_23 : Certificate := {
  objectiveScale := 7832099969591040000
  eta := 6723158110622428051094918400
  rows := #[⟨.count 2, 788114598663737862951033600⟩, ⟨.count 3, 84881175187009071882211200⟩, ⟨.count 4, 8013921009276275501728320⟩, ⟨.count 5, 604036029862328457794400⟩, ⟨.count 6, 28660228591598618414400⟩, ⟨.path 5, 20327281348423383734400⟩, ⟨.path 6, 28158375559646292760800⟩, ⟨.privateRow 2 34, 90887664306387739911120000⟩, ⟨.privateRow 3 33, 151545301136955209808324000⟩, ⟨.privateRow 4 28, 1236072234566873262791232⟩, ⟨.privateRow 5 25, 119839457994048075872160⟩, ⟨.privateRow 5 26, 508820381541350825506560⟩, ⟨.privateRow 5 27, 955618870421448236779776⟩, ⟨.privateRow 5 30, 19784720316434603233944240⟩, ⟨.privateRow 6 21, 651368831627241327600⟩, ⟨.privateRow 6 22, 8636668211946385010400⟩, ⟨.privateRow 6 23, 56777649823507869055800⟩, ⟨.privateRow 6 24, 174380741495635749703200⟩, ⟨.privateRow 6 25, 386334091469579356303200⟩, ⟨.privateRow 6 26, 799967774415802649136480⟩, ⟨.privateRow 6 27, 1322604412619113515691800⟩, ⟨.privateRow 7 17, 16701764913519008400⟩, ⟨.privateRow 7 18, 72374314625249036400⟩, ⟨.privateRow 7 19, 690845730513740802000⟩, ⟨.privateRow 7 20, 4776704765266436402400⟩, ⟨.privateRow 7 21, 21857043016825208992800⟩, ⟨.privateRow 7 22, 60658722445286848632750⟩, ⟨.privateRow 7 23, 138400367939083371607200⟩, ⟨.privateRow 7 24, 288809702512056279754200⟩, ⟨.privateRow 7 25, 706648333138006541602320⟩, ⟨.privateRow 7 26, 1240911904985863665855300⟩, ⟨.privateRow 7 27, 1686032033509801551974400⟩, ⟨.privateRow 7 28, 2836494138792760234588800⟩, ⟨.privateRow 7 29, 13764074781115236493515600⟩, ⟨.privateRow 8 15, 9869224721624868600⟩, ⟨.privateRow 8 16, 53141979270287754000⟩, ⟨.privateRow 8 17, 391479247291119787800⟩, ⟨.privateRow 8 18, 2185584674716198173600⟩, ⟨.privateRow 8 19, 8428317912267637784400⟩, ⟨.privateRow 8 20, 22490866560058450554000⟩, ⟨.privateRow 8 21, 51036228341702601747750⟩, ⟨.privateRow 8 22, 105877042813591590340800⟩, ⟨.privateRow 8 23, 257247921852299949971400⟩, ⟨.privateRow 8 24, 523882134363179924972640⟩, ⟨.privateRow 8 25, 860724695647069665211800⟩, ⟨.privateRow 8 26, 1102359503989759073058000⟩, ⟨.privateRow 8 27, 955163307008298032845200⟩, ⟨.privateRow 9 14, 31581519109199579520⟩, ⟨.privateRow 9 15, 212567917081151016000⟩, ⟨.privateRow 9 16, 1022451681160336386960⟩, ⟨.privateRow 9 17, 3527081475059243949120⟩, ⟨.privateRow 9 18, 9207591896287137409056⟩, ⟨.privateRow 9 19, 20670104256971124795840⟩, ⟨.privateRow 9 20, 42777167633410830459840⟩, ⟨.privateRow 9 21, 104645363568332806739520⟩, ⟨.privateRow 9 22, 223815594133638320093280⟩, ⟨.privateRow 9 23, 433187906861336032486080⟩, ⟨.privateRow 9 24, 734479546852988671054320⟩, ⟨.privateRow 9 25, 1125433751388918015844800⟩, ⟨.privateRow 9 27, 5691463466264402223196800⟩, ⟨.privateRow 10 12, 22107063376439705664⟩, ⟨.privateRow 10 13, 126326076436798318080⟩, ⟨.privateRow 10 14, 535671151044500560320⟩, ⟨.privateRow 10 15, 1694874858860377434240⟩, ⟨.privateRow 10 16, 4310877358405742604480⟩, ⟨.privateRow 10 17, 9528144315245513141184⟩, ⟨.privateRow 10 18, 19380525560012141965440⟩, ⟨.privateRow 10 19, 46728805211949427847280⟩, ⟨.privateRow 10 20, 101613537733849647105600⟩, ⟨.privateRow 10 21, 202924419242902798240800⟩, ⟨.privateRow 10 22, 368347889978238375773568⟩, ⟨.privateRow 10 23, 595205047581418525371120⟩, ⟨.privateRow 10 24, 850974559570419070026240⟩, ⟨.privateRow 10 25, 654479611259497486182720⟩, ⟨.privateRow 11 10, 17271143262843520050⟩, ⟨.privateRow 11 11, 82901487661648896240⟩, ⟨.privateRow 11 12, 335553640535245532400⟩, ⟨.privateRow 11 13, 988440814427352224400⟩, ⟨.privateRow 11 14, 2417960056798092807000⟩, ⟨.privateRow 11 15, 5225305888976657702400⟩, ⟨.privateRow 11 16, 10417953616147211294160⟩, ⟨.privateRow 11 17, 24302417586738926434800⟩, ⟨.privateRow 11 18, 52780613811249797272800⟩, ⟨.privateRow 11 19, 107732457061257065637600⟩, ⟨.privateRow 11 20, 202279629894423306825600⟩, ⟨.privateRow 11 21, 347550670106852722670160⟩, ⟨.privateRow 11 22, 540724953273104925725400⟩, ⟨.privateRow 12 8, 12771937875043947600⟩, ⟨.privateRow 12 9, 67850919961170971625⟩, ⟨.privateRow 12 10, 246072669725846723760⟩, ⟨.privateRow 12 11, 713403958448883358800⟩, ⟨.privateRow 12 12, 1686878256265419848400⟩, ⟨.privateRow 12 13, 3564434995293515042700⟩, ⟨.privateRow 12 14, 6947934204023907494400⟩, ⟨.privateRow 12 15, 15567715075891067729640⟩, ⟨.privateRow 12 16, 32954437926030061240800⟩, ⟨.privateRow 12 17, 67335252969466072240650⟩, ⟨.privateRow 12 18, 128940011098782961849200⟩, ⟨.privateRow 12 19, 227508658024470345923400⟩, ⟨.privateRow 12 20, 367979965280616200672160⟩, ⟨.privateRow 12 21, 539387673323324756030100⟩, ⟨.privateRow 13 6, 24124771541749678800⟩, ⟨.privateRow 13 7, 76631627250263685600⟩, ⟨.privateRow 13 8, 244263311860215497850⟩, ⟨.privateRow 13 9, 636893968702191520320⟩, ⟨.privateRow 13 10, 1519860607130229764400⟩, ⟨.privateRow 13 11, 3139931803741573579200⟩, ⟨.privateRow 13 12, 6007068113895670021200⟩, ⟨.privateRow 13 13, 12948422834771827603200⟩, ⟨.privateRow 13 14, 26488999152841147322400⟩, ⟨.privateRow 13 15, 53219246021099791432800⟩, ⟨.privateRow 13 16, 102970556133073066538100⟩, ⟨.privateRow 13 17, 186911837113607440005600⟩, ⟨.privateRow 13 18, 314176899788206067012400⟩, ⟨.privateRow 13 19, 485573751683720835014880⟩, ⟨.privateRow 13 20, 681548920825970175778800⟩, ⟨.privateRow 14 5, 62724406008549164880⟩, ⟨.privateRow 14 6, 265656307800914110080⟩, ⟨.privateRow 14 7, 776214524355795915390⟩, ⟨.privateRow 14 8, 1731193605835956950688⟩, ⟨.privateRow 14 9, 3629054919066058825200⟩, ⟨.privateRow 14 10, 6947934204023907494400⟩, ⟨.privateRow 14 11, 14489337787974857087280⟩, ⟨.privateRow 14 12, 28636542452266718729760⟩, ⟨.privateRow 14 13, 56000349684432694404864⟩, ⟨.privateRow 14 14, 107384183086636170274560⟩, ⟨.privateRow 14 15, 198569788321564518718860⟩, ⟨.privateRow 14 16, 347905398241132839375840⟩, ⟨.privateRow 14 17, 571670236361917088716320⟩, ⟨.privateRow 14 19, 3004938118651564841906160⟩, ⟨.privateRow 15 3, 207980925186241967760⟩, ⟨.privateRow 15 4, 439070842059844154160⟩, ⟨.privateRow 15 5, 1162246346628999231600⟩, ⟨.privateRow 15 6, 2716750835245285703865⟩, ⟨.privateRow 15 7, 5795735115189942834912⟩, ⟨.privateRow 15 9, 44379929728202709120480⟩, ⟨.privateRow 15 10, 31942403759853662215140⟩, ⟨.privateRow 15 11, 80110470910373383399920⟩, ⟨.privateRow 15 12, 145815426648074243596536⟩, ⟨.privateRow 15 14, 948886973546580697659030⟩, ⟨.privateRow 15 15, 436373692601476540070160⟩, ⟨.privateRow 15 16, 1026767164156945554503160⟩, ⟨.privateRow 15 18, 2287998157973847887327760⟩, ⟨.privateRow 16 2, 1039904625931209838800⟩, ⟨.privateRow 16 3, 3293031315448831156200⟩, ⟨.privateRow 16 4, 6973478079773995389600⟩, ⟨.privateRow 16 5, 13583754176226428519325⟩, ⟨.privateRow 16 6, 25027037997411116787120⟩, ⟨.privateRow 16 9, 14818640919519740202900⟩, ⟨.privateRow 16 10, 1147771096675528968442800⟩, ⟨.privateRow 16 12, 373210215750867531036000⟩, ⟨.privateRow 16 13, 2598201707889127782241800⟩, ⟨.privateRow 16 17, 33781561749531834415877700⟩, ⟨.privateRow 17 3, 158065503141543895497600⟩, ⟨.privateRow 17 4, 29637281839039480405800⟩, ⟨.privateRow 17 6, 282259827038471241960000⟩, ⟨.privateRow 17 11, 175628336823937661664000⟩, ⟨.privateRow 17 16, 214415855011504294242494400⟩, ⟨.privateRow 18 5, 9021024072149540893041600⟩, ⟨.privateRow 18 11, 1343556776703123111729600⟩, ⟨.hall 14 10, 54833779211851359720⟩, ⟨.hall 16 11, 2140980112211314374000⟩, ⟨.hall 17 11, 36369997686414621028800⟩, ⟨.hall 15 13, 190115150100215580240⟩, ⟨.hall 11 14, 290948836489845534⟩, ⟨.hall 12 14, 1495860416819168400⟩, ⟨.hall 17 15, 9012506758070485269600⟩, ⟨.hall 13 16, 13106890160207363520⟩, ⟨.hall 15 18, 6491976021884838565080⟩, ⟨.hall 7 20, 1091867584838990960⟩, ⟨.hall 9 21, 5355927333675799776⟩, ⟨.hall 4 27, 492683115226661927568⟩, ⟨.hall 5 30, 18364188553351375739004000⟩, ⟨.hall 3 32, 51197057227766200606455600⟩]
  caps := #[0, 778843721834764086758400, 0, 14595278003209061730000, 0, 125696010384005009520, 0, 2274118817805883321020, 426671800514933553930, 34167979753772755968, 576766691981150905680, 868771671930602506500, 2617880074010257089000, 0, 11810043620650299840816, 30021186608736659698362, 404355180016262001030075, 0, 0] }

theorem case_54_36_23_checked :
    (Witness.linear .conditional case_54_36_23).check 54 36 23 = true := by
  change case_54_36_23.check 54 36 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_37_1_checked :
    (Witness.rising).check 54 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_37_2_checked :
    (Witness.rising).check 54 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_37_3_checked :
    (Witness.rising).check 54 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_37_4_checked :
    (Witness.rising).check 54 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_37_5_checked :
    (Witness.rising).check 54 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_37_6_checked :
    (Witness.rising).check 54 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_37_7_checked :
    (Witness.rising).check 54 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_37_8_checked :
    (Witness.rising).check 54 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_37_9_checked :
    (Witness.rising).check 54 37 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_37_10_checked :
    (Witness.linear .positive case_54_37_10).check 54 37 10 = true := by
  change case_54_37_10.check 54 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_37_11_checked :
    (Witness.linear .positive case_54_37_11).check 54 37 11 = true := by
  change case_54_37_11.check 54 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_54_37_12_checked :
    (Witness.linear .positive case_54_37_12).check 54 37 12 = true := by
  change case_54_37_12.check 54 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_54_37_13_checked :
    (Witness.linear .positive case_54_37_13).check 54 37 13 = true := by
  change case_54_37_13.check 54 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_54_37_14_checked :
    (Witness.linear .positive case_54_37_14).check 54 37 14 = true := by
  change case_54_37_14.check 54 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_54_37_15_checked :
    (Witness.linear .positive case_54_37_15).check 54 37 15 = true := by
  change case_54_37_15.check 54 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_54_37_16_checked :
    (Witness.linear .positive case_54_37_16).check 54 37 16 = true := by
  change case_54_37_16.check 54 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_54_37_17_checked :
    (Witness.linear .positive case_54_37_17).check 54 37 17 = true := by
  change case_54_37_17.check 54 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_18 : Certificate := {
  objectiveScale := 2564376328800000
  eta := 2965671342082458254044800
  rows := #[⟨.count 2, 326023217956481803758000⟩, ⟨.count 3, 35566169231616196773600⟩, ⟨.count 4, 3569644823979061507680⟩, ⟨.count 5, 324027276741501933600⟩, ⟨.count 6, 26723899112701190400⟩, ⟨.count 7, 4251529404293371200⟩, ⟨.count 8, 1700611761717348480⟩, ⟨.path 6, 13243971853636524000⟩, ⟨.privateRow 2 34, 5699706607630800765000⟩, ⟨.privateRow 2 35, 25762673866491219457800⟩, ⟨.privateRow 3 31, 3060109147563558810720⟩, ⟨.privateRow 3 32, 5637220935191589023280⟩, ⟨.privateRow 3 33, 7716136145263741835640⟩, ⟨.privateRow 4 27, 157885750382806943640⟩, ⟨.privateRow 4 28, 543914859128196415860⟩, ⟨.privateRow 4 29, 1415698555495345561440⟩, ⟨.privateRow 4 30, 2000325604678047697050⟩, ⟨.privateRow 4 31, 2758296111959489741640⟩, ⟨.privateRow 4 32, 4013679110173537224420⟩, ⟨.privateRow 5 24, 45504861544682860320⟩, ⟨.privateRow 5 25, 111989839719163426020⟩, ⟨.privateRow 5 26, 294917315208023851200⟩, ⟨.privateRow 5 27, 513321562123135365600⟩, ⟨.privateRow 5 28, 731032260227941063392⟩, ⟨.privateRow 5 29, 974086122657958390080⟩, ⟨.privateRow 5 30, 1453334713412399737920⟩, ⟨.privateRow 5 31, 1330850175812519281920⟩, ⟨.privateRow 6 21, 7414869734868796200⟩, ⟨.privateRow 6 22, 23940159621794816400⟩, ⟨.privateRow 6 23, 64489964872664331000⟩, ⟨.privateRow 6 24, 125407464065332148700⟩, ⟨.privateRow 6 25, 198560161115650362600⟩, ⟨.privateRow 6 26, 283059910566996462900⟩, ⟨.privateRow 6 27, 369903303551638977120⟩, ⟨.privateRow 6 28, 539349526363109962500⟩, ⟨.privateRow 6 29, 526219555097668231800⟩, ⟨.privateRow 6 30, 112880636356253465700⟩, ⟨.privateRow 7 18, 525601162618686000⟩, ⟨.privateRow 7 19, 4162955875037259300⟩, ⟨.privateRow 7 20, 14797530913644460800⟩, ⟨.privateRow 7 21, 31932022632960570120⟩, ⟨.privateRow 7 22, 55995341638292456400⟩, ⟨.privateRow 7 23, 85656929471321358150⟩, ⟨.privateRow 7 24, 119997248288525150400⟩, ⟨.privateRow 7 25, 155433890483154082800⟩, ⟨.privateRow 7 26, 223296397926922560240⟩, ⟨.privateRow 7 27, 92736485131149159300⟩, ⟨.privateRow 8 16, 227760503801430600⟩, ⟨.privateRow 8 17, 2951542528749821160⟩, ⟨.privateRow 8 18, 8644776455396521440⟩, ⟨.privateRow 8 19, 16948142216205847920⟩, ⟨.privateRow 8 20, 28198268773975784484⟩, ⟨.privateRow 8 21, 42149190122008449480⟩, ⟨.privateRow 8 22, 58152950633100267945⟩, ⟨.privateRow 8 23, 74705445246869236800⟩, ⟨.privateRow 8 24, 33037926412529738700⟩, ⟨.privateRow 9 14, 132269803689127104⟩, ⟨.privateRow 9 15, 2105519324031002880⟩, ⟨.privateRow 9 16, 5537889583028288640⟩, ⟨.privateRow 9 17, 10337515014513326640⟩, ⟨.privateRow 9 18, 16653970737221912640⟩, ⟨.privateRow 9 19, 24460465839367862304⟩, ⟨.privateRow 9 20, 27010333721597145920⟩, ⟨.privateRow 10 12, 93002205718917495⟩, ⟨.privateRow 10 13, 1643924702993436864⟩, ⟨.privateRow 10 14, 4122465118805893860⟩, ⟨.privateRow 10 15, 7538288674535554320⟩, ⟨.privateRow 10 16, 11948569096649495310⟩, ⟨.privateRow 10 17, 2048464167523169760⟩, ⟨.privateRow 11 10, 80386060165210800⟩, ⟨.privateRow 11 11, 1451973211734120075⟩, ⟨.privateRow 11 12, 3704904195169937760⟩, ⟨.privateRow 11 13, 3232030006325062800⟩, ⟨.privateRow 12 8, 92791316363545800⟩, ⟨.privateRow 12 9, 1490119374544000200⟩, ⟨.privateRow 12 10, 904715334544571550⟩, ⟨.privateRow 13 6, 105489075444873120⟩, ⟨.privateRow 13 7, 556747898181274800⟩, ⟨.privateRow 14 4, 217131680290697172⟩, ⟨.hall 4 32, 417682395904650196320⟩, ⟨.hall 3 33, 1916889563413401857280⟩, ⟨.hall 2 34, 5793073230155800548960⟩, ⟨.assumptionRow 18, 2981664466903980⟩]
  caps := #[0, 1411346788364811097800, 36566852702238916200, 2805382533869332560, 13148757583182616824, 287469503914610160, 1072643343612984000, 707450895406886760, 0, 515643569381390044, 706259220929680581, 67927210558590240, 12343946005719900, 10091613293352110520, 0, 10906274511642690180, 2308566904011147780, 379292351024824380] }

theorem case_54_37_18_checked :
    (Witness.linear .conditional case_54_37_18).check 54 37 18 = true := by
  change case_54_37_18.check 54 37 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_19 : Certificate := {
  objectiveScale := 1889540452800000
  eta := 1703933623358569700697600
  rows := #[⟨.count 2, 192928735660960793894400⟩, ⟨.count 3, 21501826526920105285920⟩, ⟨.count 4, 2206057871753483267520⟩, ⟨.count 5, 200429243345258928000⟩, ⟨.count 6, 20042924334525892800⟩, ⟨.count 7, 4251529404293371200⟩, ⟨.count 8, 1700611761717348480⟩, ⟨.count 9, 566870587239116160⟩, ⟨.path 6, 7648526717080048800⟩, ⟨.privateRow 2 34, 7700936927643393033600⟩, ⟨.privateRow 2 35, 20924256257346850808400⟩, ⟨.privateRow 3 31, 2161666506005162956800⟩, ⟨.privateRow 3 32, 4516982303173288428480⟩, ⟨.privateRow 3 33, 6265455263499339507600⟩, ⟨.privateRow 4 27, 51284434963897998720⟩, ⟨.privateRow 4 28, 346204401352389379800⟩, ⟨.privateRow 4 29, 997937202616044202512⟩, ⟨.privateRow 4 30, 1552129627944666951180⟩, ⟨.privateRow 4 31, 2294358088405033450800⟩, ⟨.privateRow 4 32, 3543589022344177847040⟩, ⟨.privateRow 5 24, 10838025751262149440⟩, ⟨.privateRow 5 25, 56231537716308754800⟩, ⟨.privateRow 5 26, 187258178782570484160⟩, ⟨.privateRow 5 27, 363741960145099536000⟩, ⟨.privateRow 5 28, 565566784888466192832⟩, ⟨.privateRow 5 29, 820757751498835310160⟩, ⟨.privateRow 5 30, 1328920116432157529280⟩, ⟨.privateRow 5 31, 1375167308507748756000⟩, ⟨.privateRow 6 21, 438649859173125600⟩, ⟨.privateRow 6 22, 8147077576719321240⟩, ⟨.privateRow 6 23, 33446114475926952800⟩, ⟨.privateRow 6 24, 79568553781740523500⟩, ⟨.privateRow 6 25, 140167911318304755600⟩, ⟨.privateRow 6 26, 219111228373119482400⟩, ⟨.privateRow 6 27, 313931581521148150560⟩, ⟨.privateRow 6 28, 503810452195871921100⟩, ⟨.privateRow 6 29, 567820995267324598800⟩, ⟨.privateRow 6 30, 414591601512322634400⟩, ⟨.privateRow 7 19, 75920167933810200⟩, ⟨.privateRow 7 20, 5282203199273582400⟩, ⟨.privateRow 7 21, 16631578122033354480⟩, ⟨.privateRow 7 22, 34844545223547259200⟩, ⟨.privateRow 7 23, 59660598634652515500⟩, ⟨.privateRow 7 24, 92159853379461410400⟩, ⟨.privateRow 7 25, 131392503970780852800⟩, ⟨.privateRow 7 26, 209418191228622055680⟩, ⟨.privateRow 7 27, 246183797886701875200⟩, ⟨.privateRow 7 28, 52334302429039831200⟩, ⟨.privateRow 8 18, 3046929406410249360⟩, ⟨.privateRow 8 19, 8561034209554379280⟩, ⟨.privateRow 8 20, 16949430558449573184⟩, ⟨.privateRow 8 21, 28579725439972106400⟩, ⟨.privateRow 8 22, 43649035217411944320⟩, ⟨.privateRow 8 23, 61809139387179344160⟩, ⟨.privateRow 8 24, 98328427278185023920⟩, ⟨.privateRow 8 25, 50933322263434586976⟩, ⟨.privateRow 9 16, 1768442430275875200⟩, ⟨.privateRow 9 17, 4918127224472702240⟩, ⟨.privateRow 9 18, 9522280672511617920⟩, ⟨.privateRow 9 19, 15878675004775687104⟩, ⟨.privateRow 9 20, 24081502354195045760⟩, ⟨.privateRow 9 21, 33964996018743709920⟩, ⟨.privateRow 9 22, 20587300057192028160⟩, ⟨.privateRow 10 14, 1118557140891470280⟩, ⟨.privateRow 10 15, 3259505876624917920⟩, ⟨.privateRow 10 16, 6365484302539241880⟩, ⟨.privateRow 10 17, 10583731532203043760⟩, ⟨.privateRow 10 18, 16014094089505031520⟩, ⟨.privateRow 10 19, 425152940429337120⟩, ⟨.privateRow 11 12, 796318205883520320⟩, ⟨.privateRow 11 13, 2552363741012857200⟩, ⟨.privateRow 11 14, 5178144787280388000⟩, ⟨.privateRow 11 15, 4234658255863635600⟩, ⟨.privateRow 12 10, 661138129090263825⟩, ⟨.privateRow 12 11, 2375457698906772480⟩, ⟨.privateRow 12 12, 1113495796362549600⟩, ⟨.privateRow 13 8, 654997527272088000⟩, ⟨.privateRow 13 9, 640260082908466020⟩, ⟨.privateRow 14 6, 402095704242031800⟩, ⟨.hall 4 32, 541644846106975490880⟩, ⟨.hall 3 33, 1865629456929088250400⟩, ⟨.hall 2 34, 4988238468544949698080⟩, ⟨.assumptionRow 19, 1798533886124976⟩]
  caps := #[0, 0, 0, 0, 0, 3551733833816570688, 0, 272493056731743120, 31502510043164160, 351048867204305312, 713620746298671120, 74146386526602390, 301135689959459355, 587770705301667888, 1798533886124976, 25550636679431463600, 6781452855324026880, 1489312669518754080] }

theorem case_54_37_19_checked :
    (Witness.linear .conditional case_54_37_19).check 54 37 19 = true := by
  change case_54_37_19.check 54 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_20 : Certificate := {
  objectiveScale := 8283439964800000
  eta := 6867614489578402713753600
  rows := #[⟨.count 2, 785191582267219113386400⟩, ⟨.count 3, 87000321658876542876960⟩, ⟨.count 4, 8720008280474398427520⟩, ⟨.count 5, 734907225599282736000⟩, ⟨.count 6, 60128773003577678400⟩, ⟨.count 7, 12754588212880113600⟩, ⟨.count 8, 5101835285152045440⟩, ⟨.count 9, 1700611761717348480⟩, ⟨.path 6, 31246554209971900800⟩, ⟨.privateRow 2 34, 42633805425078389722200⟩, ⟨.privateRow 2 35, 102442726761150925749600⟩, ⟨.privateRow 3 31, 9519776636211799677720⟩, ⟨.privateRow 3 32, 21400498409451113272320⟩, ⟨.privateRow 3 33, 32151411672911165915280⟩, ⟨.privateRow 3 34, 55811527101920801090880⟩, ⟨.privateRow 4 27, 140205027844850173920⟩, ⟨.privateRow 4 28, 1404118199213175045600⟩, ⟨.privateRow 4 29, 4344370659256269017376⟩, ⟨.privateRow 4 30, 7200086518439518223520⟩, ⟨.privateRow 4 31, 11209784881141059333120⟩, ⟨.privateRow 4 32, 18469220725526701450320⟩, ⟨.privateRow 5 24, 26278500794156170560⟩, ⟨.privateRow 5 25, 197422804695080044080⟩, ⟨.privateRow 5 26, 747887405168309028480⟩, ⟨.privateRow 5 27, 1565575089685744737600⟩, ⟨.privateRow 5 28, 2589813063011872361664⟩, ⟨.privateRow 5 29, 4001569843388094497520⟩, ⟨.privateRow 5 30, 6905900929040532619200⟩, ⟨.privateRow 5 31, 7838787707233076674080⟩, ⟨.privateRow 6 21, 253067226446034000⟩, ⟨.privateRow 6 22, 23105037774522904200⟩, ⟨.privateRow 6 23, 116360310719886433200⟩, ⟨.privateRow 6 24, 312196383905149844100⟩, ⟨.privateRow 6 25, 592061622008772801600⟩, ⟨.privateRow 6 26, 989526597700852411200⟩, ⟨.privateRow 6 27, 1519030965397790164320⟩, ⟨.privateRow 6 28, 2625205526899256000700⟩, ⟨.privateRow 6 29, 3270337153916808175200⟩, ⟨.privateRow 6 30, 2864467936142658846000⟩, ⟨.privateRow 7 20, 14272991571556317600⟩, ⟨.privateRow 7 21, 56666813345795933280⟩, ⟨.privateRow 7 22, 132843422735738114400⟩, ⟨.privateRow 7 23, 245791543685710522500⟩, ⟨.privateRow 7 24, 408060056905953566400⟩, ⟨.privateRow 7 25, 626037704782198909200⟩, ⟨.privateRow 7 26, 1081771288855274777760⟩, ⟨.privateRow 7 27, 1412722484912340201600⟩, ⟨.privateRow 7 28, 1135259577836908524000⟩, ⟨.privateRow 8 18, 7741326456984180060⟩, ⟨.privateRow 8 19, 28176044870271523680⟩, ⟨.privateRow 8 20, 62327421066940821792⟩, ⟨.privateRow 8 21, 114059086074070497360⟩, ⟨.privateRow 8 22, 187811311434659672760⟩, ⟨.privateRow 8 23, 286796026386761411520⟩, ⟨.privateRow 8 24, 496153481481036419040⟩, ⟨.privateRow 8 25, 678544092925222043520⟩, ⟨.privateRow 8 26, 123666361547383434780⟩, ⟨.privateRow 9 16, 4302402405712266240⟩, ⟨.privateRow 9 17, 15384237881461569120⟩, ⟨.privateRow 9 18, 33548432026605874560⟩, ⟨.privateRow 9 19, 60900796755722379456⟩, ⟨.privateRow 9 20, 99706237733280097920⟩, ⟨.privateRow 9 21, 151496164439653793760⟩, ⟨.privateRow 9 22, 260922433154918895360⟩, ⟨.privateRow 9 23, 131608454670681468480⟩, ⟨.privateRow 10 14, 2626837810509832920⟩, ⟨.privateRow 10 15, 9614997268171162560⟩, ⟨.privateRow 10 16, 21310791139020523140⟩, ⟨.privateRow 10 17, 38708242712725556880⟩, ⟨.privateRow 10 18, 63177726947799496032⟩, ⟨.privateRow 10 19, 95801129243410631040⟩, ⟨.privateRow 10 20, 47032544034995418900⟩, ⟨.privateRow 11 12, 1822084030411444800⟩, ⟨.privateRow 11 13, 7071421356120607200⟩, ⟨.privateRow 11 14, 16328676118687178400⟩, ⟨.privateRow 11 15, 30140306669722649400⟩, ⟨.privateRow 11 16, 43315906722962983200⟩, ⟨.privateRow 12 10, 1496259976362176025⟩, ⟨.privateRow 12 11, 6272692986175696080⟩, ⟨.privateRow 12 12, 15350334906998005200⟩, ⟨.privateRow 12 13, 11520398816212532400⟩, ⟨.privateRow 13 8, 1493394362180360640⟩, ⟨.privateRow 13 9, 6764486962902488820⟩, ⟨.privateRow 13 10, 3385027220942150784⟩, ⟨.privateRow 14 6, 1930059380361752640⟩, ⟨.privateRow 14 7, 1788143249452800240⟩, ⟨.privateRow 15 4, 1066611762831494880⟩, ⟨.hall 5 31, 429670190421398826900⟩, ⟨.hall 4 32, 3405151126789139407680⟩, ⟨.hall 3 33, 9634515828051687693120⟩, ⟨.assumptionRow 20, 5794578124983648⟩]
  caps := #[0, 639599543056595721600, 0, 1811240578263436320, 29295397157725443888, 0, 1557546150695414880, 1930564737342366840, 3359220795660772224, 0, 445059273148281792, 3288981805660360400, 75858018747081571, 2837707207080009264, 1771806116714730096, 657328974180086208, 92009570482588318560, 25185295850849534400] }

theorem case_54_37_20_checked :
    (Witness.linear .conditional case_54_37_20).check 54 37 20 = true := by
  change case_54_37_20.check 54 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_21 : Certificate := {
  objectiveScale := 13398559574400000
  eta := 16434610028530752669811200
  rows := #[⟨.count 2, 1851264706158484088472000⟩, ⟨.count 3, 200994453811492558176960⟩, ⟨.count 4, 19385516416353443516160⟩, ⟨.count 5, 1509900299867617257600⟩, ⟨.count 6, 76831209949015922400⟩, ⟨.path 6, 75339938413444504800⟩, ⟨.privateRow 2 34, 91043313545889324219600⟩, ⟨.privateRow 2 35, 233763967000964575375200⟩, ⟨.privateRow 3 31, 21304236697855570859400⟩, ⟨.privateRow 3 32, 47793095406207899748000⟩, ⟨.privateRow 3 33, 73148768000865334617840⟩, ⟨.privateRow 3 34, 128727240432607454077440⟩, ⟨.privateRow 4 27, 503125122045015447120⟩, ⟨.privateRow 4 28, 3128867512988946248520⟩, ⟨.privateRow 4 29, 9631092810974163761232⟩, ⟨.privateRow 4 30, 16018889713446183864300⟩, ⟨.privateRow 4 31, 25291498120260406594560⟩, ⟨.privateRow 4 32, 42494841149692343532120⟩, ⟨.privateRow 5 24, 140745868660226269440⟩, ⟨.privateRow 5 25, 478190769747896925720⟩, ⟨.privateRow 5 26, 1646764840323379782720⟩, ⟨.privateRow 5 27, 3423554175496295000160⟩, ⟨.privateRow 5 28, 5697802529819020805184⟩, ⟨.privateRow 5 29, 8945491179237814721520⟩, ⟨.privateRow 5 30, 15822775266311829816000⟩, ⟨.privateRow 5 31, 18587808027839312982720⟩, ⟨.privateRow 6 21, 24496907519976091200⟩, ⟨.privateRow 6 22, 78000380535196599480⟩, ⟨.privateRow 6 23, 272126000455491982800⟩, ⟨.privateRow 6 24, 677562192086611431600⟩, ⟨.privateRow 6 25, 1275509434733300566800⟩, ⟨.privateRow 6 26, 2147283851968813357800⟩, ⟨.privateRow 6 27, 3355742281497815729520⟩, ⟨.privateRow 6 28, 5968059094554175218600⟩, ⟨.privateRow 6 29, 7753085647439705773200⟩, ⟨.privateRow 6 30, 7237722676356572400000⟩, ⟨.privateRow 7 17, 108457382762586000⟩, ⟨.privateRow 7 18, 3036806717352408000⟩, ⟨.privateRow 7 19, 12324373927921855800⟩, ⟨.privateRow 7 20, 46628786778256519200⟩, ⟨.privateRow 7 21, 130127167838550682800⟩, ⟨.privateRow 7 22, 285830996696580535200⟩, ⟨.privateRow 7 23, 522102994880812745400⟩, ⟨.privateRow 7 24, 872387803989136749600⟩, ⟨.privateRow 7 25, 1363526216091231192000⟩, ⟨.privateRow 7 26, 2430234943628438026080⟩, ⟨.privateRow 7 27, 3320899985760725768400⟩, ⟨.privateRow 7 28, 3479067002289497018400⟩, ⟨.privateRow 8 14, 13286029388416785⟩, ⟨.privateRow 8 15, 354294117024447600⟩, ⟨.privateRow 8 16, 1655059660957062360⟩, ⟨.privateRow 8 17, 8143314012838841760⟩, ⟨.privateRow 8 18, 26164620542255455260⟩, ⟨.privateRow 8 19, 65280301489559126880⟩, ⟨.privateRow 8 20, 133753115059069457952⟩, ⟨.privateRow 8 21, 239809878009947765520⟩, ⟨.privateRow 8 22, 395870531657266525860⟩, ⟨.privateRow 8 23, 614740783793647951440⟩, ⟨.privateRow 8 24, 1096823727484284880080⟩, ⟨.privateRow 8 25, 1569537110182983845904⟩, ⟨.privateRow 8 26, 887028466088258233740⟩, ⟨.privateRow 9 12, 44460438214832640⟩, ⟨.privateRow 9 13, 224386274115483480⟩, ⟨.privateRow 9 14, 1297503788569532544⟩, ⟨.privateRow 9 15, 5587724359928430720⟩, ⟨.privateRow 9 16, 16134009021420998400⟩, ⟨.privateRow 9 17, 37145769869363195040⟩, ⟨.privateRow 9 18, 72696858339270896640⟩, ⟨.privateRow 9 19, 127659256246248959232⟩, ⟨.privateRow 9 20, 207915534275146938240⟩, ⟨.privateRow 9 21, 319620532771654994880⟩, ⟨.privateRow 9 22, 565655864552175196800⟩, ⟨.privateRow 9 23, 607874226382745562240⟩, ⟨.privateRow 10 9, 11188235274456240⟩, ⟨.privateRow 10 10, 35429411702444760⟩, ⟨.privateRow 10 11, 225080968462590240⟩, ⟨.privateRow 10 12, 1129312498015426725⟩, ⟨.privateRow 10 13, 4364903521741194432⟩, ⟨.privateRow 10 14, 11630969727459722640⟩, ⟨.privateRow 10 15, 25231191810864122160⟩, ⟨.privateRow 10 16, 47670273445639424580⟩, ⟨.privateRow 10 17, 81880591299959153520⟩, ⟨.privateRow 10 18, 131372258592665170080⟩, ⟨.privateRow 10 19, 199703783962780297200⟩, ⟨.privateRow 10 20, 239440821638047299270⟩, ⟨.privateRow 11 8, 47949579747669600⟩, ⟨.privateRow 11 9, 253067226446034000⟩, ⟨.privateRow 11 10, 1161131980164156000⟩, ⟨.privateRow 11 11, 4061728984458845700⟩, ⟨.privateRow 11 12, 10203670570304090880⟩, ⟨.privateRow 11 13, 21214264068361821600⟩, ⟨.privateRow 11 14, 38987926240470530400⟩, ⟨.privateRow 11 15, 65645638540101219600⟩, ⟨.privateRow 11 16, 103748360398275902400⟩, ⟨.privateRow 11 17, 25478808358586703120⟩, ⟨.privateRow 12 6, 55674789818127480⟩, ⟨.privateRow 12 7, 351630251482910400⟩, ⟨.privateRow 12 8, 1453730623028884200⟩, ⟨.privateRow 12 9, 4650482443631824800⟩, ⟨.privateRow 12 10, 11204551450898155350⟩, ⟨.privateRow 12 11, 22678197719250593520⟩, ⟨.privateRow 12 12, 40841435102297801400⟩, ⟨.privateRow 12 13, 15588941149075694400⟩, ⟨.privateRow 13 4, 127256662441434240⟩, ⟨.privateRow 13 5, 601287730035776784⟩, ⟨.privateRow 13 6, 2250433609490626560⟩, ⟨.privateRow 13 7, 6755207831266134240⟩, ⟨.privateRow 13 8, 15877140061075413120⟩, ⟨.privateRow 13 9, 8267706287991930780⟩, ⟨.privateRow 14 1, 188810156774519280⟩, ⟨.privateRow 14 2, 197392436627906520⟩, ⟨.privateRow 14 3, 1240752458803983840⟩, ⟨.privateRow 14 4, 4559765286104640612⟩, ⟨.privateRow 14 5, 5256872259669510480⟩, ⟨.privateRow 15 0, 1762228129895513280⟩, ⟨.privateRow 15 1, 1842329408527127520⟩, ⟨.hall 5 31, 1432442748533147401050⟩, ⟨.hall 4 32, 8458397504463546319680⟩, ⟨.hall 3 33, 22773792425030863856640⟩, ⟨.assumptionRow 21, 3639660686133472⟩]
  caps := #[0, 2263422125379044710080, 85591237371149229720, 0, 2180685234185825796, 12980546033153858016, 0, 157616209522321550, 0, 135702257666727752, 0, 57004406399800288, 13055407138785347050, 1576492835060368368, 0, 0, 402132061870154808192, 129330303661405086240] }

theorem case_54_37_21_checked :
    (Witness.linear .conditional case_54_37_21).check 54 37 21 = true := by
  change case_54_37_21.check 54 37 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_22 : Certificate := {
  objectiveScale := 16998778298502000000
  eta := 16872123763513426634197171200
  rows := #[⟨.count 2, 2130163965820484059409143200⟩, ⟨.count 3, 256553126729081236597102560⟩, ⟨.count 4, 28461915951589780653913920⟩, ⟨.count 5, 2756757260768916698092800⟩, ⟨.count 6, 216373389653374275722400⟩, ⟨.count 7, 10199419040899797508800⟩, ⟨.path 6, 35685341408430125412000⟩, ⟨.path 7, 9961198762494899431512⟩, ⟨.privateRow 2 35, 883131996784870316995711200⟩, ⟨.privateRow 3 31, 32379075687240497171436480⟩, ⟨.privateRow 4 27, 19347673466359922009040⟩, ⟨.privateRow 4 28, 4233171735601261910336880⟩, ⟨.privateRow 4 29, 14420565175765217562645552⟩, ⟨.privateRow 4 30, 20520812205579784203165060⟩, ⟨.privateRow 4 32, 129115210595178604148712360⟩, ⟨.privateRow 5 24, 712340377459668397440⟩, ⟨.privateRow 5 25, 490847041343302755111000⟩, ⟨.privateRow 5 26, 2212274805112065875163840⟩, ⟨.privateRow 5 27, 5056191999208726285029120⟩, ⟨.privateRow 5 28, 8681862052402946494319232⟩, ⟨.privateRow 5 31, 140048077144608821024796960⟩, ⟨.privateRow 6 22, 47415156374659177704600⟩, ⟨.privateRow 6 23, 298737745797148434176400⟩, ⟨.privateRow 6 24, 899552332910787498142200⟩, ⟨.privateRow 6 25, 1836502535638207587150000⟩, ⟨.privateRow 6 27, 12193041198429961500430800⟩, ⟨.privateRow 6 28, 2853924940381774590431100⟩, ⟨.privateRow 6 31, 145791588565518944854806000⟩, ⟨.privateRow 7 18, 112081527921975796800⟩, ⟨.privateRow 7 19, 3460517174591002726200⟩, ⟨.privateRow 7 20, 33512376848670763243200⟩, ⟨.privateRow 7 21, 144540338408179987553280⟩, ⟨.privateRow 7 22, 368312354254714910040000⟩, ⟨.privateRow 7 23, 728074600285659652525500⟩, ⟨.privateRow 7 24, 1005995759687116762449600⟩, ⟨.privateRow 7 25, 1010228171670075181824000⟩, ⟨.privateRow 7 26, 7379133970104704929080960⟩, ⟨.privateRow 7 27, 4022578016737730853202800⟩, ⟨.privateRow 7 28, 4392306956970348512896800⟩, ⟨.privateRow 7 29, 4132950301358896519101600⟩, ⟨.privateRow 8 15, 33998063469665991696⟩, ⟨.privateRow 8 16, 218558979447852803760⟩, ⟨.privateRow 8 17, 2824454503633790079360⟩, ⟨.privateRow 8 18, 19633881653732110204440⟩, ⟨.privateRow 8 19, 70561435364770417310880⟩, ⟨.privateRow 8 20, 165740559414621709518000⟩, ⟨.privateRow 8 21, 322018324496853051347280⟩, ⟨.privateRow 8 22, 540059238215644278090960⟩, ⟨.privateRow 8 23, 804952721306441876248080⟩, ⟨.privateRow 8 24, 1161713828758486936252320⟩, ⟨.privateRow 8 25, 4598102092018446712917216⟩, ⟨.privateRow 8 26, 3603837225363932202265620⟩, ⟨.privateRow 8 27, 3346259397001875232678800⟩, ⟨.privateRow 9 13, 28331719558054993080⟩, ⟨.privateRow 9 14, 181323005171551955712⟩, ⟨.privateRow 9 15, 2039883808179959501760⟩, ⟨.privateRow 9 16, 11890604762211387864960⟩, ⟨.privateRow 9 17, 38077831086025910699520⟩, ⟨.privateRow 9 18, 85757539491363549962880⟩, ⟨.privateRow 9 19, 163190704654396760140800⟩, ⟨.privateRow 9 20, 279388530468499638426240⟩, ⟨.privateRow 9 21, 440048268175710152518560⟩, ⟨.privateRow 9 22, 762463236746375973768960⟩, ⟨.privateRow 9 23, 961540786174309058477760⟩, ⟨.privateRow 9 25, 2699219585735015300717760⟩, ⟨.privateRow 10 11, 29998291296764110320⟩, ⟨.privateRow 10 12, 159365922514059336075⟩, ⟨.privateRow 10 13, 1563910919604635618016⟩, ⟨.privateRow 10 14, 8086682239570553739120⟩, ⟨.privateRow 10 15, 24086320350432598732320⟩, ⟨.privateRow 10 16, 53121974171353112025000⟩, ⟨.privateRow 10 17, 99815223613896654711120⟩, ⟨.privateRow 10 18, 170585283459049113334680⟩, ⟨.privateRow 10 19, 273174439978766243277360⟩, ⟨.privateRow 10 20, 495755511756735782662110⟩, ⟨.privateRow 10 21, 763572221197648412069520⟩, ⟨.privateRow 10 23, 2350558112165767333878048⟩, ⟨.privateRow 10 24, 538274339883486813526920⟩, ⟨.privateRow 11 9, 40473885082935704400⟩, ⟨.privateRow 11 10, 171418807410080630400⟩, ⟨.privateRow 11 11, 1411526742267382690950⟩, ⟨.privateRow 11 12, 6459632059236538422240⟩, ⟨.privateRow 11 13, 18473437548568510794000⟩, ⟨.privateRow 11 14, 40461431579833262644800⟩, ⟨.privateRow 11 15, 75584980392382427967000⟩, ⟨.privateRow 11 16, 128155037948968234932000⟩, ⟨.privateRow 11 17, 203842674831697381640160⟩, ⟨.privateRow 11 19, 1333300840873338708270900⟩, ⟨.privateRow 11 20, 509034270704499077709600⟩, ⟨.privateRow 11 21, 267127641547375649040000⟩, ⟨.privateRow 11 22, 1703594391802863321041280⟩, ⟨.privateRow 11 25, 1372914655898262028952400⟩, ⟨.privateRow 12 7, 70296747775625170800⟩, ⟨.privateRow 12 8, 222606367956146374200⟩, ⟨.privateRow 12 9, 1492772114529452156400⟩, ⟨.privateRow 12 10, 6344281486750171664700⟩, ⟨.privateRow 12 11, 17719466889309251386320⟩, ⟨.privateRow 12 12, 38828910753493531842600⟩, ⟨.privateRow 12 13, 72638170220767147642800⟩, ⟨.privateRow 12 14, 122767411927814725371300⟩, ⟨.privateRow 12 15, 193424696811349731327600⟩, ⟨.privateRow 12 16, 341121998255998703824080⟩, ⟨.privateRow 12 18, 1770889308683133443354550⟩, ⟨.privateRow 12 20, 2464697706010452655142400⟩, ⟨.privateRow 13 6, 337424389323000819840⟩, ⟨.privateRow 13 7, 1958936038014088092960⟩, ⟨.privateRow 13 8, 7730988214194636431040⟩, ⟨.privateRow 13 9, 21837684696497959309020⟩, ⟨.privateRow 13 10, 48082975478527616827200⟩, ⟨.privateRow 13 12, 338553463241120091814080⟩, ⟨.privateRow 13 13, 155735415022120003390320⟩, ⟨.privateRow 13 14, 428958423662985769512960⟩, ⟨.privateRow 13 16, 1462790965113429054143040⟩, ⟨.privateRow 13 17, 2171747725780164026695200⟩, ⟨.privateRow 13 18, 1112319499403272202602560⟩, ⟨.privateRow 14 4, 520898901017382515628⟩, ⟨.privateRow 14 5, 3289887795899257993440⟩, ⟨.privateRow 14 6, 12733084247091572604240⟩, ⟨.privateRow 14 7, 34930867479989180459760⟩, ⟨.privateRow 14 8, 76832587900063921055130⟩, ⟨.privateRow 14 9, 101401652731383796375584⟩, ⟨.privateRow 14 10, 68460998419427416339680⟩, ⟨.privateRow 14 14, 6151816021015287509566680⟩, ⟨.privateRow 14 16, 4281788966362884278462160⟩, ⟨.privateRow 15 2, 2315106226743922291680⟩, ⟨.privateRow 15 3, 7292584614243355218792⟩, ⟨.privateRow 15 4, 28146817809360318388320⟩, ⟨.privateRow 15 5, 78327760671502704201840⟩, ⟨.privateRow 15 8, 116681353827893683500672⟩, ⟨.privateRow 15 9, 24308615380811184062640⟩, ⟨.privateRow 15 10, 2083061348786435311213920⟩, ⟨.privateRow 15 12, 380098349590865787161280⟩, ⟨.privateRow 15 13, 651470892205739732878752⟩, ⟨.privateRow 15 14, 1166813538278936835006720⟩, ⟨.privateRow 15 15, 1932534922774489132979880⟩, ⟨.privateRow 15 16, 46436400696029593326517440⟩, ⟨.privateRow 15 21, 25572663380613365633897280⟩, ⟨.privateRow 16 5, 1587209592511789077031200⟩, ⟨.privateRow 16 9, 13070555500913090507527200⟩, ⟨.privateRow 16 16, 221998429965258138452059800⟩, ⟨.privateRow 17 4, 24708992575318662388377600⟩, ⟨.privateRow 17 14, 2188608822514634377662604800⟩, ⟨.privateRow 17 20, 20541752341400682980293305600⟩, ⟨.hall 13 7, 126844414909232480460⟩, ⟨.hall 15 7, 8265647609609488248150⟩, ⟨.hall 11 11, 850012563478135365⟩, ⟨.hall 8 16, 296463110716829056⟩, ⟨.hall 9 16, 147953450507673888⟩, ⟨.hall 14 19, 13671022540535256536640⟩, ⟨.hall 7 24, 4321508720261110224⟩, ⟨.hall 3 30, 14378072153772235303395⟩, ⟨.hall 4 31, 355355651792540117668950⟩, ⟨.hall 2 34, 335500564167275730665682240⟩]
  caps := #[0, 1151210102755888042515648, 0, 3589809090053930944200, 54424388862948883784148, 8875702828910868951000, 0, 783310691817413451432, 7365236653138031903844, 15332713432454874456, 581713954590465361665, 13223820091462455280500, 0, 4843123077280388696136, 105139374723219694286286, 289045921155298412881776, 0, 0] }

theorem case_54_37_22_checked :
    (Witness.linear .conditional case_54_37_22).check 54 37 22 = true := by
  change case_54_37_22.check 54 37 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_23 : Certificate := {
  objectiveScale := 99588324041846640000
  eta := 85717891927940546402499571200
  rows := #[⟨.count 2, 10040146575505103349610718400⟩, ⟨.count 3, 1080468181305756362707267680⟩, ⟨.count 4, 101830953909298280653546560⟩, ⟨.count 5, 7660178527513338268041600⟩, ⟨.count 6, 370653799718387335550400⟩, ⟨.path 5, 268040708100392939712000⟩, ⟨.path 6, 357315470909021954128800⟩, ⟨.privateRow 2 35, 5199963931882542328325820000⟩, ⟨.privateRow 3 34, 5252432036420456268935954400⟩, ⟨.privateRow 4 28, 16837978446095851348864560⟩, ⟨.privateRow 4 29, 43478926219632562417847088⟩, ⟨.privateRow 5 24, 24710253314559155703360⟩, ⟨.privateRow 5 25, 1593811338789065542866720⟩, ⟨.privateRow 5 26, 8461496742142613745850560⟩, ⟨.privateRow 5 27, 18631530999177603400333440⟩, ⟨.privateRow 5 28, 32039314447657401284976576⟩, ⟨.privateRow 6 21, 11231933324799616228800⟩, ⟨.privateRow 6 22, 125610454349009041492080⟩, ⟨.privateRow 6 23, 931210472131997812154400⟩, ⟨.privateRow 6 24, 3312718334983086811481700⟩, ⟨.privateRow 6 25, 7040951346237778473332400⟩, ⟨.privateRow 6 26, 13753658355291085622391000⟩, ⟨.privateRow 6 31, 984343236724345033758222000⟩, ⟨.privateRow 7 18, 2159987177846080044000⟩, ⟨.privateRow 7 19, 9827941659199664200200⟩, ⟨.privateRow 7 20, 83218415088288065695200⟩, ⟨.privateRow 7 21, 433552626337265186431680⟩, ⟨.privateRow 7 22, 1286056365689556058197600⟩, ⟨.privateRow 7 23, 2710405910440707391212300⟩, ⟨.privateRow 7 24, 5234080929356621162620800⟩, ⟨.privateRow 7 25, 9643550753784203833777200⟩, ⟨.privateRow 7 26, 9415729706179518284603040⟩, ⟨.privateRow 7 28, 58647539855441196138679200⟩, ⟨.privateRow 8 15, 262078444245324378672⟩, ⟨.privateRow 8 16, 1123193332479961622880⟩, ⟨.privateRow 8 17, 6955158712664377741680⟩, ⟨.privateRow 8 18, 46846521908851732687620⟩, ⟨.privateRow 8 19, 204063806814654845756880⟩, ⟨.privateRow 8 20, 549971615248813208643192⟩, ⟨.privateRow 8 21, 1160570710599711456885840⟩, ⟨.privateRow 8 22, 2230942756638323773445400⟩, ⟨.privateRow 8 23, 4126050706865139021649680⟩, ⟨.privateRow 8 24, 9107881133635635469798680⟩, ⟨.privateRow 8 26, 35339312618150152531079160⟩, ⟨.privateRow 8 27, 23487470173265970816584640⟩, ⟨.privateRow 8 28, 34527524637100260268142640⟩, ⟨.privateRow 9 13, 218398703537770315560⟩, ⟨.privateRow 9 14, 931834468427820013056⟩, ⟨.privateRow 9 15, 4742371848248726852160⟩, ⟨.privateRow 9 16, 27955034052834600391680⟩, ⟨.privateRow 9 17, 105996170783664526485120⟩, ⟨.privateRow 9 18, 270020215283061481056000⟩, ⟨.privateRow 9 19, 561896184461975467872768⟩, ⟨.privateRow 9 20, 1056079064218196014796800⟩, ⟨.privateRow 9 21, 1875608065982371470029280⟩, ⟨.privateRow 9 22, 4003061036958583223944320⟩, ⟨.privateRow 9 23, 7415072782514377753893120⟩, ⟨.privateRow 9 24, 2611000180534751676582912⟩, ⟨.privateRow 10 11, 231245686098815628240⟩, ⟨.privateRow 10 12, 737095624439974815015⟩, ⟨.privateRow 10 13, 3669098219434541301408⟩, ⟨.privateRow 10 14, 18813488319039357183240⟩, ⟨.privateRow 10 15, 64410817643370106912080⟩, ⟨.privateRow 10 16, 158557458768421249096560⟩, ⟨.privateRow 10 17, 324858144298636173017520⟩, ⟨.privateRow 10 18, 601076911876651462484232⟩, ⟨.privateRow 10 19, 1050060966609599677212480⟩, ⟨.privateRow 10 20, 2173940695014965721084240⟩, ⟨.privateRow 10 21, 4151884153512178138975920⟩, ⟨.privateRow 10 22, 7380784186058947814350200⟩, ⟨.privateRow 10 24, 17993978383828665184146180⟩, ⟨.privateRow 10 25, 3510540760666120052311440⟩, ⟨.privateRow 10 27, 82613677587232377266881200⟩, ⟨.privateRow 11 9, 311998147911100450800⟩, ⟨.privateRow 11 10, 991052940423495549600⟩, ⟨.privateRow 11 11, 3509979163999880071500⟩, ⟨.privateRow 11 12, 14975911099732821638400⟩, ⟨.privateRow 11 13, 47735716630398368972400⟩, ⟨.privateRow 11 14, 114911317861411458340800⟩, ⟨.privateRow 11 15, 232594619267725386071400⟩, ⟨.privateRow 11 16, 423750211799258248632000⟩, ⟨.privateRow 11 17, 723336506117095285134720⟩, ⟨.privateRow 11 18, 1437687465574350877286400⟩, ⟨.privateRow 11 19, 2673200131302308662454400⟩, ⟨.privateRow 11 20, 4820906239194349565632800⟩, ⟨.privateRow 11 21, 8109455860505322917193600⟩, ⟨.privateRow 11 22, 3999691456961143339075680⟩, ⟨.privateRow 11 23, 11118209999886020114483400⟩, ⟨.privateRow 11 24, 14356282777981376143111200⟩, ⟨.privateRow 12 7, 541891520056121835600⟩, ⟨.privateRow 12 8, 1143993209007368319600⟩, ⟨.privateRow 12 9, 3633860781552817015200⟩, ⟨.privateRow 12 10, 14800412141532827634825⟩, ⟨.privateRow 12 11, 43242943300478522480880⟩, ⟨.privateRow 12 12, 101488540399082246638800⟩, ⟨.privateRow 12 13, 200374810531521358748400⟩, ⟨.privateRow 12 14, 352635906676521284516700⟩, ⟨.privateRow 12 15, 572828599564780427668800⟩, ⟨.privateRow 12 16, 1074896019183323273096160⟩, ⟨.privateRow 12 17, 1901316713370246147175200⟩, ⟨.privateRow 12 18, 3325588258584419705077200⟩, ⟨.privateRow 12 20, 14472658087152216611259600⟩, ⟨.privateRow 12 21, 11790909206597143796453280⟩, ⟨.privateRow 13 6, 1300539648134692405440⟩, ⟨.privateRow 13 7, 5491167403235367934080⟩, ⟨.privateRow 13 8, 18896076064074648479040⟩, ⟨.privateRow 13 9, 52509288293438205869640⟩, ⟨.privateRow 13 10, 121903916351825168136576⟩, ⟨.privateRow 13 11, 245337515051694474483360⟩, ⟨.privateRow 13 12, 440982982229055701783040⟩, ⟨.privateRow 13 13, 737189223884348145150240⟩, ⟨.privateRow 13 14, 1343339225646034100964480⟩, ⟨.privateRow 13 16, 8747429673353941118989440⟩, ⟨.privateRow 13 18, 12644589624678699389919360⟩, ⟨.privateRow 13 19, 15476855326018884522204480⟩, ⟨.privateRow 13 21, 72055098665254498030997760⟩, ⟨.privateRow 14 4, 4015416163615862801796⟩, ⟨.privateRow 14 5, 8453507712875500635360⟩, ⟨.privateRow 14 6, 31231014605901155125080⟩, ⟨.privateRow 14 7, 85032342288335918155680⟩, ⟨.privateRow 14 8, 195751537976273311587555⟩, ⟨.privateRow 14 9, 396187728143431796443872⟩, ⟨.privateRow 14 10, 717038600645689786035000⟩, ⟨.privateRow 14 13, 9060239016449610430961520⟩, ⟨.privateRow 14 15, 16195511859917313300577200⟩, ⟨.privateRow 14 16, 4105763027297219714836410⟩, ⟨.privateRow 14 17, 17185981180275892791686880⟩, ⟨.privateRow 14 18, 29620386566939681267915160⟩, ⟨.privateRow 14 20, 54810430633356527244515400⟩, ⟨.privateRow 15 2, 17846294060514945785760⟩, ⟨.privateRow 15 3, 18738608763540693075048⟩, ⟨.privateRow 15 4, 78899405320171339263360⟩, ⟨.privateRow 15 5, 187386087635406930750480⟩, ⟨.privateRow 15 6, 440908441495075131177600⟩, ⟨.privateRow 15 7, 913507177222608787408590⟩, ⟨.privateRow 15 8, 1698967194561022838804352⟩, ⟨.privateRow 15 10, 4381951587781823611395840⟩, ⟨.privateRow 15 14, 2914894696550774478340800⟩, ⟨.privateRow 15 16, 19006303174448417261834400⟩, ⟨.privateRow 15 18, 224863305162488316900576⟩, ⟨.privateRow 16 2, 843237394359331188377160⟩, ⟨.privateRow 16 3, 443809154925963783356400⟩, ⟨.privateRow 16 4, 1717705803324563531879400⟩, ⟨.privateRow 16 9, 64431985517712998496511200⟩, ⟨.privateRow 16 14, 7378327200644147898300150⟩, ⟨.privateRow 16 15, 66254366699661736229634000⟩, ⟨.privateRow 16 16, 66522061110569460416420400⟩, ⟨.privateRow 16 17, 562158262906220792251440⟩, ⟨.privateRow 17 5, 84323739435933118837716000⟩, ⟨.privateRow 17 8, 795670156728804813648192000⟩, ⟨.privateRow 17 13, 702697828632775990314300000⟩, ⟨.privateRow 17 15, 929434994671618376522380800⟩, ⟨.hall 11 10, 24539361665124398400⟩, ⟨.hall 13 10, 386666246864505117510⟩, ⟨.hall 8 18, 8425648713098320704⟩, ⟨.hall 6 19, 1550871758735186976⟩, ⟨.hall 12 20, 741354108477457071168⟩, ⟨.hall 16 20, 143484204246540164117510400⟩, ⟨.hall 7 22, 30421168738659784008⟩, ⟨.hall 14 22, 391066617673892725044480⟩, ⟨.hall 11 25, 1076321610720701685925200⟩, ⟨.hall 10 26, 345069951589677098584800⟩, ⟨.hall 6 27, 11205116258502919226760⟩, ⟨.hall 8 27, 88344965220234222820320⟩, ⟨.hall 3 33, 1346898129790192887599611920⟩]
  caps := #[0, 36330666341879740909478400, 0, 0, 111930305139839463502368, 12300051498025318444560, 78080842792252659001500, 361208940565317102720, 15366181862179535024988, 11115956012120127441728, 29295560256880620896865, 172362526006116784663800, 0, 8280102426457541647968, 60848680027384240847856, 8586892943285891218068084, 0, 0] }

theorem case_54_37_23_checked :
    (Witness.linear .conditional case_54_37_23).check 54 37 23 = true := by
  change case_54_37_23.check 54 37 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440, 48450] }

theorem case_54_37_24_checked :
    (Witness.linear .negative case_54_37_24).check 54 37 24 = true := by
  change case_54_37_24.check 54 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_38_1_checked :
    (Witness.rising).check 54 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_38_2_checked :
    (Witness.rising).check 54 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_38_3_checked :
    (Witness.rising).check 54 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_38_4_checked :
    (Witness.rising).check 54 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_38_5_checked :
    (Witness.rising).check 54 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_38_6_checked :
    (Witness.rising).check 54 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_38_7_checked :
    (Witness.rising).check 54 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_38_8_checked :
    (Witness.rising).check 54 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_38_9_checked :
    (Witness.rising).check 54 38 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_38_10_checked :
    (Witness.linear .positive case_54_38_10).check 54 38 10 = true := by
  change case_54_38_10.check 54 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_54_38_11_checked :
    (Witness.linear .positive case_54_38_11).check 54 38 11 = true := by
  change case_54_38_11.check 54 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_54_38_12_checked :
    (Witness.linear .positive case_54_38_12).check 54 38 12 = true := by
  change case_54_38_12.check 54 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_54_38_13_checked :
    (Witness.linear .positive case_54_38_13).check 54 38 13 = true := by
  change case_54_38_13.check 54 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_54_38_14_checked :
    (Witness.linear .positive case_54_38_14).check 54 38 14 = true := by
  change case_54_38_14.check 54 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_54_38_15_checked :
    (Witness.linear .positive case_54_38_15).check 54 38 15 = true := by
  change case_54_38_15.check 54 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_54_38_16_checked :
    (Witness.linear .positive case_54_38_16).check 54 38 16 = true := by
  change case_54_38_16.check 54 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_54_38_17_checked :
    (Witness.linear .positive case_54_38_17).check 54 38 17 = true := by
  change case_54_38_17.check 54 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_18 : Certificate := {
  objectiveScale := 7
  eta := 229064475
  rows := #[⟨.assumptionRow 18, 18⟩]
  caps := #[0, 0, 63734265, 17866745, 5051720, 1456084, 425068, 125970, 38012, 11726, 3718, 1221, 32890, 139150, 68310, 22264, 5401] }

theorem case_54_38_18_checked :
    (Witness.linear .conditional case_54_38_18).check 54 38 18 = true := by
  change case_54_38_18.check 54 38 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_19 : Certificate := {
  objectiveScale := 130618413099294120000
  eta := 198139348234597089535314699600
  rows := #[⟨.count 2, 20925072388262811747896517600⟩, ⟨.count 3, 2053113414839518406272017120⟩, ⟨.count 4, 187521732280879784979871680⟩, ⟨.count 5, 15448558426181477850052800⟩, ⟨.count 6, 1458430340933216440389600⟩, ⟨.count 7, 226866941922944779616160⟩, ⟨.count 8, 100829751965753235384960⟩, ⟨.path 5, 2192738314459348540684800⟩, ⟨.path 6, 448973232433225207868160⟩, ⟨.privateRow 2 35, 1654540607444036277740654880⟩, ⟨.privateRow 2 36, 2660241760988450485779092160⟩, ⟨.privateRow 3 31, 112928962095386603083885968⟩, ⟨.privateRow 3 32, 311481559267884047151689580⟩, ⟨.privateRow 3 33, 650899261689779600082224640⟩, ⟨.privateRow 3 34, 814525243020418419644033880⟩, ⟨.privateRow 3 35, 1268326646789499331489334880⟩, ⟨.privateRow 4 28, 34453680577950889337013360⟩, ⟨.privateRow 4 29, 61408019744071374453959880⟩, ⟨.privateRow 4 30, 144598506869058632676494208⟩, ⟨.privateRow 4 31, 210427191024314245407546120⟩, ⟨.privateRow 4 32, 288293867245509732801754560⟩, ⟨.privateRow 4 33, 417111077506899901951425600⟩, ⟨.privateRow 5 24, 190136103706848958154496⟩, ⟨.privateRow 5 25, 6384083759879268838034640⟩, ⟨.privateRow 5 26, 13792294710297598253628870⟩, ⟨.privateRow 5 27, 31525245052108796008294560⟩, ⟨.privateRow 5 28, 53307429492394163632586040⟩, ⟨.privateRow 5 29, 77195258104980677010725376⟩, ⟨.privateRow 5 30, 104084662396397707014730740⟩, ⟨.privateRow 5 31, 156406751143019398181880720⟩, ⟨.privateRow 5 32, 138145762849507446159126000⟩, ⟨.privateRow 6 22, 937913114876243569408800⟩, ⟨.privateRow 6 23, 2811529601687922804528840⟩, ⟨.privateRow 6 24, 7484208375077040745538400⟩, ⟨.privateRow 6 25, 13547872588344901794637650⟩, ⟨.privateRow 6 26, 21417319636297048837573200⟩, ⟨.privateRow 6 27, 30924124821639496745298000⟩, ⟨.privateRow 6 28, 41127735614316703618986720⟩, ⟨.privateRow 6 29, 61206810372961143667276500⟩, ⟨.privateRow 6 30, 54222999650868905064608400⟩, ⟨.privateRow 7 19, 67312169581533066479520⟩, ⟨.privateRow 7 20, 483442650050084708943960⟩, ⟨.privateRow 7 21, 1733911627553935101352080⟩, ⟨.privateRow 7 22, 3761129801451105953493624⟩, ⟨.privateRow 7 23, 6352274373842453829252480⟩, ⟨.privateRow 7 24, 9722868939554776269264000⟩, ⟨.privateRow 7 25, 13818048738143442750294480⟩, ⟨.privateRow 7 26, 18260088027869400654581640⟩, ⟨.privateRow 7 27, 27010129914083168476015392⟩, ⟨.privateRow 7 28, 3970171483651533643282800⟩, ⟨.privateRow 8 17, 31509297489297886057800⟩, ⟨.privateRow 8 18, 353873648725960874187600⟩, ⟨.privateRow 8 19, 1065014255138268548753640⟩, ⟨.privateRow 8 20, 2108258450193022194412800⟩, ⟨.privateRow 8 21, 3442075657730901072954072⟩, ⟨.privateRow 8 22, 5135315284144682141064560⟩, ⟨.privateRow 8 23, 7177817968062058443966840⟩, ⟨.privateRow 8 24, 9422180214942619299455280⟩, ⟨.privateRow 8 25, 1310786775554792060004480⟩, ⟨.privateRow 9 15, 21006198326198590705200⟩, ⟨.privateRow 9 16, 274581020978167292789400⟩, ⟨.privateRow 9 17, 742649903901605560623840⟩, ⟨.privateRow 9 18, 1400063118441136070501580⟩, ⟨.privateRow 9 19, 2240024603330086081563600⟩, ⟨.privateRow 9 20, 3280748054585695896338136⟩, ⟨.privateRow 9 21, 2379302063747427040542320⟩, ⟨.privateRow 10 13, 18230379261665205504870⟩, ⟨.privateRow 10 14, 240911085946746123116208⟩, ⟨.privateRow 10 15, 619254152697833964768600⟩, ⟨.privateRow 10 16, 1145553404544979409160720⟩, ⟨.privateRow 10 17, 1446276754758772970053020⟩, ⟨.privateRow 11 11, 20653152976178446323600⟩, ⟨.privateRow 11 12, 248135717728220852705175⟩, ⟨.privateRow 11 13, 640989137496574139232960⟩, ⟨.privateRow 11 14, 237284301501039182761800⟩, ⟨.privateRow 12 9, 29708766204195149711640⟩, ⟨.privateRow 12 10, 311068257902749214627760⟩, ⟨.privateRow 12 11, 25995170428670755997685⟩, ⟨.privateRow 13 7, 46908578217150236386800⟩, ⟨.privateRow 13 8, 59417532408390299423280⟩, ⟨.privateRow 14 5, 38621396065453694625132⟩, ⟨.hall 4 33, 23864877134381703791891520⟩, ⟨.hall 3 34, 150226196010024742464727728⟩, ⟨.assumptionRow 19, 131196520520233588420⟩]
  caps := #[0, 67202108475527870950024920, 161846689678866549308952, 0, 1393566595713134815026912, 56717351659359979115528, 23313185449542699816060, 20270040392615590087280, 51540497993042713015004, 29114677378527032472180, 119127609975507471268062, 269112902927246973158850, 656560710022107410520, 1494393256286606530214360, 0, 2309156783018563670912720, 582585090287437775758220] }

theorem case_54_38_19_checked :
    (Witness.linear .conditional case_54_38_19).check 54 38 19 = true := by
  change case_54_38_19.check 54 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_20 : Certificate := {
  objectiveScale := 171866333025387000000
  eta := 284434995603246824805709640400
  rows := #[⟨.count 2, 28116376335650289687096096000⟩, ⟨.count 3, 2495714613749617746676029840⟩, ⟨.count 4, 193225815392085253724506560⟩, ⟨.count 5, 12180594143720011381772400⟩, ⟨.count 6, 810239078296231355772000⟩, ⟨.count 7, 226866941922944779616160⟩, ⟨.count 8, 100829751965753235384960⟩, ⟨.path 5, 5962610885109260727945600⟩, ⟨.path 6, 148694199564544840926720⟩, ⟨.privateRow 2 35, 2352043020386130002670538800⟩, ⟨.privateRow 2 36, 3930885691541877038945934960⟩, ⟨.privateRow 3 31, 141972251936607781441985232⟩, ⟨.privateRow 3 32, 415952435624936291112671640⟩, ⟨.privateRow 3 33, 918931750384028240780640720⟩, ⟨.privateRow 3 34, 1211166980612627863444139520⟩, ⟨.privateRow 3 35, 1972780911023374721451742560⟩, ⟨.privateRow 4 28, 40259622316142170023516720⟩, ⟨.privateRow 4 29, 75608809989676656016123800⟩, ⟨.privateRow 4 30, 191371988380943476382500224⟩, ⟨.privateRow 4 31, 297191642723666180140390740⟩, ⟨.privateRow 4 32, 431371285284913573813012800⟩, ⟨.privateRow 4 33, 661851893497059545275915920⟩, ⟨.privateRow 5 24, 154485584261814778500528⟩, ⟨.privateRow 5 25, 6780200642601870834189840⟩, ⟨.privateRow 5 26, 15493121575487770574620260⟩, ⟨.privateRow 5 27, 38324308403411743128015600⟩, ⟨.privateRow 5 28, 70182008696377008668797560⟩, ⟨.privateRow 5 29, 108627132749019145405640496⟩, ⟨.privateRow 5 30, 156906848707456683202026660⟩, ⟨.privateRow 5 31, 253257328968695586241827120⟩, ⟨.privateRow 5 32, 251454997152307747159320960⟩, ⟨.privateRow 6 22, 844612857375465413289600⟩, ⟨.privateRow 6 23, 2822332789398539222605800⟩, ⟨.privateRow 6 24, 8228427972919505101951200⟩, ⟨.privateRow 6 25, 16295933462232953142964350⟩, ⟨.privateRow 6 26, 27852932886764257891990800⟩, ⟨.privateRow 6 27, 43221753498891185989570800⟩, ⟨.privateRow 6 28, 61945478332674541253288640⟩, ⟨.privateRow 6 29, 100105038123499384005630600⟩, ⟨.privateRow 6 30, 110552620905308011654224000⟩, ⟨.privateRow 6 31, 40012306483195558452540600⟩, ⟨.privateRow 7 19, 42381736403187486301920⟩, ⟨.privateRow 7 20, 402418742220461573366760⟩, ⟨.privateRow 7 21, 1685297282856161220005760⟩, ⟨.privateRow 7 22, 4064159216733896480552352⟩, ⟨.privateRow 7 23, 7493811208597588672717920⟩, ⟨.privateRow 7 24, 12404760288715302056869320⟩, ⟨.privateRow 7 25, 19017468652010115964762800⟩, ⟨.privateRow 7 26, 27145709919851404522881240⟩, ⟨.privateRow 7 27, 43911717087342554557419312⟩, ⟨.privateRow 7 28, 41686800578341103254469400⟩, ⟨.privateRow 8 17, 9002656425513681730800⟩, ⟨.privateRow 8 18, 282129402134944149009840⟩, ⟨.privateRow 8 19, 1013549069239082001525900⟩, ⟨.privateRow 8 20, 2226275091698392458556560⟩, ⟨.privateRow 8 21, 3955047020856670657975056⟩, ⟨.privateRow 8 22, 6377481811833892138098720⟩, ⟨.privateRow 8 23, 9616637593733714824840560⟩, ⟨.privateRow 8 24, 13637223953368125085815840⟩, ⟨.privateRow 8 25, 22024998945019222354402200⟩, ⟨.privateRow 9 16, 213362957284674257019960⟩, ⟨.privateRow 9 17, 689326477381255291910640⟩, ⟨.privateRow 9 18, 1437874275428293533770940⟩, ⟨.privateRow 9 19, 2493244775880443638609920⟩, ⟨.privateRow 9 20, 3932360326664376180013440⟩, ⟨.privateRow 9 21, 5828519828909235634336160⟩, ⟨.privateRow 9 22, 7070686356598445631370320⟩, ⟨.privateRow 10 14, 180413234767294181885232⟩, ⟨.privateRow 10 15, 559064964024399635482680⟩, ⟨.privateRow 10 16, 1139320796250393014116320⟩, ⟨.privateRow 10 17, 1947274584838609358372040⟩, ⟨.privateRow 10 18, 3024401504985750860727120⟩, ⟨.privateRow 10 19, 871817248246744938810672⟩, ⟨.privateRow 11 12, 178927796457084424399650⟩, ⟨.privateRow 11 13, 558164698381848267309600⟩, ⟨.privateRow 11 14, 1140122131602554122050600⟩, ⟨.privateRow 11 15, 839324583670967865979200⟩, ⟨.privateRow 12 10, 213204086877165192048240⟩, ⟨.privateRow 12 11, 701869601574110411937495⟩, ⟨.privateRow 12 12, 15844675308904079846208⟩, ⟨.privateRow 13 8, 306990584110016547020280⟩, ⟨.privateRow 14 6, 81308202243060409737120⟩, ⟨.hall 4 33, 62577147072930583580847360⟩, ⟨.hall 3 34, 263773100442458604662615808⟩, ⟨.assumptionRow 20, 132923828090496661218⟩]
  caps := #[0, 0, 7317419831156783549112912, 0, 34182593346596419478754, 536895675965551239013248, 76424666153700097944900, 0, 0, 157658701924781230522720, 153822972306200512284396, 3105536985938900142630, 758600463608089628526, 132923828090496661218, 3538908021529251407620584, 8270547086266720107760908, 2501090680587217134466050] }

theorem case_54_38_20_checked :
    (Witness.linear .conditional case_54_38_20).check 54 38 20 = true := by
  change case_54_38_20.check 54 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_21 : Certificate := {
  objectiveScale := 320817154980722400000
  eta := 632050733029969348648672719600
  rows := #[⟨.count 2, 63953942172706082003648581440⟩, ⟨.count 3, 5807113112401617523834847520⟩, ⟨.count 4, 462030732007642968315425280⟩, ⟨.count 5, 27629152569901489231825200⟩, ⟨.count 6, 972286893955477626926400⟩, ⟨.path 5, 10663514365266070538630400⟩, ⟨.path 6, 799318041671616240533760⟩, ⟨.privateRow 2 35, 5534059842218859902835164280⟩, ⟨.privateRow 2 36, 9446021049688664631414784560⟩, ⟨.privateRow 3 31, 301401374894800632854530128⟩, ⟨.privateRow 3 32, 952017413013433572509503800⟩, ⟨.privateRow 3 33, 2155073900452316160082365600⟩, ⟨.privateRow 3 34, 2915529188981099407251214680⟩, ⟨.privateRow 3 35, 4863978620483238301089124080⟩, ⟨.privateRow 4 28, 88184106312966688672636560⟩, ⟨.privateRow 4 29, 166992974833780936529128440⟩, ⟨.privateRow 4 30, 435114589826642162676679440⟩, ⟨.privateRow 4 31, 693580855803139965167947440⟩, ⟨.privateRow 4 32, 1035588172345834528648347120⟩, ⟨.privateRow 4 33, 1640369525964635191328202600⟩, ⟨.privateRow 5 24, 1348777985670459796908456⟩, ⟨.privateRow 5 25, 15065645439549629253769440⟩, ⟨.privateRow 5 26, 33741731216414641284995130⟩, ⟨.privateRow 5 27, 84041855482210336369985040⟩, ⟨.privateRow 5 28, 157911995297365285767270480⟩, ⟨.privateRow 5 29, 250955889880077268644165408⟩, ⟨.privateRow 5 30, 374716668133513423312915320⟩, ⟨.privateRow 5 31, 629409920802078441790805040⟩, ⟨.privateRow 5 32, 663812672066536425156884160⟩, ⟨.privateRow 6 21, 384863562190709893991700⟩, ⟨.privateRow 6 22, 2330051167585222898871600⟩, ⟨.privateRow 6 23, 6233439309025673230405920⟩, ⟨.privateRow 6 24, 17708225188985411964483600⟩, ⟨.privateRow 6 25, 35282535863641307913221550⟩, ⟨.privateRow 6 26, 61705493234245847966007600⟩, ⟨.privateRow 6 27, 98547578561885517066202200⟩, ⟨.privateRow 6 28, 146442611011260855242231280⟩, ⟨.privateRow 6 29, 247784614127625819117673800⟩, ⟨.privateRow 6 30, 293171506496853045563502000⟩, ⟨.privateRow 6 31, 173796282294541625813094000⟩, ⟨.privateRow 7 18, 72921517046660822019480⟩, ⟨.privateRow 7 19, 387668235923273771761680⟩, ⟨.privateRow 7 20, 1108677138802009905148020⟩, ⟨.privateRow 7 21, 3691743873109737777390240⟩, ⟨.privateRow 7 22, 8633907618324641327106432⟩, ⟨.privateRow 7 23, 15997720468137812435631600⟩, ⟨.privateRow 7 24, 27017422065787834558217340⟩, ⟨.privateRow 7 25, 42660244956694146926189760⟩, ⟨.privateRow 7 26, 63252664045659127840600800⟩, ⟨.privateRow 7 27, 107298340660613325982174416⟩, ⟨.privateRow 7 28, 135986475705847989595993620⟩, ⟨.privateRow 7 29, 21222862257505953312187920⟩, ⟨.privateRow 8 15, 14179183870184048726010⟩, ⟨.privateRow 8 16, 73941818108219039282304⟩, ⟨.privateRow 8 17, 221465348067636570577680⟩, ⟨.privateRow 8 18, 780461060888763023893200⟩, ⟨.privateRow 8 19, 2204600514334542094510740⟩, ⟨.privateRow 8 20, 4690875051679474382568480⟩, ⟨.privateRow 8 21, 8334839371869076820009256⟩, ⟨.privateRow 8 22, 13659630564916070249234720⟩, ⟨.privateRow 8 23, 21166370588435854959327150⟩, ⟨.privateRow 8 24, 31114981137860386797990960⟩, ⟨.privateRow 8 25, 52769670815243479710532920⟩, ⟨.privateRow 8 26, 33200716578523396581382704⟩, ⟨.privateRow 9 12, 3501033054366431784200⟩, ⟨.privateRow 9 13, 17793485641015276832640⟩, ⟨.privateRow 9 14, 54353538169038853449705⟩, ⟨.privateRow 9 15, 193257024601027034487840⟩, ⟨.privateRow 9 16, 593275058441351626059720⟩, ⟨.privateRow 9 17, 1514385313177947631454880⟩, ⟨.privateRow 9 18, 3022791939139977202478280⟩, ⟨.privateRow 9 19, 5211064908411883119668160⟩, ⟨.privateRow 9 20, 8303330074379778933951456⟩, ⟨.privateRow 9 21, 12577111144505969541560080⟩, ⟨.privateRow 9 22, 18232854992182221767345970⟩, ⟨.privateRow 9 23, 13975723834967439518893920⟩, ⟨.privateRow 10 9, 810239078296231355772⟩, ⟨.privateRow 10 10, 5117299441870934878560⟩, ⟨.privateRow 10 11, 17105047208475995288520⟩, ⟨.privateRow 10 12, 61959458928535338970800⟩, ⟨.privateRow 10 13, 192431781095354946995850⟩, ⟨.privateRow 10 14, 536918429217635978424912⟩, ⟨.privateRow 10 15, 1260500508949422780622440⟩, ⟨.privateRow 10 16, 2412019410004934882182800⟩, ⟨.privateRow 10 17, 3226101930082827848232180⟩, ⟨.privateRow 10 18, 7988957312000841167911920⟩, ⟨.privateRow 10 19, 7509295777649472205294896⟩, ⟨.privateRow 11 7, 2572187550146766208800⟩, ⟨.privateRow 11 8, 6751992319135261298100⟩, ⟨.privateRow 11 9, 25586497209354674392800⟩, ⟨.privateRow 11 10, 82524350567208749199000⟩, ⟨.privateRow 11 11, 235128203113416158145600⟩, ⟨.privateRow 11 12, 600927316403038255530900⟩, ⟨.privateRow 11 13, 1069515583351025389619040⟩, ⟨.privateRow 11 14, 2963160057769074672537600⟩, ⟨.privateRow 11 15, 3400926592745976229227600⟩, ⟨.privateRow 12 5, 2700796927654104519240⟩, ⟨.privateRow 12 6, 14147031525807214148400⟩, ⟨.privateRow 12 7, 47534025926712239538624⟩, ⟨.privateRow 12 8, 137598496103640693401280⟩, ⟨.privateRow 12 9, 264077921815067997436800⟩, ⟨.privateRow 12 10, 1059030136455427101485520⟩, ⟨.privateRow 12 11, 1452015948230037942156405⟩, ⟨.privateRow 13 3, 7750112922833517316080⟩, ⟨.privateRow 13 4, 32409563131849254230880⟩, ⟨.privateRow 13 5, 110346845901296270357520⟩, ⟨.privateRow 13 6, 294116785421531982145236⟩, ⟨.privateRow 13 7, 562902938605802836641600⟩, ⟨.privateRow 14 2, 235086758659283358587760⟩, ⟨.privateRow 14 3, 105331080178510076250360⟩, ⟨.hall 4 33, 188968723952472348742297440⟩, ⟨.hall 3 34, 687902237348680949408779680⟩, ⟨.assumptionRow 21, 137869453689635197530⟩]
  caps := #[0, 59390518205622220045048620, 0, 0, 331813019218361576485590, 41027149570477930878876, 152749010955462355059210, 148427003341687613967108, 4528146967759829001588, 0, 196188697601546010673950, 135573080694470519080200, 1291685487138919552680, 3635959607857342944157122, 0, 36986703425364907780626060, 12866592285591124927776930] }

theorem case_54_38_21_checked :
    (Witness.linear .conditional case_54_38_21).check 54 38 21 = true := by
  change case_54_38_21.check 54 38 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_22 : Certificate := {
  objectiveScale := 1024458141955248000000
  eta := 3075904536142895874182075310000
  rows := #[⟨.count 2, 306684781876554698279248185600⟩, ⟨.count 3, 27065874362669949193292505600⟩, ⟨.count 4, 2053469920033968748068556800⟩, ⟨.count 5, 111407873265731811418650000⟩, ⟨.count 6, 2430717234888694067316000⟩, ⟨.path 5, 58530542306715956196720000⟩, ⟨.path 6, 2696961279038109187104000⟩, ⟨.privateRow 2 36, 108815783414415784606309410000⟩, ⟨.privateRow 3 31, 1320851745438516356179514400⟩, ⟨.privateRow 3 32, 4542841712198990830281151500⟩, ⟨.privateRow 3 34, 31036153878198589000756075200⟩, ⟨.privateRow 4 28, 386935459262353114172888400⟩, ⟨.privateRow 4 29, 749255083669801675727560800⟩, ⟨.privateRow 4 30, 2050083120686690501001429840⟩, ⟨.privateRow 4 32, 9576323698260264558050037600⟩, ⟨.privateRow 4 33, 7849798750303463432558079000⟩, ⟨.privateRow 5 24, 7783696745499129224449680⟩, ⟨.privateRow 5 25, 65260256428548678866569200⟩, ⟨.privateRow 5 26, 146352809513416356266966550⟩, ⟨.privateRow 5 27, 373821161037929826657321600⟩, ⟨.privateRow 5 28, 734301671347023450372702000⟩, ⟨.privateRow 5 30, 3233353569833579118866339400⟩, ⟨.privateRow 5 31, 3670022918424907494377928000⟩, ⟨.privateRow 6 20, 103876804909773250740000⟩, ⟨.privateRow 6 21, 2408210593824909862989000⟩, ⟨.privateRow 6 22, 10508555318508697583952000⟩, ⟨.privateRow 6 23, 26724385599137364217879800⟩, ⟨.privateRow 6 24, 76012429086087186080388000⟩, ⟨.privateRow 6 25, 155042623628143437557621250⟩, ⟨.privateRow 6 26, 280747840629644164774998000⟩, ⟨.privateRow 6 27, 354434583472473649741596000⟩, ⟨.privateRow 6 28, 389589956814104576900370000⟩, ⟨.privateRow 6 29, 1776482939126082923836600500⟩, ⟨.privateRow 6 30, 1732741282218618322727076000⟩, ⟨.privateRow 7 17, 43212750842465672307840⟩, ⟨.privateRow 7 18, 555592510831701501100800⟩, ⟨.privateRow 7 19, 2000667262562232809252400⟩, ⟨.privateRow 7 20, 4996474316160093360594000⟩, ⟨.privateRow 7 21, 15748101358157660351277600⟩, ⟨.privateRow 7 22, 36760546982300016611375640⟩, ⟨.privateRow 7 23, 69401478384284972462737200⟩, ⟨.privateRow 7 24, 120664854735266254658345100⟩, ⟨.privateRow 7 25, 186748532703305667057506400⟩, ⟨.privateRow 7 26, 264083923586018339891287200⟩, ⟨.privateRow 7 27, 394942936324715012057503680⟩, ⟨.privateRow 7 28, 992927734475074120714691700⟩, ⟨.privateRow 7 29, 998052496645297784039949600⟩, ⟨.privateRow 8 14, 14827904700846064027200⟩, ⟨.privateRow 8 15, 137853176515678251502875⟩, ⟨.privateRow 8 16, 478941321837327868078560⟩, ⟨.privateRow 8 17, 1161342678891264943273200⟩, ⟨.privateRow 8 18, 3524193734572240486772400⟩, ⟨.privateRow 8 19, 9374016003066121102195500⟩, ⟨.privateRow 8 20, 19850857418257668216414000⟩, ⟨.privateRow 8 21, 35718939633868083635122080⟩, ⟨.privateRow 8 22, 59874667295774716373388400⟩, ⟨.privateRow 8 23, 94598788387244578417030050⟩, ⟨.privateRow 8 24, 140954591654267714859135600⟩, ⟨.privateRow 8 25, 236939414020357003859303400⟩, ⟨.privateRow 8 27, 1117083369239333305464154500⟩, ⟨.privateRow 9 11, 6633536313536397064800⟩, ⟨.privateRow 9 12, 42012396652397181410400⟩, ⟨.privateRow 9 13, 148279047008460640272000⟩, ⟨.privateRow 9 16, 5829220035520108920693000⟩, ⟨.privateRow 9 17, 4711851870707314653566400⟩, ⟨.privateRow 9 18, 12756013933584094205732700⟩, ⟨.privateRow 9 19, 22119526837487116012575600⟩, ⟨.privateRow 9 21, 88387080490534936823913200⟩, ⟨.privateRow 9 22, 124083613512855075295616400⟩, ⟨.privateRow 9 23, 103773620616896209310931600⟩, ⟨.privateRow 9 25, 464938590033083887514473680⟩, ⟨.privateRow 9 28, 402090145260930323983585800⟩, ⟨.privateRow 10 8, 3858281325220149313200⟩, ⟨.privateRow 10 9, 16204781565924627115440⟩, ⟨.privateRow 10 10, 55437410620268461184400⟩, ⟨.privateRow 10 11, 148543831020975748558200⟩, ⟨.privateRow 10 14, 5007277503870709778670960⟩, ⟨.privateRow 10 15, 5069781661339276197544800⟩, ⟨.privateRow 10 16, 9442401566298388492266000⟩, ⟨.privateRow 10 17, 17143308498284428435875900⟩, ⟨.privateRow 10 18, 16705656632507751953553600⟩, ⟨.privateRow 10 19, 14568098627766239776780560⟩, ⟨.privateRow 10 20, 92070167263728423060891600⟩, ⟨.privateRow 10 21, 147949655696891845563967200⟩, ⟨.privateRow 10 22, 112368585315711628597636800⟩, ⟨.privateRow 11 6, 6138174835577510271000⟩, ⟨.privateRow 11 7, 25721875501467662088000⟩, ⟨.privateRow 11 8, 74271915510487874279100⟩, ⟨.privateRow 11 9, 220328170413887473938000⟩, ⟨.privateRow 11 12, 5004914306559012437216625⟩, ⟨.privateRow 11 13, 6724984349858720252907600⟩, ⟨.privateRow 11 14, 9684286126302574776132000⟩, ⟨.privateRow 11 15, 16485248939181014892438000⟩, ⟨.privateRow 11 16, 22878000641336643698395500⟩, ⟨.privateRow 11 17, 22330680051830982365898000⟩, ⟨.privateRow 11 18, 20282984926682324939492400⟩, ⟨.privateRow 11 19, 139586187877589635236054000⟩, ⟨.privateRow 11 20, 192887540576896577133471750⟩, ⟨.privateRow 12 4, 12916854871389195526800⟩, ⟨.privateRow 12 5, 54015938553082090384800⟩, ⟨.privateRow 12 6, 155617346783879355632400⟩, ⟨.privateRow 12 7, 401068343756634521107140⟩, ⟨.privateRow 12 8, 46908578217150236386800⟩, ⟨.privateRow 12 10, 5994180475317021382995600⟩, ⟨.privateRow 12 11, 10732291791265497833329950⟩, ⟨.privateRow 12 12, 14478072063511102959472560⟩, ⟨.privateRow 12 13, 21538855498041483540939000⟩, ⟨.privateRow 12 14, 32313996471332262840199200⟩, ⟨.privateRow 12 16, 123156339901027166077344000⟩, ⟨.privateRow 12 18, 252227425073616821051823600⟩, ⟨.privateRow 13 1, 35650519445034179653968⟩, ⟨.privateRow 13 2, 37135957755243937139550⟩, ⟨.privateRow 13 3, 155002258456670346321600⟩, ⟨.privateRow 13 4, 364607585233304110097400⟩, ⟨.privateRow 13 5, 933704080703276133794400⟩, ⟨.privateRow 13 6, 267378895837756347404760⟩, ⟨.privateRow 13 8, 792233765445203992310400⟩, ⟨.privateRow 13 9, 36961200306983965670658000⟩, ⟨.privateRow 13 10, 22058758906614898660892700⟩, ⟨.privateRow 13 11, 40819844764564135703793360⟩, ⟨.privateRow 13 12, 58059417381912806865033600⟩, ⟨.privateRow 13 13, 69312836844095299288772400⟩, ⟨.privateRow 13 15, 329524233143077292392472400⟩, ⟨.privateRow 13 17, 555058781915046047112474000⟩, ⟨.privateRow 14 1, 1126457385242399426566350⟩, ⟨.privateRow 14 2, 839595566640297709242000⟩, ⟨.privateRow 14 3, 2984380605057785493760200⟩, ⟨.privateRow 14 5, 3669032626218100989387540⟩, ⟨.privateRow 14 8, 242633241164144387409652800⟩, ⟨.privateRow 14 9, 37173093712999181076689550⟩, ⟨.privateRow 14 10, 162724815422444900020556160⟩, ⟨.privateRow 14 12, 593878236421861042735683600⟩, ⟨.privateRow 14 14, 1117562760693991909016319600⟩, ⟨.privateRow 14 19, 4277963304183420907977121200⟩, ⟨.privateRow 15 1, 39964748972078170959919200⟩, ⟨.privateRow 15 3, 6436899344242282437522000⟩, ⟨.privateRow 15 5, 22766296628056914726393600⟩, ⟨.privateRow 15 6, 3003886360646398470843600⟩, ⟨.privateRow 15 15, 29690412788629002485818142400⟩, ⟨.privateRow 16 1, 976945768655680957222089000⟩, ⟨.privateRow 16 5, 22529147704847988531327000⟩, ⟨.hall 12 5, 934891244187959256660⟩, ⟨.hall 12 7, 2390069789489217577896⟩, ⟨.hall 10 9, 17733156795250204860⟩, ⟨.hall 11 9, 39046902715130631552⟩, ⟨.hall 14 16, 81971959816462127412000⟩, ⟨.hall 11 21, 7827393251123880024360⟩, ⟨.hall 12 21, 14660178640744520517480⟩, ⟨.hall 5 22, 17083660397025198900⟩, ⟨.hall 6 26, 427386557623107010500⟩, ⟨.hall 3 30, 137060319226590673223310⟩, ⟨.hall 2 33, 18924484072072310366314680⟩]
  caps := #[0, 117704734003682628330528000, 0, 2333382473042481875414400, 2060231705605785274580160, 280251054413254965902400, 266244044149415119788000, 2788431638262311321280, 2167451746274750021549155, 10455716760859749659280, 0, 366523032379088304573750, 6559881367027186045767348, 0, 42448275928284040417402800, 0, 0] }

theorem case_54_38_22_checked :
    (Witness.linear .conditional case_54_38_22).check 54 38 22 = true := by
  change case_54_38_22.check 54 38 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_23 : Certificate := {
  objectiveScale := 210035268568125000
  eta := 562901780011712879241504000
  rows := #[⟨.count 2, 54821157934711301762428800⟩, ⟨.count 3, 4632421232302797271338000⟩, ⟨.count 4, 312588685470506545900800⟩, ⟨.count 5, 13299694657635988602000⟩, ⟨.path 5, 13325256613560331440000⟩, ⟨.privateRow 2 35, 5997107487224432143164600⟩, ⟨.privateRow 2 36, 12461630450140678065058800⟩, ⟨.privateRow 3 31, 162403030074553664956560⟩, ⟨.privateRow 3 35, 25062770111138351569177200⟩, ⟨.privateRow 4 28, 45166549246178574099600⟩, ⟨.privateRow 4 29, 111900879188385559272000⟩, ⟨.privateRow 4 30, 234331447664333956416480⟩, ⟨.privateRow 5 24, 504471176668951291800⟩, ⟨.privateRow 5 25, 7470249949461440341200⟩, ⟨.privateRow 5 26, 18046309819930212120300⟩, ⟨.privateRow 5 27, 55321488516787333869600⟩, ⟨.privateRow 5 28, 104670125656130590756200⟩, ⟨.privateRow 5 29, 165374823915294396202800⟩, ⟨.privateRow 5 32, 2631092352424945869259800⟩, ⟨.privateRow 6 19, 2977988055896997000⟩, ⟨.privateRow 6 20, 16035320300983830000⟩, ⟨.privateRow 6 21, 163293011731685335500⟩, ⟨.privateRow 6 22, 1042295819563948950000⟩, ⟨.privateRow 6 23, 2955950944283359222200⟩, ⟨.privateRow 6 24, 9315808413969339282000⟩, ⟨.privateRow 6 25, 22518801181679117064750⟩, ⟨.privateRow 6 26, 42418461868196825268000⟩, ⟨.privateRow 6 27, 75830495192675832609000⟩, ⟨.privateRow 6 28, 132980269843246862836800⟩, ⟨.privateRow 6 30, 652435491214249484742000⟩, ⟨.privateRow 7 16, 1563443729345923425⟩, ⟨.privateRow 7 17, 5003019933906954960⟩, ⟨.privateRow 7 18, 37522649504302162200⟩, ⟨.privateRow 7 19, 167408743942271185200⟩, ⟨.privateRow 7 20, 479456076999416517000⟩, ⟨.privateRow 7 21, 1703300877498322393200⟩, ⟨.privateRow 7 22, 4437678681375469049520⟩, ⟨.privateRow 7 23, 9703079216260655425200⟩, ⟨.privateRow 7 24, 18135947260412711730000⟩, ⟨.privateRow 7 25, 32319508773038929041600⟩, ⟨.privateRow 7 26, 56046330809592662939400⟩, ⟨.privateRow 7 27, 116940587935141165235040⟩, ⟨.privateRow 7 28, 89522787942347575315500⟩, ⟨.privateRow 7 29, 333351218196220408984800⟩, ⟨.privateRow 7 30, 286597996913859914883600⟩, ⟨.privateRow 8 14, 2288963368454162400⟩, ⟨.privateRow 8 15, 9728094315930190200⟩, ⟨.privateRow 8 16, 36318218779472710080⟩, ⟨.privateRow 8 17, 94501487640464704800⟩, ⟨.privateRow 8 18, 332251836636384957600⟩, ⟨.privateRow 8 19, 998751016435499527200⟩, ⟨.privateRow 8 20, 2343586357928636730000⟩, ⟨.privateRow 8 21, 4762874977079421121920⟩, ⟨.privateRow 8 22, 8712048909599703668000⟩, ⟨.privateRow 8 23, 15134482732008393403650⟩, ⟨.privateRow 8 24, 25573770228821051437200⟩, ⟨.privateRow 8 25, 52538194702233647206800⟩, ⟨.privateRow 8 27, 279804312761942095627500⟩, ⟨.privateRow 8 28, 90743663778996814185600⟩, ⟨.privateRow 8 29, 198443395950659949889800⟩, ⟨.privateRow 9 11, 1024009927992651600⟩, ⟨.privateRow 9 12, 3242698105310063400⟩, ⟨.privateRow 9 13, 10300335158043730800⟩, ⟨.privateRow 9 14, 26752259368808023050⟩, ⟨.privateRow 9 15, 83013071495937623040⟩, ⟨.privateRow 9 16, 251540724454766346600⟩, ⟨.privateRow 9 17, 676476712430837841600⟩, ⟨.privateRow 9 18, 1465699543600148656800⟩, ⟨.privateRow 9 19, 2808766140672207643200⟩, ⟨.privateRow 9 20, 4967164957713955116120⟩, ⟨.privateRow 9 21, 8353190319278723318400⟩, ⟨.privateRow 9 22, 13638788230934126660400⟩, ⟨.privateRow 9 23, 27041322742767091558800⟩, ⟨.privateRow 9 25, 116702110651624933715280⟩, ⟨.privateRow 9 26, 112004413906462244867700⟩, ⟨.privateRow 10 9, 1250754983476738740⟩, ⟨.privateRow 10 10, 3949752579400227600⟩, ⟨.privateRow 10 11, 11117822075348788800⟩, ⟨.privateRow 10 12, 30901005474131192400⟩, ⟨.privateRow 10 13, 82862517655333941525⟩, ⟨.privateRow 10 14, 228471243648417609840⟩, ⟨.privateRow 10 15, 557479364063917838400⟩, ⟨.privateRow 10 16, 1137224915745773223600⟩, ⟨.privateRow 10 17, 2078337864210514206300⟩, ⟨.privateRow 10 18, 3540773653224149487600⟩, ⟨.privateRow 10 19, 5750971414026044726520⟩, ⟨.privateRow 10 20, 9052686624852751280400⟩, ⟨.privateRow 10 21, 17041536649870565332500⟩, ⟨.privateRow 10 22, 29753674264078076426400⟩, ⟨.privateRow 10 24, 106239128296514188575600⟩, ⟨.privateRow 10 25, 111629882275298932545000⟩, ⟨.privateRow 11 6, 1895083308298089000⟩, ⟨.privateRow 11 7, 1985325370597998000⟩, ⟨.privateRow 11 8, 6253774917383693700⟩, ⟨.privateRow 11 9, 15360148919889774000⟩, ⟨.privateRow 11 10, 34743193985464965000⟩, ⟨.privateRow 11 11, 78478744061285568000⟩, ⟨.privateRow 11 12, 190218987070420683375⟩, ⟨.privateRow 11 13, 419697783344416777200⟩, ⟨.privateRow 11 14, 786188846756807208000⟩, ⟨.privateRow 11 15, 1305275072500083762000⟩, ⟨.privateRow 11 16, 1994259334765688991000⟩, ⟨.privateRow 11 17, 2872946295379902924000⟩, ⟨.privateRow 11 18, 3964893297621261805800⟩, ⟨.privateRow 11 19, 7629605399208106314000⟩, ⟨.privateRow 11 20, 13450827551472761199750⟩, ⟨.privateRow 11 22, 35361622838406241377000⟩, ⟨.privateRow 11 23, 32828149132986136129200⟩, ⟨.privateRow 12 4, 3987914440070761200⟩, ⟨.privateRow 12 5, 4169183278255795800⟩, ⟨.privateRow 12 6, 13103147445946786800⟩, ⟨.privateRow 12 7, 27516609636488252280⟩, ⟨.privateRow 12 8, 57929704497870004800⟩, ⟨.privateRow 12 9, 127391711280038205000⟩, ⟨.privateRow 12 10, 291352337327522671200⟩, ⟨.privateRow 12 11, 624856343828587395525⟩, ⟨.privateRow 12 12, 1198501219722599432640⟩, ⟨.privateRow 12 13, 2083400443905539101200⟩, ⟨.privateRow 12 14, 3393715188500217781200⟩, ⟨.privateRow 12 15, 5312234360377593148500⟩, ⟨.privateRow 12 17, 29341878075708639681240⟩, ⟨.privateRow 12 18, 14563420433533967595600⟩, ⟨.privateRow 12 20, 103737618329560711095600⟩, ⟨.privateRow 12 21, 39837935951493547467600⟩, ⟨.privateRow 12 24, 545042888877417859328400⟩, ⟨.privateRow 13 4, 100060398678139099200⟩, ⟨.privateRow 13 5, 13103147445946786800⟩, ⟨.privateRow 13 6, 123824743364197135260⟩, ⟨.privateRow 13 7, 260683670240415021600⟩, ⟨.privateRow 13 9, 2266073734769620776000⟩, ⟨.privateRow 13 11, 6695708344878808054800⟩, ⟨.privateRow 13 14, 31139629905292538830200⟩, ⟨.privateRow 13 18, 213253724682783955170000⟩, ⟨.privateRow 13 24, 380279545176267646509600⟩, ⟨.privateRow 14 3, 758791356642554835600⟩, ⟨.privateRow 14 4, 56780305599102742800⟩, ⟨.privateRow 14 5, 775051171427752439220⟩, ⟨.privateRow 14 6, 439300259108847536400⟩, ⟨.privateRow 14 7, 3775890322340332396200⟩, ⟨.privateRow 14 8, 5260528312858048230000⟩, ⟨.privateRow 14 12, 825498289094647568400⟩, ⟨.privateRow 14 14, 259506643971753753775200⟩, ⟨.privateRow 14 17, 149048302197644699850⟩, ⟨.privateRow 14 18, 511022750391924685200⟩, ⟨.privateRow 14 20, 2608226049817024131615120⟩, ⟨.privateRow 15 6, 77438873452909624055400⟩, ⟨.privateRow 15 13, 1427286541844645645763600⟩, ⟨.privateRow 15 14, 259582523107418009258760⟩, ⟨.privateRow 15 17, 1192386417581157598800⟩, ⟨.privateRow 15 19, 6528792590823870316469520⟩, ⟨.privateRow 15 21, 16298332479777649498797600⟩, ⟨.privateRow 16 5, 1126805164614193930866000⟩, ⟨.privateRow 16 12, 15661453601102331806784000⟩, ⟨.privateRow 16 13, 6873511504146582978282600⟩, ⟨.privateRow 16 14, 1043338115383512898950000⟩, ⟨.privateRow 16 21, 459861707736437145341202000⟩, ⟨.hall 14 8, 34046365892338800⟩, ⟨.hall 10 9, 201478231133535960⟩, ⟨.hall 12 9, 334209833641557720⟩, ⟨.hall 12 10, 650910107681341200⟩, ⟨.hall 15 14, 30335312010073870800⟩, ⟨.hall 14 15, 5553813436187766750⟩, ⟨.hall 13 16, 2667289579336942560⟩, ⟨.hall 7 23, 47224028195753640⟩, ⟨.hall 9 23, 168340144155922200⟩, ⟨.hall 13 23, 4757621806148818819212⟩, ⟨.hall 11 24, 47298255880383415600⟩, ⟨.hall 6 25, 142885839166958250⟩, ⟨.hall 10 27, 2814198712822662165000⟩, ⟨.hall 4 29, 27832265068750882740⟩, ⟨.hall 3 34, 5449035587429092918287600⟩]
  caps := #[0, 0, 15607451121393590058600, 404258605478584857000, 1434368033085651515280, 50939708120302230900, 74432267493746041950, 273480929976888222120, 1325189318578725600, 65681020745157175155, 495442125927364187025, 935057585050501412250, 41898997169055140400, 420940732249810978920, 21506422644033567867198, 0, 0] }

theorem case_54_38_23_checked :
    (Witness.linear .conditional case_54_38_23).check 54 38 23 = true := by
  change case_54_38_23.check 54 38 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876, 177650] }

theorem case_54_38_24_checked :
    (Witness.linear .negative case_54_38_24).check 54 38 24 = true := by
  change case_54_38_24.check 54 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_39_1_checked :
    (Witness.rising).check 54 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_39_2_checked :
    (Witness.rising).check 54 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_39_3_checked :
    (Witness.rising).check 54 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_39_4_checked :
    (Witness.rising).check 54 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_39_5_checked :
    (Witness.rising).check 54 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_39_6_checked :
    (Witness.rising).check 54 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_39_7_checked :
    (Witness.rising).check 54 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_39_8_checked :
    (Witness.rising).check 54 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_39_9_checked :
    (Witness.rising).check 54 39 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_54_39_10_checked :
    (Witness.linear .positive case_54_39_10).check 54 39 10 = true := by
  change case_54_39_10.check 54 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_54_39_11_checked :
    (Witness.linear .positive case_54_39_11).check 54 39 11 = true := by
  change case_54_39_11.check 54 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_54_39_12_checked :
    (Witness.linear .positive case_54_39_12).check 54 39 12 = true := by
  change case_54_39_12.check 54 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_54_39_13_checked :
    (Witness.linear .positive case_54_39_13).check 54 39 13 = true := by
  change case_54_39_13.check 54 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_54_39_14_checked :
    (Witness.linear .positive case_54_39_14).check 54 39 14 = true := by
  change case_54_39_14.check 54 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_54_39_15_checked :
    (Witness.linear .positive case_54_39_15).check 54 39 15 = true := by
  change case_54_39_15.check 54 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_54_39_16_checked :
    (Witness.linear .positive case_54_39_16).check 54 39 16 = true := by
  change case_54_39_16.check 54 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_54_39_17_checked :
    (Witness.linear .positive case_54_39_17).check 54 39 17 = true := by
  change case_54_39_17.check 54 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_54_39_18_checked :
    (Witness.linear .positive case_54_39_18).check 54 39 18 = true := by
  change case_54_39_18.check 54 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_19 : Certificate := {
  objectiveScale := 999
  eta := 40875947760
  rows := #[⟨.assumptionRow 19, 1748⟩]
  caps := #[0, 0, 11625259725, 3333040515, 964321345, 281885976, 83374698, 24996970, 7613892, 2362776, 1430715, 431730585, 295861995, 139683830, 53086990, 16809826] }

theorem case_54_39_19_checked :
    (Witness.linear .conditional case_54_39_19).check 54 39 19 = true := by
  change case_54_39_19.check 54 39 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_20 : Certificate := {
  objectiveScale := 211347656465400000
  eta := 878604599631189687777480960
  rows := #[⟨.count 2, 71006350398314563921328640⟩, ⟨.count 3, 5091461928046147241427840⟩, ⟨.count 4, 287653216273793629459200⟩, ⟨.count 5, 13844272440984720134400⟩, ⟨.count 6, 922951496065648008960⟩, ⟨.path 4, 88378913401040165904000⟩, ⟨.path 5, 7388586206839226188800⟩, ⟨.privateRow 2 36, 5521249674714050664266880⟩, ⟨.privateRow 2 37, 8589832661258313882056640⟩, ⟨.privateRow 3 32, 550263681954339342941952⟩, ⟨.privateRow 3 33, 1033013461971476534028480⟩, ⟨.privateRow 3 34, 2170371718081486051292160⟩, ⟨.privateRow 3 35, 2620182384705702560103360⟩, ⟨.privateRow 3 36, 3961153995864416979788160⟩, ⟨.privateRow 4 28, 29082586204151929449000⟩, ⟨.privateRow 4 29, 129323084627293774588800⟩, ⟨.privateRow 4 30, 216021925162476392319360⟩, ⟨.privateRow 4 31, 485710916067014478448608⟩, ⟨.privateRow 4 32, 703481321563704126162720⟩, ⟨.privateRow 4 33, 952780775667658605027360⟩, ⟨.privateRow 4 34, 1352604645640375191464400⟩, ⟨.privateRow 5 25, 8983394561705640620544⟩, ⟨.privateRow 5 26, 25244432586832631652480⟩, ⟨.privateRow 5 27, 48628006948958829472080⟩, ⟨.privateRow 5 28, 110292703779844937070720⟩, ⟨.privateRow 5 29, 182872583928785201330880⟩, ⟨.privateRow 5 30, 264610193922021284168832⟩, ⟨.privateRow 5 31, 355951626982651582122240⟩, ⟨.privateRow 5 32, 531876437149387044274560⟩, ⟨.privateRow 5 33, 436248407140362958901760⟩, ⟨.privateRow 6 22, 1794627909016537795200⟩, ⟨.privateRow 6 23, 5425836067779870113280⟩, ⟨.privateRow 6 24, 10790841241500867971424⟩, ⟨.privateRow 6 25, 27064698037406548559040⟩, ⟨.privateRow 6 26, 48791446276387121307000⟩, ⟨.privateRow 6 27, 76495098995345731409280⟩, ⟨.privateRow 6 28, 110536260424640038628640⟩, ⟨.privateRow 6 29, 147533796646093834232256⟩, ⟨.privateRow 6 30, 221046883307722698145920⟩, ⟨.privateRow 6 31, 118804367576894802042240⟩, ⟨.privateRow 7 19, 303987992751780891840⟩, ⟨.privateRow 7 20, 1250323180567565892480⟩, ⟨.privateRow 7 21, 2721852328675082322720⟩, ⟨.privateRow 7 22, 6959427190030366047360⟩, ⟨.privateRow 7 23, 14372405797066729828416⟩, ⟨.privateRow 7 24, 24156261378508318259200⟩, ⟨.privateRow 7 25, 36828328447175093468640⟩, ⟨.privateRow 7 26, 52439760002650588064640⟩, ⟨.privateRow 7 27, 69793933966371734159040⟩, ⟨.privateRow 7 28, 77599710785875094264448⟩, ⟨.privateRow 8 16, 53278016048928465795⟩, ⟨.privateRow 8 17, 296113604987728736208⟩, ⟨.privateRow 8 18, 788354402889407674320⟩, ⟨.privateRow 8 19, 2125943830681129388160⟩, ⟨.privateRow 8 20, 4639860906436507091340⟩, ⟨.privateRow 8 21, 8793676754181035196480⟩, ⟨.privateRow 8 22, 14204479899865896649008⟩, ⟨.privateRow 8 23, 21121773473619640661840⟩, ⟨.privateRow 8 24, 29588927649910166898360⟩, ⟨.privateRow 8 25, 22240567301026379104800⟩, ⟨.privateRow 9 13, 11394462914390716160⟩, ⟨.privateRow 9 14, 75404533992291504000⟩, ⟨.privateRow 9 15, 246761337489773946840⟩, ⟨.privateRow 9 16, 786217941092959415040⟩, ⟨.privateRow 9 17, 1845902992131296017920⟩, ⟨.privateRow 9 18, 3707582932913286873600⟩, ⟨.privateRow 9 19, 5546254823579681090880⟩, ⟨.privateRow 9 20, 12441199712117245130880⟩, ⟨.privateRow 9 21, 11941966857427190071488⟩, ⟨.privateRow 10 10, 3845631233606866704⟩, ⟨.privateRow 10 11, 24288197264885473920⟩, ⟨.privateRow 10 12, 85458471857930371200⟩, ⟨.privateRow 10 13, 325747586846699297280⟩, ⟨.privateRow 10 14, 918144457023639425580⟩, ⟨.privateRow 10 15, 1979218208229667396992⟩, ⟨.privateRow 10 16, 3735756055503813369600⟩, ⟨.privateRow 10 17, 5632370668298057080320⟩, ⟨.privateRow 11 8, 7325011873536888960⟩, ⟨.privateRow 11 9, 38456312336068667040⟩, ⟨.privateRow 11 10, 153825249344274668160⟩, ⟨.privateRow 11 11, 452929900847030967360⟩, ⟨.privateRow 11 12, 1483961228968296798720⟩, ⟨.privateRow 11 13, 2172781646987879687760⟩, ⟨.privateRow 12 6, 19228156168034333520⟩, ⟨.privateRow 12 7, 100718913261132223200⟩, ⟨.privateRow 12 8, 338415548557404269952⟩, ⟨.privateRow 12 9, 935095594698090745920⟩, ⟨.privateRow 13 4, 73568597512479189120⟩, ⟨.privateRow 13 5, 307650498688549336320⟩, ⟨.hall 4 34, 10104121378356784631424⟩, ⟨.hall 3 35, 376487297770112250321600⟩, ⟨.assumptionRow 20, 177583417919958960⟩]
  caps := #[0, 0, 21181727501152225207200, 510898048586099913024, 49204445473574388192, 607334381381225619264, 258667391259592007760, 179850384109397705472, 9006750287212532400, 411749365599212270224, 0, 18490113101762181360, 623007529062215517792, 9818905454761767043680, 42150132183358127728800, 13802424182759165073120] }

theorem case_54_39_20_checked :
    (Witness.linear .conditional case_54_39_20).check 54 39 20 = true := by
  change case_54_39_20.check 54 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_21 : Certificate := {
  objectiveScale := 355953947731200000
  eta := 1748124433861355857928100480
  rows := #[⟨.count 2, 138163223931788654271953280⟩, ⟨.count 3, 9446870037979940195710080⟩, ⟨.count 4, 482242156694301084681600⟩, ⟨.count 5, 13075146194263346793600⟩, ⟨.path 4, 198952437790244900361600⟩, ⟨.path 5, 11790902259171917481600⟩, ⟨.privateRow 2 36, 11146985150045199896881440⟩, ⟨.privateRow 2 37, 17784583115562987896652480⟩, ⟨.privateRow 3 32, 1037920487425558895942784⟩, ⟨.privateRow 3 33, 2005112125202620299465600⟩, ⟨.privateRow 3 34, 4362176420904941039681280⟩, ⟨.privateRow 3 35, 5455258642745356831626240⟩, ⟨.privateRow 3 36, 8512843123961504410642560⟩, ⟨.privateRow 4 28, 57689275543145009143380⟩, ⟨.privateRow 4 29, 236407433206529554295040⟩, ⟨.privateRow 4 30, 401022425040524059893120⟩, ⟨.privateRow 4 31, 936311218971198263889696⟩, ⟨.privateRow 4 32, 1411298592343299994534200⟩, ⟨.privateRow 4 33, 1988050341296184500855520⟩, ⟨.privateRow 4 34, 2948233957088536324288080⟩, ⟨.privateRow 5 24, 1342474903368215285760⟩, ⟨.privateRow 5 25, 17366870650968610035264⟩, ⟨.privateRow 5 26, 45241715001588338513280⟩, ⟨.privateRow 5 27, 86738212474002878508720⟩, ⟨.privateRow 5 28, 202412053101444852631680⟩, ⟨.privateRow 5 29, 349824254550437974507200⟩, ⟨.privateRow 5 30, 527128364452960432850688⟩, ⟨.privateRow 5 31, 742822129083502372544640⟩, ⟨.privateRow 5 32, 1171327998673536839815680⟩, ⟨.privateRow 5 33, 1061009657352134523633600⟩, ⟨.privateRow 6 21, 396395834848707798720⟩, ⟨.privateRow 6 22, 4108416034570002595440⟩, ⟨.privateRow 6 23, 9830831844456826519680⟩, ⟨.privateRow 6 24, 18812827994804791915968⟩, ⟨.privateRow 6 25, 47497818658637700312960⟩, ⟨.privateRow 6 26, 88497588763378020025800⟩, ⟨.privateRow 6 27, 144419934098653302735360⟩, ⟨.privateRow 6 28, 217880646925386377892960⟩, ⟨.privateRow 6 29, 305681535496942620567552⟩, ⟨.privateRow 6 30, 486895370486965393393440⟩, ⟨.privateRow 6 31, 435299818102739931781440⟩, ⟨.privateRow 7 18, 102550166229516445440⟩, ⟨.privateRow 7 19, 1003526626674553787520⟩, ⟨.privateRow 7 20, 2567698392900584845440⟩, ⟨.privateRow 7 21, 4849768277937548565600⟩, ⟨.privateRow 7 22, 11933110252161913651200⟩, ⟨.privateRow 7 23, 24888925343903641308288⟩, ⟨.privateRow 7 24, 43179317214083618888320⟩, ⟨.privateRow 7 25, 68388142104308779552800⟩, ⟨.privateRow 7 26, 101729764899680313876480⟩, ⟨.privateRow 7 27, 142373814115311998419200⟩, ⟨.privateRow 7 28, 227989529561460961502208⟩, ⟨.privateRow 7 29, 59645740433242502579040⟩, ⟨.privateRow 8 15, 34309062966492634320⟩, ⟨.privateRow 8 16, 283214716891672370805⟩, ⟨.privateRow 8 17, 816555698602524696816⟩, ⟨.privateRow 8 18, 1624779196198901182440⟩, ⟨.privateRow 8 19, 3758364986382710882640⟩, ⟨.privateRow 8 20, 7877668758953844030180⟩, ⟨.privateRow 8 21, 15066717036152478671520⟩, ⟨.privateRow 8 22, 24999166772600371487136⟩, ⟨.privateRow 8 23, 38489783570879689768720⟩, ⟨.privateRow 8 24, 56166245340001956309150⟩, ⟨.privateRow 8 25, 77925307563653808978720⟩, ⟨.privateRow 8 26, 34202616899340182813520⟩, ⟨.privateRow 9 12, 13493442924936374400⟩, ⟨.privateRow 9 13, 99701550500918766400⟩, ⟨.privateRow 9 14, 316699042767624316800⟩, ⟨.privateRow 9 15, 695418314743908395640⟩, ⟨.privateRow 9 16, 1623710965300677052800⟩, ⟨.privateRow 9 17, 3248642765913610253760⟩, ⟨.privateRow 9 18, 6279225562976545428480⟩, ⟨.privateRow 9 19, 11199332736981775145760⟩, ⟨.privateRow 9 20, 17983570059703383932160⟩, ⟨.privateRow 9 21, 26950183685116921861632⟩, ⟨.privateRow 9 22, 27084638347506732312320⟩, ⟨.privateRow 10 9, 7325011873536888960⟩, ⟨.privateRow 10 10, 46147574803282400448⟩, ⟨.privateRow 10 11, 149777216466793755840⟩, ⟨.privateRow 10 12, 367471428989100596160⟩, ⟨.privateRow 10 13, 927475768105185499200⟩, ⟨.privateRow 10 14, 1893973382551381851720⟩, ⟨.privateRow 10 15, 3522598209983889900864⟩, ⟨.privateRow 10 16, 6345291535451330061600⟩, ⟨.privateRow 10 17, 10708603896659121129600⟩, ⟨.privateRow 10 18, 10363976174570505767280⟩, ⟨.privateRow 11 6, 6688054319316289920⟩, ⟨.privateRow 11 7, 27968227153504485120⟩, ⟨.privateRow 11 8, 95225154355979556480⟩, ⟨.privateRow 11 9, 238429136483625735648⟩, ⟨.privateRow 11 10, 663877391906869620480⟩, ⟨.privateRow 11 11, 1478431563142195421760⟩, ⟨.privateRow 11 12, 2832194296750468890240⟩, ⟨.privateRow 11 13, 4989706525604909548440⟩, ⟨.privateRow 11 14, 1743352825901779572480⟩, ⟨.privateRow 12 4, 17625809820698139060⟩, ⟨.privateRow 12 5, 73568597512479189120⟩, ⟨.privateRow 12 6, 211509717848377668720⟩, ⟨.privateRow 12 7, 604313479566793339200⟩, ⟨.privateRow 12 8, 1480568024938643681040⟩, ⟨.privateRow 12 9, 1758870285265456403040⟩, ⟨.privateRow 13 3, 141006478565585112480⟩, ⟨.privateRow 13 4, 1250666157712146215040⟩, ⟨.privateRow 14 0, 423019435696755337440⟩, ⟨.hall 4 34, 94611318360977165185152⟩, ⟨.hall 3 35, 896096171284293389810400⟩, ⟨.assumptionRow 21, 195733291605736248⟩]
  caps := #[0, 135503007977485455587280, 23790395417005402305120, 2864144654025509230272, 616912291989891313416, 1639162754385723725808, 320131500630825507648, 542698006730324300736, 195733291605736248, 25394360244742759296, 1088842459528515480408, 0, 4003958664704922194700, 846038871393510674880, 5979379081922151665760, 57261637286175187049184] }

theorem case_54_39_21_checked :
    (Witness.linear .conditional case_54_39_21).check 54 39 21 = true := by
  change case_54_39_21.check 54 39 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_22 : Certificate := {
  objectiveScale := 885647322331200000
  eta := 7157332334797892510009947200
  rows := #[⟨.count 2, 570712441475920495953801600⟩, ⟨.count 3, 39366188685940051702166400⟩, ⟨.count 4, 2051644263129263386584000⟩, ⟨.count 5, 57684468504103000560000⟩, ⟨.path 4, 744952267323109021176000⟩, ⟨.path 5, 57850564308917948568000⟩, ⟨.privateRow 2 36, 47046106541014644853389600⟩, ⟨.privateRow 2 37, 77072026086770338704880800⟩, ⟨.privateRow 3 32, 4242038901167062523848320⟩, ⟨.privateRow 3 33, 8252051641854454745110800⟩, ⟨.privateRow 3 34, 18289950334742044939780800⟩, ⟨.privateRow 3 36, 85251106875967103154283200⟩, ⟨.privateRow 4 28, 261743275837367365041000⟩, ⟨.privateRow 4 29, 965088626868168962702400⟩, ⟨.privateRow 4 30, 1625452181664782384113200⟩, ⟨.privateRow 4 31, 3825787776441455271807360⟩, ⟨.privateRow 4 32, 5868601508850548890722300⟩, ⟨.privateRow 4 33, 8478014523755804887860000⟩, ⟨.privateRow 4 34, 9563411892514396291174800⟩, ⟨.privateRow 5 23, 160234634733619446000⟩, ⟨.privateRow 5 24, 11606814268704361324800⟩, ⟨.privateRow 5 25, 78950809225948973433120⟩, ⟨.privateRow 5 26, 188948681277884050723200⟩, ⟨.privateRow 5 27, 351538765142087702579400⟩, ⟨.privateRow 5 28, 813790506620264521233600⟩, ⟨.privateRow 5 29, 1415961420214048320412800⟩, ⟨.privateRow 5 30, 2166936287512797250369920⟩, ⟨.privateRow 5 31, 3133228047581194647084000⟩, ⟨.privateRow 5 32, 5159042487591398578972800⟩, ⟨.privateRow 6 18, 12017597605021458450⟩, ⟨.privateRow 6 19, 64093853893447778400⟩, ⟨.privateRow 6 20, 315891137046278336400⟩, ⟨.privateRow 6 21, 4422475918647896709600⟩, ⟨.privateRow 6 22, 19949212024335621027000⟩, ⟨.privateRow 6 23, 43175950668222548904000⟩, ⟨.privateRow 6 24, 78393192697075977761040⟩, ⟨.privateRow 6 25, 191277424636012653338400⟩, ⟨.privateRow 6 26, 352692454512169762590600⟩, ⟨.privateRow 6 27, 578410406328998515615200⟩, ⟨.privateRow 6 28, 884783606072099856922800⟩, ⟨.privateRow 6 29, 1271827161578462956346880⟩, ⟨.privateRow 6 30, 2111924532716051022169200⟩, ⟨.privateRow 6 31, 1706434766059153652121600⟩, ⟨.privateRow 7 15, 7121539321494197600⟩, ⟨.privateRow 7 16, 37702266996145752000⟩, ⟨.privateRow 7 17, 152222902996938473700⟩, ⟨.privateRow 7 18, 1563890035000125792960⟩, ⟨.privateRow 7 19, 5640259142623404499200⟩, ⟨.privateRow 7 20, 12207414018475130716800⟩, ⟨.privateRow 7 21, 21482123363287247060400⟩, ⟨.privateRow 7 22, 49655256625451087956800⟩, ⟨.privateRow 7 23, 99704399116647364079040⟩, ⟨.privateRow 7 25, 613217947125561619842000⟩, ⟨.privateRow 7 26, 237092321816705253412800⟩, ⟨.privateRow 7 27, 583318164284268231218400⟩, ⟨.privateRow 7 28, 969765646949422266303360⟩, ⟨.privateRow 7 29, 647155642762142218504800⟩, ⟨.privateRow 8 12, 5608212215676680610⟩, ⟨.privateRow 8 13, 23613525118638655200⟩, ⟨.privateRow 8 14, 81007509781996497700⟩, ⟨.privateRow 8 15, 626800188810923127000⟩, ⟨.privateRow 8 16, 2004935867104413318075⟩, ⟨.privateRow 8 17, 4396838377090517598240⟩, ⟨.privateRow 8 18, 7819450175000628964800⟩, ⟨.privateRow 8 19, 16712472402716508217800⟩, ⟨.privateRow 8 20, 32723918278473431359350⟩, ⟨.privateRow 8 21, 60252592695333646771800⟩, ⟨.privateRow 8 22, 34299825911078578610760⟩, ⟨.privateRow 8 23, 172184577715086709572800⟩, ⟨.privateRow 8 24, 370436437375983945992025⟩, ⟨.privateRow 8 25, 202600672157188427522400⟩, ⟨.privateRow 8 26, 256239216134267537070900⟩, ⟨.privateRow 9 9, 5826713990313434400⟩, ⟨.privateRow 9 10, 18312529683842222400⟩, ⟨.privateRow 9 11, 51275083114758222720⟩, ⟨.privateRow 9 12, 303602465811068424000⟩, ⟨.privateRow 9 13, 932921651115739885600⟩, ⟨.privateRow 9 14, 2066084231388787209600⟩, ⟨.privateRow 9 15, 3773525647976737953300⟩, ⟨.privateRow 9 16, 7862179410929594150400⟩, ⟨.privateRow 9 17, 14485210979919197918400⟩, ⟨.privateRow 9 18, 26239037724686852049600⟩, ⟨.privateRow 9 19, 45047296978111546918800⟩, ⟨.privateRow 9 21, 162016443871857294239520⟩, ⟨.privateRow 9 23, 362370626450080377129000⟩, ⟨.privateRow 10 7, 16720135798290724800⟩, ⟨.privateRow 10 8, 43700354927350758000⟩, ⟨.privateRow 10 9, 183125296838422224000⟩, ⟨.privateRow 10 10, 567230606957012838840⟩, ⟨.privateRow 10 11, 1275130356406487380800⟩, ⟨.privateRow 10 12, 2403519521004291690000⟩, ⟨.privateRow 10 13, 5033252643985457892000⟩, ⟨.privateRow 10 14, 9181444570236394255800⟩, ⟨.privateRow 10 15, 15831181911681601264800⟩, ⟨.privateRow 10 16, 26837012251670776927200⟩, ⟨.privateRow 10 17, 43529587386557725807200⟩, ⟨.privateRow 10 18, 30941307967061915022600⟩, ⟨.privateRow 10 19, 55971414590950850846400⟩, ⟨.privateRow 10 20, 165746706168455954942400⟩, ⟨.privateRow 11 4, 30765049868854933632⟩, ⟨.privateRow 11 5, 32046926946723889200⟩, ⟨.privateRow 11 6, 150481222184616523200⟩, ⟨.privateRow 11 7, 454483691244447883200⟩, ⟨.privateRow 11 8, 1043814191979006676800⟩, ⟨.privateRow 11 9, 2038184553811639353120⟩, ⟨.privateRow 11 10, 4331395178904576182400⟩, ⟨.privateRow 11 11, 8054460972609937485600⟩, ⟨.privateRow 11 12, 13866893801182407585600⟩, ⟨.privateRow 11 13, 22689224278280513553600⟩, ⟨.privateRow 11 14, 36379671469920959019840⟩, ⟨.privateRow 11 15, 56393435161392123880800⟩, ⟨.privateRow 11 16, 62387971320591399067200⟩, ⟨.privateRow 11 17, 60184128805947463917600⟩, ⟨.privateRow 11 21, 129501631791711236257200⟩, ⟨.privateRow 12 3, 465321379266430871184⟩, ⟨.privateRow 12 4, 352516196413962781200⟩, ⟨.privateRow 12 5, 1149509336132487330000⟩, ⟨.privateRow 12 6, 2355449130584205856200⟩, ⟨.privateRow 12 7, 2517972831528305580000⟩, ⟨.privateRow 12 10, 102229696960049206548000⟩, ⟨.privateRow 12 12, 68145787219274180140725⟩, ⟨.privateRow 12 13, 101877180763635243766800⟩, ⟨.privateRow 12 16, 469815960770708896644300⟩, ⟨.privateRow 13 2, 5583856551197170454208⟩, ⟨.privateRow 13 3, 528774294620944171800⟩, ⟨.privateRow 13 5, 22304661154919826883200⟩, ⟨.privateRow 13 10, 13188252995251784049600⟩, ⟨.privateRow 13 13, 13899210030036246801600⟩, ⟨.privateRow 14 0, 35956652034224203682400⟩, ⟨.privateRow 14 3, 111180542990734174557600⟩, ⟨.privateRow 14 4, 22496942716600170218400⟩, ⟨.privateRow 14 8, 32078973873670613089200⟩, ⟨.privateRow 14 9, 45287963115770277302400⟩, ⟨.privateRow 14 11, 14664673770820851697920⟩, ⟨.privateRow 15 0, 1416607486261294274019072⟩, ⟨.privateRow 15 4, 1393144008227980911302400⟩, ⟨.privateRow 15 8, 407591668041932495721600⟩, ⟨.hall 7 16, 2449742536681440⟩, ⟨.hall 14 24, 76989537296809471414080⟩]
  caps := #[0, 454979682341307700948800, 21226793935338880162560, 7299101162972307134160, 2226193942262010846840, 206021339635214961000, 2952912752930243818650, 1170652439836471422360, 86370378096964262470, 0, 871345399551467317560, 1578488431252884240180, 0, 0, 30158338000595582997648, 0] }

theorem case_54_39_22_checked :
    (Witness.linear .conditional case_54_39_22).check 54 39 22 = true := by
  change case_54_39_22.check 54 39 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_23 : Certificate := {
  objectiveScale := 929
  eta := 2510367600
  rows := #[⟨.assumptionRow 23, 564⟩]
  caps := #[0, 0, 1022180835, 355063995, 153777195, 56849100, 23112056, 9253893, 3469989, 1542648, 570285, 1475523945, 1442093445, 1009428485, 596524665, 311815669] }

theorem case_54_39_23_checked :
    (Witness.linear .conditional case_54_39_23).check 54 39 23 = true := by
  change case_54_39_23.check 54 39 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640, 653752] }

theorem case_54_39_24_checked :
    (Witness.linear .negative case_54_39_24).check 54 39 24 = true := by
  change case_54_39_24.check 54 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888] }

theorem case_54_39_25_checked :
    (Witness.linear .negative case_54_39_25).check 54 39 25 = true := by
  change case_54_39_25.check 54 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_40_1_checked :
    (Witness.rising).check 54 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_40_2_checked :
    (Witness.rising).check 54 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_40_3_checked :
    (Witness.rising).check 54 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_40_4_checked :
    (Witness.rising).check 54 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_40_5_checked :
    (Witness.rising).check 54 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_40_6_checked :
    (Witness.rising).check 54 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_40_7_checked :
    (Witness.rising).check 54 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_40_8_checked :
    (Witness.rising).check 54 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_40_9_checked :
    (Witness.rising).check 54 40 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_54_40_10_checked :
    (Witness.linear .positive case_54_40_10).check 54 40 10 = true := by
  change case_54_40_10.check 54 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_54_40_11_checked :
    (Witness.linear .positive case_54_40_11).check 54 40 11 = true := by
  change case_54_40_11.check 54 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_54_40_12_checked :
    (Witness.linear .positive case_54_40_12).check 54 40 12 = true := by
  change case_54_40_12.check 54 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_54_40_13_checked :
    (Witness.linear .positive case_54_40_13).check 54 40 13 = true := by
  change case_54_40_13.check 54 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_54_40_14_checked :
    (Witness.linear .positive case_54_40_14).check 54 40 14 = true := by
  change case_54_40_14.check 54 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_54_40_15_checked :
    (Witness.linear .positive case_54_40_15).check 54 40 15 = true := by
  change case_54_40_15.check 54 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_54_40_16_checked :
    (Witness.linear .positive case_54_40_16).check 54 40 16 = true := by
  change case_54_40_16.check 54 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_54_40_17_checked :
    (Witness.linear .positive case_54_40_17).check 54 40 17 = true := by
  change case_54_40_17.check 54 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_54_40_18_checked :
    (Witness.linear .positive case_54_40_18).check 54 40 18 = true := by
  change case_54_40_18.check 54 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_54_40_19_checked :
    (Witness.linear .positive case_54_40_19).check 54 40 19 = true := by
  change case_54_40_19.check 54 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_20 : Certificate := {
  objectiveScale := 299
  eta := 28521853800
  rows := #[⟨.assumptionRow 20, 467⟩]
  caps := #[0, 0, 8045420700, 2284751805, 653684265, 188585165, 54915168, 16571192, 5122780, 1608438, 520260, 321910875, 237301350, 121808115, 51045280] }

theorem case_54_40_20_checked :
    (Witness.linear .conditional case_54_40_20).check 54 40 20 = true := by
  change case_54_40_20.check 54 40 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_21 : Certificate := {
  objectiveScale := 37812649056000000
  eta := 500967940032177218581780800
  rows := #[⟨.count 2, 29527834653469578666240000⟩, ⟨.count 3, 1307040916278579879196800⟩, ⟨.count 4, 30791057526345282566400⟩, ⟨.count 5, 197378573886828734400⟩, ⟨.path 3, 517480845700299698337120⟩, ⟨.path 4, 29301719074168831355520⟩, ⟨.privateRow 2 37, 2166821984129605846243200⟩, ⟨.privateRow 2 38, 3200296197001041099561600⟩, ⟨.privateRow 3 32, 77619124180995399802800⟩, ⟨.privateRow 3 33, 222616714201157901905280⟩, ⟨.privateRow 3 34, 406098191664904836497400⟩, ⟨.privateRow 3 35, 850734549881212983386400⟩, ⟨.privateRow 3 36, 970510447801536887044800⟩, ⟨.privateRow 3 37, 1385926552975349096712000⟩, ⟨.privateRow 4 28, 6162597695799874929600⟩, ⟨.privateRow 4 29, 29273709739590286670700⟩, ⟨.privateRow 4 30, 53588282810274001389600⟩, ⟨.privateRow 4 31, 86912365368166919380800⟩, ⟨.privateRow 4 32, 195365312433183081309120⟩, ⟨.privateRow 4 33, 277440257919673639791000⟩, ⟨.privateRow 4 34, 365413533122482263619200⟩, ⟨.privateRow 4 35, 495814977603713780812800⟩, ⟨.privateRow 5 24, 75661786656617681520⟩, ⟨.privateRow 5 25, 2415196004106104331840⟩, ⟨.privateRow 5 26, 7583284808731959975648⟩, ⟨.privateRow 5 27, 12693635396188496830080⟩, ⟨.privateRow 5 28, 20616192042479261308080⟩, ⟨.privateRow 5 29, 46085077308661840500480⟩, ⟨.privateRow 5 30, 75734158800376185389280⟩, ⟨.privateRow 5 31, 107634483911965445443008⟩, ⟨.privateRow 5 32, 141915194624629860033600⟩, ⟨.privateRow 5 33, 206392195427660579937600⟩, ⟨.privateRow 5 34, 94682501893511743891680⟩, ⟨.privateRow 6 21, 6265986472597737600⟩, ⟨.privateRow 6 22, 828315211781477851200⟩, ⟨.privateRow 6 23, 2098061137241475806400⟩, ⟨.privateRow 6 24, 3580726451522670777600⟩, ⟨.privateRow 6 25, 5524406973565795355040⟩, ⟨.privateRow 6 26, 12137563907781406494400⟩, ⟨.privateRow 6 27, 21459437172029101845600⟩, ⟨.privateRow 6 28, 33187797352113917198400⟩, ⟨.privateRow 6 29, 47290444239773891956800⟩, ⟨.privateRow 6 30, 62209340298597598666560⟩, ⟨.privateRow 6 31, 87334536206758191951600⟩, ⟨.privateRow 7 19, 303743694259175330160⟩, ⟨.privateRow 7 20, 734295289757547375000⟩, ⟨.privateRow 7 21, 1269043010310828337200⟩, ⟨.privateRow 7 22, 1927182464478341670600⟩, ⟨.privateRow 7 23, 3836919852981837367200⟩, ⟨.privateRow 7 24, 6978977408348452667160⟩, ⟨.privateRow 7 25, 11457095182375271629200⟩, ⟨.privateRow 7 26, 17171935928154099892800⟩, ⟨.privateRow 7 27, 24136579892446485235200⟩, ⟨.privateRow 7 28, 31816329562924087381200⟩, ⟨.privateRow 7 29, 4950912561661287421200⟩, ⟨.privateRow 8 16, 128683089837981478800⟩, ⟨.privateRow 8 17, 338216410462326320925⟩, ⟨.privateRow 8 18, 599811555089418431760⟩, ⟨.privateRow 8 19, 914050776690194972400⟩, ⟨.privateRow 8 20, 1689105103454592054000⟩, ⟨.privateRow 8 21, 2856506583195493628400⟩, ⟨.privateRow 8 22, 4819326845736734931600⟩, ⟨.privateRow 8 23, 7505320272046662625560⟩, ⟨.privateRow 8 24, 10939890215616266704800⟩, ⟨.privateRow 8 25, 8503726891624204640400⟩, ⟨.privateRow 9 13, 63484336630266552000⟩, ⟨.privateRow 9 14, 197378573886828734400⟩, ⟨.privateRow 9 15, 380566531350421416000⟩, ⟨.privateRow 9 16, 598989144364889978700⟩, ⟨.privateRow 9 17, 1068768426009420776640⟩, ⟨.privateRow 9 18, 1699648830692136324000⟩, ⟨.privateRow 9 19, 2695820180095318953600⟩, ⟨.privateRow 9 20, 4254604814893863830400⟩, ⟨.privateRow 9 21, 2627726872553942140800⟩, ⟨.privateRow 10 10, 37595918835586425600⟩, ⟨.privateRow 10 11, 142112573198516688768⟩, ⟨.privateRow 10 12, 313728049020117251520⟩, ⟨.privateRow 10 13, 532922149494437582880⟩, ⟨.privateRow 10 14, 956705558133805159680⟩, ⟨.privateRow 10 15, 1495142697192727663080⟩, ⟨.privateRow 10 16, 1226378872416829203072⟩, ⟨.privateRow 11 7, 30035869939300024800⟩, ⟨.privateRow 11 8, 130090423698137120400⟩, ⟨.privateRow 11 9, 328964289811381224000⟩, ⟨.privateRow 11 10, 626676972090681231720⟩, ⟨.privateRow 11 11, 524611472699202688800⟩, ⟨.privateRow 12 4, 28948857503401547712⟩, ⟨.privateRow 12 5, 150775299496883061000⟩, ⟨.privateRow 12 6, 377593793522628883200⟩, ⟨.privateRow 13 1, 80413493065004299200⟩, ⟨.privateRow 13 2, 167012639442701236800⟩, ⟨.hall 3 36, 90631440028385859002400⟩, ⟨.assumptionRow 21, 24442555503394080⟩]
  caps := #[0, 8217596173770420746400, 1558610836630290817920, 200309672920447029420, 705690589801242771180, 88449804970397488800, 111446113396957420480, 131029161778482696720, 255498016984728960, 0, 599751963989618941800, 0, 5032762368796233103032, 0, 23749692298339393214400] }

theorem case_54_40_21_checked :
    (Witness.linear .conditional case_54_40_21).check 54 40 21 = true := by
  change case_54_40_21.check 54 40 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_22 : Certificate := {
  objectiveScale := 16824386094546888000000
  eta := 302815753382816065359004568731200
  rows := #[⟨.count 2, 19425240808060652388083891030400⟩, ⟨.count 3, 981787564259723782915768814400⟩, ⟨.count 4, 30489961248966698615962425600⟩, ⟨.path 3, 174697885143963505452652524000⟩, ⟨.path 4, 30452295422568114883464768000⟩, ⟨.path 5, 222272946518305008526200⟩, ⟨.privateRow 2 37, 1462869417370636284659473824000⟩, ⟨.privateRow 2 38, 2187168177678536689015262083200⟩, ⟨.privateRow 3 32, 44236272580381255310727991200⟩, ⟨.privateRow 3 33, 148249327540853506408783261920⟩, ⟨.privateRow 3 34, 271760700706658854507877860800⟩, ⟨.privateRow 3 35, 575467985121479526704683255200⟩, ⟨.privateRow 3 36, 667112062894427698647894194400⟩, ⟨.privateRow 3 37, 966623673957711089721127927200⟩, ⟨.privateRow 4 28, 4502014569759759773968447200⟩, ⟨.privateRow 4 29, 18421018254584047080477298800⟩, ⟨.privateRow 4 30, 35660434667452819366566996000⟩, ⟨.privateRow 4 31, 57488533613780147907549721200⟩, ⟨.privateRow 4 32, 130079689285928493279660972480⟩, ⟨.privateRow 4 33, 187055101359185989447796077800⟩, ⟨.privateRow 4 34, 250605136577647681827535137600⟩, ⟨.privateRow 4 35, 348134269420271803922241188400⟩, ⟨.privateRow 5 20, 675752687255467611169380⟩, ⟨.privateRow 5 21, 2883211465623328474322688⟩, ⟨.privateRow 5 22, 13901198137826762286912960⟩, ⟨.privateRow 5 23, 53228519365353756449034240⟩, ⟨.privateRow 5 24, 170289677188377838014683760⟩, ⟨.privateRow 5 25, 1837064396335227585855376320⟩, ⟨.privateRow 5 26, 4940022444912370424692635552⟩, ⟨.privateRow 5 27, 8376930645746445604771709760⟩, ⟨.privateRow 5 28, 13593441056830986466283248080⟩, ⟨.privateRow 5 29, 30232016794631468693527485120⟩, ⟨.privateRow 5 30, 50025520935730763609795088480⟩, ⟨.privateRow 5 31, 72034155257133238602478036992⟩, ⟨.privateRow 5 32, 96897529330936011700799736960⟩, ⟨.privateRow 5 33, 145083200950165888827917660160⟩, ⟨.privateRow 5 34, 80976796019197194781649144160⟩, ⟨.privateRow 6 16, 316141608072733385342400⟩, ⟨.privateRow 6 17, 1001115092230322386917600⟩, ⟨.privateRow 6 18, 3533347384342314306768000⟩, ⟨.privateRow 6 19, 9385453989659272377352500⟩, ⟨.privateRow 6 20, 20422747881498576693119040⟩, ⟨.privateRow 6 21, 87955111674521181136332000⟩, ⟨.privateRow 6 22, 655653376557612677093572800⟩, ⟨.privateRow 6 23, 1432595696981591335679085600⟩, ⟨.privateRow 6 24, 2379741584694406343011036800⟩, ⟨.privateRow 6 25, 3647863173068848713450350880⟩, ⟨.privateRow 6 26, 7944181961878351580986795200⟩, ⟨.privateRow 6 27, 13958798009740442621388826200⟩, ⟨.privateRow 6 28, 21724483534281490173936753600⟩, ⟨.privateRow 6 29, 31368940299944921671676078400⟩, ⟨.privateRow 6 30, 42134531555752916491633181760⟩, ⟨.privateRow 6 31, 64361689279487426254932504000⟩, ⟨.privateRow 6 32, 8217152677026486151819660800⟩, ⟨.privateRow 7 12, 204773541592565942778600⟩, ⟨.privateRow 7 13, 429049325241566737250400⟩, ⟨.privateRow 7 14, 1126254478759112685282300⟩, ⟨.privateRow 7 15, 2608168266600050429074800⟩, ⟨.privateRow 7 16, 4755296688094031337858600⟩, ⟨.privateRow 7 17, 12985051637458005077372400⟩, ⟨.privateRow 7 18, 44487051910984951068650850⟩, ⟨.privateRow 7 19, 259489031906099562689041920⟩, ⟨.privateRow 7 20, 532557474956094712612059000⟩, ⟨.privateRow 7 21, 869468457602034993037935600⟩, ⟨.privateRow 7 22, 1288435123700424911962951200⟩, ⟨.privateRow 7 23, 2528134144501819129544595600⟩, ⟨.privateRow 7 24, 4539256051190727766761781920⟩, ⟨.privateRow 7 25, 7405248337227694696029487200⟩, ⟨.privateRow 7 26, 11147103703518317802581564250⟩, ⟨.privateRow 7 27, 15856375912952581908563032800⟩, ⟨.privateRow 7 28, 21308734738122412005541116000⟩, ⟨.privateRow 7 29, 10889529304226108731457502240⟩, ⟨.privateRow 8 9, 187709079793185447547050⟩, ⟨.privateRow 8 10, 587611032396058792321200⟩, ⟨.privateRow 8 11, 1023867707962829713893000⟩, ⟨.privateRow 8 12, 1716197300966266949001600⟩, ⟨.privateRow 8 13, 4054516123532805667016280⟩, ⟨.privateRow 8 14, 9247142036127451521265200⟩, ⟨.privateRow 8 15, 27280386263276285043504600⟩, ⟨.privateRow 8 16, 124020493190415232167556800⟩, ⟨.privateRow 8 17, 263825111649322146527378775⟩, ⟨.privateRow 8 18, 430980047205153787568026800⟩, ⟨.privateRow 8 19, 630058934117240753652212400⟩, ⟨.privateRow 8 20, 1131799116193003701579074400⟩, ⟨.privateRow 8 21, 1878592470570199959050876400⟩, ⟨.privateRow 8 22, 3126482433035296814343664800⟩, ⟨.privateRow 8 23, 4834785226417118935379857440⟩, ⟨.privateRow 8 24, 7056860285131542505382162400⟩, ⟨.privateRow 8 25, 8766201735421553585894782050⟩, ⟨.privateRow 9 5, 222470020495627197092800⟩, ⟨.privateRow 9 6, 231026559745459012365600⟩, ⟨.privateRow 9 7, 480535244270554745720448⟩, ⟨.privateRow 9 8, 1001115092230322386917600⟩, ⟨.privateRow 9 9, 2089283670741542372697600⟩, ⟨.privateRow 9 10, 4095470831851318855572000⟩, ⟨.privateRow 9 11, 8294953621336956920174400⟩, ⟨.privateRow 9 12, 21323751464505866841344880⟩, ⟨.privateRow 9 13, 75557844329383279096833600⟩, ⟨.privateRow 9 14, 170523270709898246571631200⟩, ⟨.privateRow 9 15, 291854493946675161739036800⟩, ⟨.privateRow 9 16, 431730883524326529358215000⟩, ⟨.privateRow 9 17, 737221153918409405726120640⟩, ⟨.privateRow 9 18, 1139555007841601254137062400⟩, ⟨.privateRow 9 19, 1775670138203597969042001600⟩, ⟨.privateRow 9 20, 2763578212101804949086034800⟩, ⟨.privateRow 9 21, 2836250066751433351445462400⟩, ⟨.privateRow 10 5, 1247543422625478666774240⟩, ⟨.privateRow 10 7, 20272580617664028335081400⟩, ⟨.privateRow 10 9, 22115542491997121820088800⟩, ⟨.privateRow 10 10, 62297962025075490248758080⟩, ⟨.privateRow 10 11, 143800171847963507656844064⟩, ⟨.privateRow 10 12, 262903361273285083250739840⟩, ⟨.privateRow 10 13, 408454957629971533862380800⟩, ⟨.privateRow 10 15, 2413788598876530307097025360⟩, ⟨.privateRow 10 16, 294087569493579504380914176⟩, ⟨.privateRow 11 2, 2896082945380575476440200⟩, ⟨.privateRow 11 4, 9356575669691090000806800⟩, ⟨.privateRow 11 5, 58385032178872401605034432⟩, ⟨.privateRow 11 7, 74038990081903407832471200⟩, ⟨.privateRow 11 9, 648722579765248906722604800⟩, ⟨.privateRow 11 10, 360851934994419704364448920⟩, ⟨.privateRow 11 11, 130882625742111621531753600⟩, ⟨.privateRow 12 0, 17087998988069295914628000⟩, ⟨.privateRow 12 2, 55061330072667731280468000⟩, ⟨.privateRow 12 3, 236340170619604569650008800⟩, ⟨.privateRow 12 5, 132147192174402555073123200⟩, ⟨.privateRow 13 0, 169903532795660427951158400⟩, ⟨.hall 3 36, 67815617519176003110532298400⟩, ⟨.assumptionRow 22, 2945504753725183191360⟩]
  caps := #[0, 5645134084426446343727986200, 601395980511373271013160800, 452988052588669898802705840, 0, 12728299707753190040356668, 36804967303507727087874600, 0, 11180323663888102763836365, 9146703003481593624954312, 54841962631028325194364840, 0, 970332153455807095537029600, 0, 23620182373732654383194664000] }

theorem case_54_40_22_checked :
    (Witness.linear .conditional case_54_40_22).check 54 40 22 = true := by
  change case_54_40_22.check 54 40 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_23 : Certificate := {
  objectiveScale := 14
  eta := 70122000
  rows := #[⟨.assumptionRow 23, 9⟩]
  caps := #[0, 0, 24192090, 10015005, 3552120, 1397825, 543191, 187473, 83334, 31008, 59879925, 67863915, 50106420, 30677400, 16560115] }

theorem case_54_40_23_checked :
    (Witness.linear .conditional case_54_40_23).check 54 40 23 = true := by
  change case_54_40_23.check 54 40 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405, 4345965, 2414425] }

theorem case_54_40_24_checked :
    (Witness.linear .negative case_54_40_24).check 54 40 24 = true := by
  change case_54_40_24.check 54 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540] }

theorem case_54_40_25_checked :
    (Witness.linear .negative case_54_40_25).check 54 40 25 = true := by
  change case_54_40_25.check 54 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900] }

theorem case_54_40_26_checked :
    (Witness.linear .negative case_54_40_26).check 54 40 26 = true := by
  change case_54_40_26.check 54 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_41_1_checked :
    (Witness.rising).check 54 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_41_2_checked :
    (Witness.rising).check 54 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_41_3_checked :
    (Witness.rising).check 54 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_41_4_checked :
    (Witness.rising).check 54 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_41_5_checked :
    (Witness.rising).check 54 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_41_6_checked :
    (Witness.rising).check 54 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_41_7_checked :
    (Witness.rising).check 54 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_41_8_checked :
    (Witness.rising).check 54 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_41_9_checked :
    (Witness.rising).check 54 41 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_54_41_10_checked :
    (Witness.linear .positive case_54_41_10).check 54 41 10 = true := by
  change case_54_41_10.check 54 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_54_41_11_checked :
    (Witness.linear .positive case_54_41_11).check 54 41 11 = true := by
  change case_54_41_11.check 54 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_54_41_12_checked :
    (Witness.linear .positive case_54_41_12).check 54 41 12 = true := by
  change case_54_41_12.check 54 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_54_41_13_checked :
    (Witness.linear .positive case_54_41_13).check 54 41 13 = true := by
  change case_54_41_13.check 54 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_54_41_14_checked :
    (Witness.linear .positive case_54_41_14).check 54 41 14 = true := by
  change case_54_41_14.check 54 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_54_41_15_checked :
    (Witness.linear .positive case_54_41_15).check 54 41 15 = true := by
  change case_54_41_15.check 54 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_54_41_16_checked :
    (Witness.linear .positive case_54_41_16).check 54 41 16 = true := by
  change case_54_41_16.check 54 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_54_41_17_checked :
    (Witness.linear .positive case_54_41_17).check 54 41 17 = true := by
  change case_54_41_17.check 54 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_54_41_18_checked :
    (Witness.linear .positive case_54_41_18).check 54 41 18 = true := by
  change case_54_41_18.check 54 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_54_41_19_checked :
    (Witness.linear .positive case_54_41_19).check 54 41 19 = true := by
  change case_54_41_19.check 54 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_20 : Certificate := {
  objectiveScale := 3
  eta := 354817320
  rows := #[⟨.assumptionRow 20, 5⟩]
  caps := #[0, 0, 99249600, 28514250, 8259300, 2414425, 713184, 213180, 64600, 19890, 6240, 4942470, 3511755, 1735695] }

theorem case_54_41_20_checked :
    (Witness.linear .conditional case_54_41_20).check 54 41 20 = true := by
  change case_54_41_20.check 54 41 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_21 : Certificate := {
  objectiveScale := 593
  eta := 70526765760
  rows := #[⟨.assumptionRow 21, 745⟩]
  caps := #[0, 0, 20328799320, 5887142100, 1713758865, 508989195, 158646295, 49685152, 15662270, 4978722, 3435276780, 2852585580, 1675367265, 819257010] }

theorem case_54_41_21_checked :
    (Witness.linear .conditional case_54_41_21).check 54 41 21 = true := by
  change case_54_41_21.check 54 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_22 : Certificate := {
  objectiveScale := 935
  eta := 96510311040
  rows := #[⟨.assumptionRow 22, 954⟩]
  caps := #[0, 0, 30186765840, 9357376350, 2882500530, 884190840, 270489890, 88828553, 29951790, 9980700, 7047341910, 6343139985, 4066092030, 2188105920] }

theorem case_54_41_22_checked :
    (Witness.linear .conditional case_54_41_22).check 54 41 22 = true := by
  change case_54_41_22.check 54 41 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_23 : Certificate := {
  objectiveScale := 804
  eta := 21099709800
  rows := #[⟨.assumptionRow 23, 611⟩]
  caps := #[0, 0, 7257627000, 2366532675, 848544060, 307653060, 104311900, 36461095, 14048562, 4984536, 7583289750, 7276286325, 5007502500, 2916155970] }

theorem case_54_41_23_checked :
    (Witness.linear .conditional case_54_41_23).check 54 41 23 = true := by
  change case_54_41_23.check 54 41 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825, 15967980, 8947575] }

theorem case_54_41_24_checked :
    (Witness.linear .negative case_54_41_24).check 54 41 24 = true := by
  change case_54_41_24.check 54 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405] }

theorem case_54_41_25_checked :
    (Witness.linear .negative case_54_41_25).check 54 41 25 = true := by
  change case_54_41_25.check 54 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440] }

theorem case_54_41_26_checked :
    (Witness.linear .negative case_54_41_26).check 54 41 26 = true := by
  change case_54_41_26.check 54 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_42_1_checked :
    (Witness.rising).check 54 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_42_2_checked :
    (Witness.rising).check 54 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_42_3_checked :
    (Witness.rising).check 54 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_42_4_checked :
    (Witness.rising).check 54 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_42_5_checked :
    (Witness.rising).check 54 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_42_6_checked :
    (Witness.rising).check 54 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_42_7_checked :
    (Witness.rising).check 54 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_42_8_checked :
    (Witness.rising).check 54 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_42_9_checked :
    (Witness.rising).check 54 42 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_54_42_10_checked :
    (Witness.linear .positive case_54_42_10).check 54 42 10 = true := by
  change case_54_42_10.check 54 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_54_42_11_checked :
    (Witness.linear .positive case_54_42_11).check 54 42 11 = true := by
  change case_54_42_11.check 54 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_54_42_12_checked :
    (Witness.linear .positive case_54_42_12).check 54 42 12 = true := by
  change case_54_42_12.check 54 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_54_42_13_checked :
    (Witness.linear .positive case_54_42_13).check 54 42 13 = true := by
  change case_54_42_13.check 54 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_54_42_14_checked :
    (Witness.linear .positive case_54_42_14).check 54 42 14 = true := by
  change case_54_42_14.check 54 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_54_42_15_checked :
    (Witness.linear .positive case_54_42_15).check 54 42 15 = true := by
  change case_54_42_15.check 54 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_54_42_16_checked :
    (Witness.linear .positive case_54_42_16).check 54 42 16 = true := by
  change case_54_42_16.check 54 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_54_42_17_checked :
    (Witness.linear .positive case_54_42_17).check 54 42 17 = true := by
  change case_54_42_17.check 54 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_54_42_18_checked :
    (Witness.linear .positive case_54_42_18).check 54 42 18 = true := by
  change case_54_42_18.check 54 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_54_42_19_checked :
    (Witness.linear .positive case_54_42_19).check 54 42 19 = true := by
  change case_54_42_19.check 54 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_54_42_20_checked :
    (Witness.linear .positive case_54_42_20).check 54 42 20 = true := by
  change case_54_42_20.check 54 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_21 : Certificate := {
  objectiveScale := 913
  eta := 156365263560
  rows := #[⟨.assumptionRow 21, 1236⟩]
  caps := #[0, 0, 45607672440, 13370782050, 3942760395, 1170342810, 350017335, 105580948, 32161110, 9924960, 8612384040, 6910873710, 3919248645] }

theorem case_54_42_21_checked :
    (Witness.linear .conditional case_54_42_21).check 54 42 21 = true := by
  change case_54_42_21.check 54 42 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_22 : Certificate := {
  objectiveScale := 1
  eta := 84362160
  rows := #[⟨.assumptionRow 22, 1⟩]
  caps := #[0, 0, 27293640, 8684340, 2731365, 852150, 264385, 81719, 28424, 27293640, 24812400, 16128060, 8844420] }

theorem case_54_42_22_checked :
    (Witness.linear .conditional case_54_42_22).check 54 42 22 = true := by
  change case_54_42_22.check 54 42 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_23 : Certificate := {
  objectiveScale := 4
  eta := 89864040
  rows := #[⟨.assumptionRow 23, 3⟩]
  caps := #[0, 0, 32256120, 10795395, 3641820, 1381380, 480700, 158631, 63954, 136468200, 131505720, 91185570, 53716845] }

theorem case_54_42_23_checked :
    (Witness.linear .conditional case_54_42_23).check 54 42 23 = true := by
  change case_54_42_23.check 54 42 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_24 : Certificate := {
  objectiveScale := 51
  eta := 2459925
  rows := #[⟨.assumptionRow 24, 19⟩]
  caps := #[0, 0, 1137240, 532220, 290950, 123970, 66836, 35511, 14535, 2463251010, 2451465120, 1767883500, 1091145300] }

theorem case_54_42_24_checked :
    (Witness.linear .conditional case_54_42_24).check 54 42 24 = true := by
  change case_54_42_24.check 54 42 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825] }

theorem case_54_42_25_checked :
    (Witness.linear .negative case_54_42_25).check 54 42 25 = true := by
  change case_54_42_25.check 54 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845] }

theorem case_54_42_26_checked :
    (Witness.linear .negative case_54_42_26).check 54 42 26 = true := by
  change case_54_42_26.check 54 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_42_27_checked :
    (Witness.linear .negative case_54_42_27).check 54 42 27 = true := by
  change case_54_42_27.check 54 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_43_1_checked :
    (Witness.rising).check 54 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_43_2_checked :
    (Witness.rising).check 54 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_43_3_checked :
    (Witness.rising).check 54 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_43_4_checked :
    (Witness.rising).check 54 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_43_5_checked :
    (Witness.rising).check 54 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_43_6_checked :
    (Witness.rising).check 54 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_43_7_checked :
    (Witness.rising).check 54 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_43_8_checked :
    (Witness.rising).check 54 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_43_9_checked :
    (Witness.rising).check 54 43 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_54_43_10_checked :
    (Witness.linear .positive case_54_43_10).check 54 43 10 = true := by
  change case_54_43_10.check 54 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_54_43_11_checked :
    (Witness.linear .positive case_54_43_11).check 54 43 11 = true := by
  change case_54_43_11.check 54 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_54_43_12_checked :
    (Witness.linear .positive case_54_43_12).check 54 43 12 = true := by
  change case_54_43_12.check 54 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_54_43_13_checked :
    (Witness.linear .positive case_54_43_13).check 54 43 13 = true := by
  change case_54_43_13.check 54 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_54_43_14_checked :
    (Witness.linear .positive case_54_43_14).check 54 43 14 = true := by
  change case_54_43_14.check 54 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_54_43_15_checked :
    (Witness.linear .positive case_54_43_15).check 54 43 15 = true := by
  change case_54_43_15.check 54 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_54_43_16_checked :
    (Witness.linear .positive case_54_43_16).check 54 43 16 = true := by
  change case_54_43_16.check 54 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_54_43_17_checked :
    (Witness.linear .positive case_54_43_17).check 54 43 17 = true := by
  change case_54_43_17.check 54 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_54_43_18_checked :
    (Witness.linear .positive case_54_43_18).check 54 43 18 = true := by
  change case_54_43_18.check 54 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_54_43_19_checked :
    (Witness.linear .positive case_54_43_19).check 54 43 19 = true := by
  change case_54_43_19.check 54 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_54_43_20_checked :
    (Witness.linear .positive case_54_43_20).check 54 43 20 = true := by
  change case_54_43_20.check 54 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_54_43_21_checked :
    (Witness.linear .positive case_54_43_21).check 54 43 21 = true := by
  change case_54_43_21.check 54 43 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_22 : Certificate := {
  objectiveScale := 991
  eta := 175473292800
  rows := #[⟨.assumptionRow 22, 1090⟩]
  caps := #[0, 0, 51366630480, 15054303390, 4681489575, 1476946380, 464222915, 145704977, 84362160, 46019558280, 40588123920, 25579103160] }

theorem case_54_43_22_checked :
    (Witness.linear .conditional case_54_43_22).check 54 43 22 = true := by
  change case_54_43_22.check 54 43 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_23 : Certificate := {
  objectiveScale := 8
  eta := 770263200
  rows := #[⟨.assumptionRow 23, 7⟩]
  caps := #[0, 0, 238199040, 76918440, 26403195, 8727810, 2812095, 889295, 326876, 463991880, 436698240, 295267560] }

theorem case_54_43_23_checked :
    (Witness.linear .conditional case_54_43_23).check 54 43 23 = true := by
  change case_54_43_23.check 54 43 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_24 : Certificate := {
  objectiveScale := 77
  eta := 73628100
  rows := #[⟨.assumptionRow 24, 39⟩]
  caps := #[0, 0, 35796150, 12876435, 6364215, 2351635, 1157728, 442244, 5110734090, 8699847750, 7232814600, 4811124360] }

theorem case_54_43_24_checked :
    (Witness.linear .conditional case_54_43_24).check 54 43 24 = true := by
  change case_54_43_24.check 54 43 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 129644790, 129644790, 94287120] }

theorem case_54_43_25_checked :
    (Witness.linear .negative case_54_43_25).check 54 43 25 = true := by
  change case_54_43_25.check 54 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670] }

theorem case_54_43_26_checked :
    (Witness.linear .negative case_54_43_26).check 54 43 26 = true := by
  change case_54_43_26.check 54 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_43_27_checked :
    (Witness.linear .negative case_54_43_27).check 54 43 27 = true := by
  change case_54_43_27.check 54 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_43_28_checked :
    (Witness.linear .negative case_54_43_28).check 54 43 28 = true := by
  change case_54_43_28.check 54 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_44_1_checked :
    (Witness.rising).check 54 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_44_2_checked :
    (Witness.rising).check 54 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_44_3_checked :
    (Witness.rising).check 54 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_44_4_checked :
    (Witness.rising).check 54 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_44_5_checked :
    (Witness.rising).check 54 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_44_6_checked :
    (Witness.rising).check 54 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_44_7_checked :
    (Witness.rising).check 54 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_44_8_checked :
    (Witness.rising).check 54 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_44_9_checked :
    (Witness.rising).check 54 44 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_54_44_10_checked :
    (Witness.linear .positive case_54_44_10).check 54 44 10 = true := by
  change case_54_44_10.check 54 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_54_44_11_checked :
    (Witness.linear .positive case_54_44_11).check 54 44 11 = true := by
  change case_54_44_11.check 54 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_54_44_12_checked :
    (Witness.linear .positive case_54_44_12).check 54 44 12 = true := by
  change case_54_44_12.check 54 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_54_44_13_checked :
    (Witness.linear .positive case_54_44_13).check 54 44 13 = true := by
  change case_54_44_13.check 54 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_54_44_14_checked :
    (Witness.linear .positive case_54_44_14).check 54 44 14 = true := by
  change case_54_44_14.check 54 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_54_44_15_checked :
    (Witness.linear .positive case_54_44_15).check 54 44 15 = true := by
  change case_54_44_15.check 54 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_54_44_16_checked :
    (Witness.linear .positive case_54_44_16).check 54 44 16 = true := by
  change case_54_44_16.check 54 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_54_44_17_checked :
    (Witness.linear .positive case_54_44_17).check 54 44 17 = true := by
  change case_54_44_17.check 54 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_54_44_18_checked :
    (Witness.linear .positive case_54_44_18).check 54 44 18 = true := by
  change case_54_44_18.check 54 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_54_44_19_checked :
    (Witness.linear .positive case_54_44_19).check 54 44 19 = true := by
  change case_54_44_19.check 54 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_54_44_20_checked :
    (Witness.linear .positive case_54_44_20).check 54 44 20 = true := by
  change case_54_44_20.check 54 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_54_44_21_checked :
    (Witness.linear .positive case_54_44_21).check 54 44 21 = true := by
  change case_54_44_21.check 54 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_22 : Certificate := {
  objectiveScale := 3
  eta := 1645062120
  rows := #[⟨.assumptionRow 22, 4⟩]
  caps := #[0, 0, 463991880, 136468200, 40320150, 11975985, 3579030, 1077205, 326876, 100130, 89864040] }

theorem case_54_44_22_checked :
    (Witness.linear .conditional case_54_44_22).check 54 44 22 = true := by
  change case_54_44_22.check 54 44 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_23 : Certificate := {
  objectiveScale := 641
  eta := 55073818800
  rows := #[⟨.assumptionRow 23, 553⟩]
  caps := #[0, 0, 17366198760, 5370643980, 1864611840, 633551100, 208095030, 68854410, 135622717470, 128314845360, 87483559920] }

theorem case_54_44_23_checked :
    (Witness.linear .conditional case_54_44_23).check 54 44 23 = true := by
  change case_54_44_23.check 54 44 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_24 : Certificate := {
  objectiveScale := 12
  eta := 58902480
  rows := #[⟨.assumptionRow 24, 7⟩]
  caps := #[0, 0, 22088430, 8714355, 3502785, 1282710, 562925, 201894, 3295707030, 3247943160, 2319959400] }

theorem case_54_44_24_checked :
    (Witness.linear .conditional case_54_44_24).check 54 44 24 = true := by
  change case_54_44_24.check 54 44 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 477638700, 477638700, 347993910] }

theorem case_54_44_25_checked :
    (Witness.linear .negative case_54_44_25).check 54 44 25 = true := by
  change case_54_44_25.check 54 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 129644790] }

theorem case_54_44_26_checked :
    (Witness.linear .negative case_54_44_26).check 54 44 26 = true := by
  change case_54_44_26.check 54 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_44_27_checked :
    (Witness.linear .negative case_54_44_27).check 54 44 27 = true := by
  change case_54_44_27.check 54 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_44_28_checked :
    (Witness.linear .negative case_54_44_28).check 54 44 28 = true := by
  change case_54_44_28.check 54 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_45_1_checked :
    (Witness.rising).check 54 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_45_2_checked :
    (Witness.rising).check 54 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_45_3_checked :
    (Witness.rising).check 54 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_45_4_checked :
    (Witness.rising).check 54 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_45_5_checked :
    (Witness.rising).check 54 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_45_6_checked :
    (Witness.rising).check 54 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_45_7_checked :
    (Witness.rising).check 54 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_45_8_checked :
    (Witness.rising).check 54 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_45_9_checked :
    (Witness.rising).check 54 45 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_54_45_10_checked :
    (Witness.linear .positive case_54_45_10).check 54 45 10 = true := by
  change case_54_45_10.check 54 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_54_45_11_checked :
    (Witness.linear .positive case_54_45_11).check 54 45 11 = true := by
  change case_54_45_11.check 54 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_54_45_12_checked :
    (Witness.linear .positive case_54_45_12).check 54 45 12 = true := by
  change case_54_45_12.check 54 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_54_45_13_checked :
    (Witness.linear .positive case_54_45_13).check 54 45 13 = true := by
  change case_54_45_13.check 54 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_54_45_14_checked :
    (Witness.linear .positive case_54_45_14).check 54 45 14 = true := by
  change case_54_45_14.check 54 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_54_45_15_checked :
    (Witness.linear .positive case_54_45_15).check 54 45 15 = true := by
  change case_54_45_15.check 54 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_54_45_16_checked :
    (Witness.linear .positive case_54_45_16).check 54 45 16 = true := by
  change case_54_45_16.check 54 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_54_45_17_checked :
    (Witness.linear .positive case_54_45_17).check 54 45 17 = true := by
  change case_54_45_17.check 54 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_54_45_18_checked :
    (Witness.linear .positive case_54_45_18).check 54 45 18 = true := by
  change case_54_45_18.check 54 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_54_45_19_checked :
    (Witness.linear .positive case_54_45_19).check 54 45 19 = true := by
  change case_54_45_19.check 54 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_54_45_20_checked :
    (Witness.linear .positive case_54_45_20).check 54 45 20 = true := by
  change case_54_45_20.check 54 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_54_45_21_checked :
    (Witness.linear .positive case_54_45_21).check 54 45 21 = true := by
  change case_54_45_21.check 54 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_54_45_22_checked :
    (Witness.linear .positive case_54_45_22).check 54 45 22 = true := by
  change case_54_45_22.check 54 45 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_23 : Certificate := {
  objectiveScale := 743
  eta := 168280501680
  rows := #[⟨.assumptionRow 23, 718⟩]
  caps := #[0, 0, 51081287880, 15396094200, 4824150870, 1596938070, 518107200, 170639190, 270493052850, 249708325680] }

theorem case_54_45_23_checked :
    (Witness.linear .conditional case_54_45_23).check 54 45 23 = true := by
  change case_54_45_23.check 54 45 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_24 : Certificate := {
  objectiveScale := 19
  eta := 84847620
  rows := #[⟨.assumptionRow 24, 11⟩]
  caps := #[0, 0, 32957340, 12486240, 5229510, 1825395, 841225, 19187428920, 18934962750, 13571762490] }

theorem case_54_45_24_checked :
    (Witness.linear .conditional case_54_45_24).check 54 45 24 = true := by
  change case_54_45_24.check 54 45 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 1767263190, 1767263190, 1289624490] }

theorem case_54_45_25_checked :
    (Witness.linear .negative case_54_45_25).check 54 45 25 = true := by
  change case_54_45_25.check 54 45 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 477638700] }

theorem case_54_45_26_checked :
    (Witness.linear .negative case_54_45_26).check 54 45 26 = true := by
  change case_54_45_26.check 54 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_45_27_checked :
    (Witness.linear .negative case_54_45_27).check 54 45 27 = true := by
  change case_54_45_27.check 54 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_45_28_checked :
    (Witness.linear .negative case_54_45_28).check 54 45 28 = true := by
  change case_54_45_28.check 54 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_45_29_checked :
    (Witness.linear .negative case_54_45_29).check 54 45 29 = true := by
  change case_54_45_29.check 54 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_46_1_checked :
    (Witness.rising).check 54 46 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_46_2_checked :
    (Witness.rising).check 54 46 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_46_3_checked :
    (Witness.rising).check 54 46 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_46_4_checked :
    (Witness.rising).check 54 46 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_46_5_checked :
    (Witness.rising).check 54 46 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_46_6_checked :
    (Witness.rising).check 54 46 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_46_7_checked :
    (Witness.rising).check 54 46 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_46_8_checked :
    (Witness.rising).check 54 46 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_46_9_checked :
    (Witness.rising).check 54 46 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_54_46_10_checked :
    (Witness.linear .positive case_54_46_10).check 54 46 10 = true := by
  change case_54_46_10.check 54 46 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_54_46_11_checked :
    (Witness.linear .positive case_54_46_11).check 54 46 11 = true := by
  change case_54_46_11.check 54 46 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_54_46_12_checked :
    (Witness.linear .positive case_54_46_12).check 54 46 12 = true := by
  change case_54_46_12.check 54 46 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_54_46_13_checked :
    (Witness.linear .positive case_54_46_13).check 54 46 13 = true := by
  change case_54_46_13.check 54 46 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_54_46_14_checked :
    (Witness.linear .positive case_54_46_14).check 54 46 14 = true := by
  change case_54_46_14.check 54 46 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_54_46_15_checked :
    (Witness.linear .positive case_54_46_15).check 54 46 15 = true := by
  change case_54_46_15.check 54 46 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_54_46_16_checked :
    (Witness.linear .positive case_54_46_16).check 54 46 16 = true := by
  change case_54_46_16.check 54 46 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_54_46_17_checked :
    (Witness.linear .positive case_54_46_17).check 54 46 17 = true := by
  change case_54_46_17.check 54 46 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_54_46_18_checked :
    (Witness.linear .positive case_54_46_18).check 54 46 18 = true := by
  change case_54_46_18.check 54 46 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_54_46_19_checked :
    (Witness.linear .positive case_54_46_19).check 54 46 19 = true := by
  change case_54_46_19.check 54 46 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_54_46_20_checked :
    (Witness.linear .positive case_54_46_20).check 54 46 20 = true := by
  change case_54_46_20.check 54 46 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_54_46_21_checked :
    (Witness.linear .positive case_54_46_21).check 54 46 21 = true := by
  change case_54_46_21.check 54 46 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_54_46_22_checked :
    (Witness.linear .positive case_54_46_22).check 54 46 22 = true := by
  change case_54_46_22.check 54 46 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_23 : Certificate := {
  objectiveScale := 11
  eta := 69014072400
  rows := #[⟨.assumptionRow 23, 19⟩]
  caps := #[0, 0, 19187428920, 5363200260, 1507973610, 426773280, 121660800, 34964370, 10140585] }

theorem case_54_46_23_checked :
    (Witness.linear .conditional case_54_46_23).check 54 46 23 = true := by
  change case_54_46_23.check 54 46 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_24 : Certificate := {
  objectiveScale := 939
  eta := 45991131900
  rows := #[⟨.assumptionRow 24, 682⟩]
  caps := #[0, 0, 15177205680, 5419028160, 1987263135, 672386715, 259451400, 1569084231780, 1525912516710] }

theorem case_54_46_24_checked :
    (Witness.linear .conditional case_54_46_24).check 54 46 24 = true := by
  change case_54_46_24.check 54 46 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 6564120420, 6564120420, 4796857230] }

theorem case_54_46_25_checked :
    (Witness.linear .negative case_54_46_25).check 54 46 25 = true := by
  change case_54_46_25.check 54 46 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 1767263190] }

theorem case_54_46_26_checked :
    (Witness.linear .negative case_54_46_26).check 54 46 26 = true := by
  change case_54_46_26.check 54 46 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_46_27_checked :
    (Witness.linear .negative case_54_46_27).check 54 46 27 = true := by
  change case_54_46_27.check 54 46 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_46_28_checked :
    (Witness.linear .negative case_54_46_28).check 54 46 28 = true := by
  change case_54_46_28.check 54 46 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_46_29_checked :
    (Witness.linear .negative case_54_46_29).check 54 46 29 = true := by
  change case_54_46_29.check 54 46 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_46_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_46_30_checked :
    (Witness.linear .negative case_54_46_30).check 54 46 30 = true := by
  change case_54_46_30.check 54 46 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_47_1_checked :
    (Witness.rising).check 54 47 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_47_2_checked :
    (Witness.rising).check 54 47 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_47_3_checked :
    (Witness.rising).check 54 47 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_47_4_checked :
    (Witness.rising).check 54 47 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_47_5_checked :
    (Witness.rising).check 54 47 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_47_6_checked :
    (Witness.rising).check 54 47 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_47_7_checked :
    (Witness.rising).check 54 47 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_47_8_checked :
    (Witness.rising).check 54 47 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_47_9_checked :
    (Witness.rising).check 54 47 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_54_47_10_checked :
    (Witness.linear .positive case_54_47_10).check 54 47 10 = true := by
  change case_54_47_10.check 54 47 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_54_47_11_checked :
    (Witness.linear .positive case_54_47_11).check 54 47 11 = true := by
  change case_54_47_11.check 54 47 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_54_47_12_checked :
    (Witness.linear .positive case_54_47_12).check 54 47 12 = true := by
  change case_54_47_12.check 54 47 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_54_47_13_checked :
    (Witness.linear .positive case_54_47_13).check 54 47 13 = true := by
  change case_54_47_13.check 54 47 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_54_47_14_checked :
    (Witness.linear .positive case_54_47_14).check 54 47 14 = true := by
  change case_54_47_14.check 54 47 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_54_47_15_checked :
    (Witness.linear .positive case_54_47_15).check 54 47 15 = true := by
  change case_54_47_15.check 54 47 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_54_47_16_checked :
    (Witness.linear .positive case_54_47_16).check 54 47 16 = true := by
  change case_54_47_16.check 54 47 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_54_47_17_checked :
    (Witness.linear .positive case_54_47_17).check 54 47 17 = true := by
  change case_54_47_17.check 54 47 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_54_47_18_checked :
    (Witness.linear .positive case_54_47_18).check 54 47 18 = true := by
  change case_54_47_18.check 54 47 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_54_47_19_checked :
    (Witness.linear .positive case_54_47_19).check 54 47 19 = true := by
  change case_54_47_19.check 54 47 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_54_47_20_checked :
    (Witness.linear .positive case_54_47_20).check 54 47 20 = true := by
  change case_54_47_20.check 54 47 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_54_47_21_checked :
    (Witness.linear .positive case_54_47_21).check 54 47 21 = true := by
  change case_54_47_21.check 54 47 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_54_47_22_checked :
    (Witness.linear .positive case_54_47_22).check 54 47 22 = true := by
  change case_54_47_22.check 54 47 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_54_47_23_checked :
    (Witness.linear .positive case_54_47_23).check 54 47 23 = true := by
  change case_54_47_23.check 54 47 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_24 : Certificate := {
  objectiveScale := 19
  eta := 3766036860
  rows := #[⟨.assumptionRow 24, 16⟩]
  caps := #[0, 0, 1302111600, 429254520, 137088510, 42791385, 15509130, 54225342600] }

theorem case_54_47_24_checked :
    (Witness.linear .conditional case_54_47_24).check 54 47 24 = true := by
  change case_54_47_24.check 54 47 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 24466267020, 24466267020, 17902146600] }

theorem case_54_47_25_checked :
    (Witness.linear .negative case_54_47_25).check 54 47 25 = true := by
  change case_54_47_25.check 54 47 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 6564120420] }

theorem case_54_47_26_checked :
    (Witness.linear .negative case_54_47_26).check 54 47 26 = true := by
  change case_54_47_26.check 54 47 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_47_27_checked :
    (Witness.linear .negative case_54_47_27).check 54 47 27 = true := by
  change case_54_47_27.check 54 47 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_47_28_checked :
    (Witness.linear .negative case_54_47_28).check 54 47 28 = true := by
  change case_54_47_28.check 54 47 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_47_29_checked :
    (Witness.linear .negative case_54_47_29).check 54 47 29 = true := by
  change case_54_47_29.check 54 47 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_47_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_54_47_30_checked :
    (Witness.linear .negative case_54_47_30).check 54 47 30 = true := by
  change case_54_47_30.check 54 47 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_48_1_checked :
    (Witness.rising).check 54 48 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_48_2_checked :
    (Witness.rising).check 54 48 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_48_3_checked :
    (Witness.rising).check 54 48 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_48_4_checked :
    (Witness.rising).check 54 48 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_48_5_checked :
    (Witness.rising).check 54 48 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_48_6_checked :
    (Witness.rising).check 54 48 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_48_7_checked :
    (Witness.rising).check 54 48 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_48_8_checked :
    (Witness.rising).check 54 48 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_48_9_checked :
    (Witness.rising).check 54 48 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_54_48_10_checked :
    (Witness.linear .positive case_54_48_10).check 54 48 10 = true := by
  change case_54_48_10.check 54 48 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_54_48_11_checked :
    (Witness.linear .positive case_54_48_11).check 54 48 11 = true := by
  change case_54_48_11.check 54 48 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_54_48_12_checked :
    (Witness.linear .positive case_54_48_12).check 54 48 12 = true := by
  change case_54_48_12.check 54 48 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_54_48_13_checked :
    (Witness.linear .positive case_54_48_13).check 54 48 13 = true := by
  change case_54_48_13.check 54 48 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_54_48_14_checked :
    (Witness.linear .positive case_54_48_14).check 54 48 14 = true := by
  change case_54_48_14.check 54 48 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_54_48_15_checked :
    (Witness.linear .positive case_54_48_15).check 54 48 15 = true := by
  change case_54_48_15.check 54 48 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_54_48_16_checked :
    (Witness.linear .positive case_54_48_16).check 54 48 16 = true := by
  change case_54_48_16.check 54 48 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_54_48_17_checked :
    (Witness.linear .positive case_54_48_17).check 54 48 17 = true := by
  change case_54_48_17.check 54 48 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_54_48_18_checked :
    (Witness.linear .positive case_54_48_18).check 54 48 18 = true := by
  change case_54_48_18.check 54 48 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_54_48_19_checked :
    (Witness.linear .positive case_54_48_19).check 54 48 19 = true := by
  change case_54_48_19.check 54 48 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_54_48_20_checked :
    (Witness.linear .positive case_54_48_20).check 54 48 20 = true := by
  change case_54_48_20.check 54 48 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_54_48_21_checked :
    (Witness.linear .positive case_54_48_21).check 54 48 21 = true := by
  change case_54_48_21.check 54 48 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_54_48_22_checked :
    (Witness.linear .positive case_54_48_22).check 54 48 22 = true := by
  change case_54_48_22.check 54 48 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670] }

theorem case_54_48_23_checked :
    (Witness.linear .positive case_54_48_23).check 54 48 23 = true := by
  change case_54_48_23.check 54 48 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700, 129644790] }

theorem case_54_48_24_checked :
    (Witness.linear .positive case_54_48_24).check 54 48 24 = true := by
  change case_54_48_24.check 54 48 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 91482563640, 91482563640, 67016296620] }

theorem case_54_48_25_checked :
    (Witness.linear .negative case_54_48_25).check 54 48 25 = true := by
  change case_54_48_25.check 54 48 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 24466267020] }

theorem case_54_48_26_checked :
    (Witness.linear .negative case_54_48_26).check 54 48 26 = true := by
  change case_54_48_26.check 54 48 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_54_48_27_checked :
    (Witness.linear .negative case_54_48_27).check 54 48 27 = true := by
  change case_54_48_27.check 54 48 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_54_48_28_checked :
    (Witness.linear .negative case_54_48_28).check 54 48 28 = true := by
  change case_54_48_28.check 54 48 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_54_48_29_checked :
    (Witness.linear .negative case_54_48_29).check 54 48 29 = true := by
  change case_54_48_29.check 54 48 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_54_48_30_checked :
    (Witness.linear .negative case_54_48_30).check 54 48 30 = true := by
  change case_54_48_30.check 54 48 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_48_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_54_48_31_checked :
    (Witness.linear .negative case_54_48_31).check 54 48 31 = true := by
  change case_54_48_31.check 54 48 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_49_1_checked :
    (Witness.rising).check 54 49 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_49_2_checked :
    (Witness.rising).check 54 49 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_49_3_checked :
    (Witness.rising).check 54 49 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_49_4_checked :
    (Witness.rising).check 54 49 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_49_5_checked :
    (Witness.rising).check 54 49 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_49_6_checked :
    (Witness.rising).check 54 49 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_49_7_checked :
    (Witness.rising).check 54 49 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_49_8_checked :
    (Witness.rising).check 54 49 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_49_9_checked :
    (Witness.rising).check 54 49 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_54_49_10_checked :
    (Witness.linear .positive case_54_49_10).check 54 49 10 = true := by
  change case_54_49_10.check 54 49 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_54_49_11_checked :
    (Witness.linear .positive case_54_49_11).check 54 49 11 = true := by
  change case_54_49_11.check 54 49 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_54_49_12_checked :
    (Witness.linear .positive case_54_49_12).check 54 49 12 = true := by
  change case_54_49_12.check 54 49 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_54_49_13_checked :
    (Witness.linear .positive case_54_49_13).check 54 49 13 = true := by
  change case_54_49_13.check 54 49 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_54_49_14_checked :
    (Witness.linear .positive case_54_49_14).check 54 49 14 = true := by
  change case_54_49_14.check 54 49 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_54_49_15_checked :
    (Witness.linear .positive case_54_49_15).check 54 49 15 = true := by
  change case_54_49_15.check 54 49 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_54_49_16_checked :
    (Witness.linear .positive case_54_49_16).check 54 49 16 = true := by
  change case_54_49_16.check 54 49 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_54_49_17_checked :
    (Witness.linear .positive case_54_49_17).check 54 49 17 = true := by
  change case_54_49_17.check 54 49 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_54_49_18_checked :
    (Witness.linear .positive case_54_49_18).check 54 49 18 = true := by
  change case_54_49_18.check 54 49 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_54_49_19_checked :
    (Witness.linear .positive case_54_49_19).check 54 49 19 = true := by
  change case_54_49_19.check 54 49 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_54_49_20_checked :
    (Witness.linear .positive case_54_49_20).check 54 49 20 = true := by
  change case_54_49_20.check 54 49 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845] }

theorem case_54_49_21_checked :
    (Witness.linear .positive case_54_49_21).check 54 49 21 = true := by
  change case_54_49_21.check 54 49 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670] }

theorem case_54_49_22_checked :
    (Witness.linear .positive case_54_49_22).check 54 49 22 = true := by
  change case_54_49_22.check 54 49 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790] }

theorem case_54_49_23_checked :
    (Witness.linear .positive case_54_49_23).check 54 49 23 = true := by
  change case_54_49_23.check 54 49 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700] }

theorem case_54_49_24_checked :
    (Witness.linear .positive case_54_49_24).check 54 49 24 = true := by
  change case_54_49_24.check 54 49 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_25 : Certificate := {
  objectiveScale := 7
  eta := 753207372
  rows := #[⟨.assumptionRow 25, 5⟩]
  caps := #[0, 0, 288848700, 99573240, 32256120, 12746370] }

theorem case_54_49_25_checked :
    (Witness.linear .conditional case_54_49_25).check 54 49 25 = true := by
  change case_54_49_25.check 54 49 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 91482563640] }

theorem case_54_49_26_checked :
    (Witness.linear .negative case_54_49_26).check 54 49 26 = true := by
  change case_54_49_26.check 54 49 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_54_49_27_checked :
    (Witness.linear .negative case_54_49_27).check 54 49 27 = true := by
  change case_54_49_27.check 54 49 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_54_49_28_checked :
    (Witness.linear .negative case_54_49_28).check 54 49 28 = true := by
  change case_54_49_28.check 54 49 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_54_49_29_checked :
    (Witness.linear .negative case_54_49_29).check 54 49 29 = true := by
  change case_54_49_29.check 54 49 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_54_49_30_checked :
    (Witness.linear .negative case_54_49_30).check 54 49 30 = true := by
  change case_54_49_30.check 54 49 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_54_49_31_checked :
    (Witness.linear .negative case_54_49_31).check 54 49 31 = true := by
  change case_54_49_31.check 54 49 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_49_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_54_49_32_checked :
    (Witness.linear .negative case_54_49_32).check 54 49 32 = true := by
  change case_54_49_32.check 54 49 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_50_1_checked :
    (Witness.rising).check 54 50 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_50_2_checked :
    (Witness.rising).check 54 50 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_50_3_checked :
    (Witness.rising).check 54 50 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_50_4_checked :
    (Witness.rising).check 54 50 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_50_5_checked :
    (Witness.rising).check 54 50 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_50_6_checked :
    (Witness.rising).check 54 50 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_50_7_checked :
    (Witness.rising).check 54 50 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_50_8_checked :
    (Witness.rising).check 54 50 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_50_9_checked :
    (Witness.rising).check 54 50 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_54_50_10_checked :
    (Witness.linear .positive case_54_50_10).check 54 50 10 = true := by
  change case_54_50_10.check 54 50 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_54_50_11_checked :
    (Witness.linear .positive case_54_50_11).check 54 50 11 = true := by
  change case_54_50_11.check 54 50 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_54_50_12_checked :
    (Witness.linear .positive case_54_50_12).check 54 50 12 = true := by
  change case_54_50_12.check 54 50 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_54_50_13_checked :
    (Witness.linear .positive case_54_50_13).check 54 50 13 = true := by
  change case_54_50_13.check 54 50 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_54_50_14_checked :
    (Witness.linear .positive case_54_50_14).check 54 50 14 = true := by
  change case_54_50_14.check 54 50 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_54_50_15_checked :
    (Witness.linear .positive case_54_50_15).check 54 50 15 = true := by
  change case_54_50_15.check 54 50 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_54_50_16_checked :
    (Witness.linear .positive case_54_50_16).check 54 50 16 = true := by
  change case_54_50_16.check 54 50 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_54_50_17_checked :
    (Witness.linear .positive case_54_50_17).check 54 50 17 = true := by
  change case_54_50_17.check 54 50 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_54_50_18_checked :
    (Witness.linear .positive case_54_50_18).check 54 50 18 = true := by
  change case_54_50_18.check 54 50 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_54_50_19_checked :
    (Witness.linear .positive case_54_50_19).check 54 50 19 = true := by
  change case_54_50_19.check 54 50 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_54_50_20_checked :
    (Witness.linear .positive case_54_50_20).check 54 50 20 = true := by
  change case_54_50_20.check 54 50 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_54_50_21_checked :
    (Witness.linear .positive case_54_50_21).check 54 50 21 = true := by
  change case_54_50_21.check 54 50 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790] }

theorem case_54_50_22_checked :
    (Witness.linear .positive case_54_50_22).check 54 50 22 = true := by
  change case_54_50_22.check 54 50 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700] }

theorem case_54_50_23_checked :
    (Witness.linear .positive case_54_50_23).check 54 50 23 = true := by
  change case_54_50_23.check 54 50 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190] }

theorem case_54_50_24_checked :
    (Witness.linear .positive case_54_50_24).check 54 50 24 = true := by
  change case_54_50_24.check 54 50 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020, 6564120420] }

theorem case_54_50_25_checked :
    (Witness.linear .positive case_54_50_25).check 54 50 25 = true := by
  change case_54_50_25.check 54 50 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 343059613650] }

theorem case_54_50_26_checked :
    (Witness.linear .negative case_54_50_26).check 54 50 26 = true := by
  change case_54_50_26.check 54 50 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_54_50_27_checked :
    (Witness.linear .negative case_54_50_27).check 54 50 27 = true := by
  change case_54_50_27.check 54 50 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_54_50_28_checked :
    (Witness.linear .negative case_54_50_28).check 54 50 28 = true := by
  change case_54_50_28.check 54 50 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_54_50_29_checked :
    (Witness.linear .negative case_54_50_29).check 54 50 29 = true := by
  change case_54_50_29.check 54 50 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_54_50_30_checked :
    (Witness.linear .negative case_54_50_30).check 54 50 30 = true := by
  change case_54_50_30.check 54 50 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_54_50_31_checked :
    (Witness.linear .negative case_54_50_31).check 54 50 31 = true := by
  change case_54_50_31.check 54 50 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_50_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_54_50_32_checked :
    (Witness.linear .negative case_54_50_32).check 54 50 32 = true := by
  change case_54_50_32.check 54 50 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_51_1_checked :
    (Witness.rising).check 54 51 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_51_2_checked :
    (Witness.rising).check 54 51 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_51_3_checked :
    (Witness.rising).check 54 51 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_51_4_checked :
    (Witness.rising).check 54 51 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_51_5_checked :
    (Witness.rising).check 54 51 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_51_6_checked :
    (Witness.rising).check 54 51 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_51_7_checked :
    (Witness.rising).check 54 51 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_51_8_checked :
    (Witness.rising).check 54 51 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_51_9_checked :
    (Witness.rising).check 54 51 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_54_51_10_checked :
    (Witness.linear .positive case_54_51_10).check 54 51 10 = true := by
  change case_54_51_10.check 54 51 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_54_51_11_checked :
    (Witness.linear .positive case_54_51_11).check 54 51 11 = true := by
  change case_54_51_11.check 54 51 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_54_51_12_checked :
    (Witness.linear .positive case_54_51_12).check 54 51 12 = true := by
  change case_54_51_12.check 54 51 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_54_51_13_checked :
    (Witness.linear .positive case_54_51_13).check 54 51 13 = true := by
  change case_54_51_13.check 54 51 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_54_51_14_checked :
    (Witness.linear .positive case_54_51_14).check 54 51 14 = true := by
  change case_54_51_14.check 54 51 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_54_51_15_checked :
    (Witness.linear .positive case_54_51_15).check 54 51 15 = true := by
  change case_54_51_15.check 54 51 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_54_51_16_checked :
    (Witness.linear .positive case_54_51_16).check 54 51 16 = true := by
  change case_54_51_16.check 54 51 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_54_51_17_checked :
    (Witness.linear .positive case_54_51_17).check 54 51 17 = true := by
  change case_54_51_17.check 54 51 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_54_51_18_checked :
    (Witness.linear .positive case_54_51_18).check 54 51 18 = true := by
  change case_54_51_18.check 54 51 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_54_51_19_checked :
    (Witness.linear .positive case_54_51_19).check 54 51 19 = true := by
  change case_54_51_19.check 54 51 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_54_51_20_checked :
    (Witness.linear .positive case_54_51_20).check 54 51 20 = true := by
  change case_54_51_20.check 54 51 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_54_51_21_checked :
    (Witness.linear .positive case_54_51_21).check 54 51 21 = true := by
  change case_54_51_21.check 54 51 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700] }

theorem case_54_51_22_checked :
    (Witness.linear .positive case_54_51_22).check 54 51 22 = true := by
  change case_54_51_22.check 54 51 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190] }

theorem case_54_51_23_checked :
    (Witness.linear .positive case_54_51_23).check 54 51 23 = true := by
  change case_54_51_23.check 54 51 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420] }

theorem case_54_51_24_checked :
    (Witness.linear .positive case_54_51_24).check 54 51 24 = true := by
  change case_54_51_24.check 54 51 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020] }

theorem case_54_51_25_checked :
    (Witness.linear .positive case_54_51_25).check 54 51 25 = true := by
  change case_54_51_25.check 54 51 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 1289904147324] }

theorem case_54_51_26_checked :
    (Witness.linear .negative case_54_51_26).check 54 51 26 = true := by
  change case_54_51_26.check 54 51 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_54_51_27_checked :
    (Witness.linear .negative case_54_51_27).check 54 51 27 = true := by
  change case_54_51_27.check 54 51 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_54_51_28_checked :
    (Witness.linear .negative case_54_51_28).check 54 51 28 = true := by
  change case_54_51_28.check 54 51 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_54_51_29_checked :
    (Witness.linear .negative case_54_51_29).check 54 51 29 = true := by
  change case_54_51_29.check 54 51 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_54_51_30_checked :
    (Witness.linear .negative case_54_51_30).check 54 51 30 = true := by
  change case_54_51_30.check 54 51 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_54_51_31_checked :
    (Witness.linear .negative case_54_51_31).check 54 51 31 = true := by
  change case_54_51_31.check 54 51 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_54_51_32_checked :
    (Witness.linear .negative case_54_51_32).check 54 51 32 = true := by
  change case_54_51_32.check 54 51 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_51_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_54_51_33_checked :
    (Witness.linear .negative case_54_51_33).check 54 51 33 = true := by
  change case_54_51_33.check 54 51 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_52_1_checked :
    (Witness.rising).check 54 52 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_52_2_checked :
    (Witness.rising).check 54 52 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_52_3_checked :
    (Witness.rising).check 54 52 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_52_4_checked :
    (Witness.rising).check 54 52 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_52_5_checked :
    (Witness.rising).check 54 52 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_52_6_checked :
    (Witness.rising).check 54 52 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_52_7_checked :
    (Witness.rising).check 54 52 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_52_8_checked :
    (Witness.rising).check 54 52 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_52_9_checked :
    (Witness.rising).check 54 52 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_54_52_10_checked :
    (Witness.linear .positive case_54_52_10).check 54 52 10 = true := by
  change case_54_52_10.check 54 52 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_54_52_11_checked :
    (Witness.linear .positive case_54_52_11).check 54 52 11 = true := by
  change case_54_52_11.check 54 52 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_54_52_12_checked :
    (Witness.linear .positive case_54_52_12).check 54 52 12 = true := by
  change case_54_52_12.check 54 52 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_54_52_13_checked :
    (Witness.linear .positive case_54_52_13).check 54 52 13 = true := by
  change case_54_52_13.check 54 52 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_54_52_14_checked :
    (Witness.linear .positive case_54_52_14).check 54 52 14 = true := by
  change case_54_52_14.check 54 52 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_54_52_15_checked :
    (Witness.linear .positive case_54_52_15).check 54 52 15 = true := by
  change case_54_52_15.check 54 52 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_54_52_16_checked :
    (Witness.linear .positive case_54_52_16).check 54 52 16 = true := by
  change case_54_52_16.check 54 52 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_54_52_17_checked :
    (Witness.linear .positive case_54_52_17).check 54 52 17 = true := by
  change case_54_52_17.check 54 52 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_54_52_18_checked :
    (Witness.linear .positive case_54_52_18).check 54 52 18 = true := by
  change case_54_52_18.check 54 52 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_54_52_19_checked :
    (Witness.linear .positive case_54_52_19).check 54 52 19 = true := by
  change case_54_52_19.check 54 52 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_54_52_20_checked :
    (Witness.linear .positive case_54_52_20).check 54 52 20 = true := by
  change case_54_52_20.check 54 52 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_54_52_21_checked :
    (Witness.linear .positive case_54_52_21).check 54 52 21 = true := by
  change case_54_52_21.check 54 52 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_54_52_22_checked :
    (Witness.linear .positive case_54_52_22).check 54 52 22 = true := by
  change case_54_52_22.check 54 52 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420] }

theorem case_54_52_23_checked :
    (Witness.linear .positive case_54_52_23).check 54 52 23 = true := by
  change case_54_52_23.check 54 52 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020] }

theorem case_54_52_24_checked :
    (Witness.linear .positive case_54_52_24).check 54 52 24 = true := by
  change case_54_52_24.check 54 52 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640] }

theorem case_54_52_25_checked :
    (Witness.linear .positive case_54_52_25).check 54 52 25 = true := by
  change case_54_52_25.check 54 52 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0, 343059613650] }

theorem case_54_52_26_checked :
    (Witness.linear .positive case_54_52_26).check 54 52 26 = true := by
  change case_54_52_26.check 54 52 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_54_52_27_checked :
    (Witness.linear .negative case_54_52_27).check 54 52 27 = true := by
  change case_54_52_27.check 54 52 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_54_52_28_checked :
    (Witness.linear .negative case_54_52_28).check 54 52 28 = true := by
  change case_54_52_28.check 54 52 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_54_52_29_checked :
    (Witness.linear .negative case_54_52_29).check 54 52 29 = true := by
  change case_54_52_29.check 54 52 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_54_52_30_checked :
    (Witness.linear .negative case_54_52_30).check 54 52 30 = true := by
  change case_54_52_30.check 54 52 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_54_52_31_checked :
    (Witness.linear .negative case_54_52_31).check 54 52 31 = true := by
  change case_54_52_31.check 54 52 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_54_52_32_checked :
    (Witness.linear .negative case_54_52_32).check 54 52 32 = true := by
  change case_54_52_32.check 54 52 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_54_52_33_checked :
    (Witness.linear .negative case_54_52_33).check 54 52 33 = true := by
  change case_54_52_33.check 54 52 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_52_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_54_52_34_checked :
    (Witness.linear .negative case_54_52_34).check 54 52 34 = true := by
  change case_54_52_34.check 54 52 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_53_1_checked :
    (Witness.rising).check 54 53 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_53_2_checked :
    (Witness.rising).check 54 53 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_53_3_checked :
    (Witness.rising).check 54 53 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_53_4_checked :
    (Witness.rising).check 54 53 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_53_5_checked :
    (Witness.rising).check 54 53 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_53_6_checked :
    (Witness.rising).check 54 53 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_53_7_checked :
    (Witness.rising).check 54 53 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_53_8_checked :
    (Witness.rising).check 54 53 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_54_53_9_checked :
    (Witness.rising).check 54 53 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_10_checked :
    (Witness.linear .positive case_54_53_10).check 54 53 10 = true := by
  change case_54_53_10.check 54 53 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_11_checked :
    (Witness.linear .positive case_54_53_11).check 54 53 11 = true := by
  change case_54_53_11.check 54 53 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_12_checked :
    (Witness.linear .positive case_54_53_12).check 54 53 12 = true := by
  change case_54_53_12.check 54 53 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_13_checked :
    (Witness.linear .positive case_54_53_13).check 54 53 13 = true := by
  change case_54_53_13.check 54 53 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_14_checked :
    (Witness.linear .positive case_54_53_14).check 54 53 14 = true := by
  change case_54_53_14.check 54 53 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_15_checked :
    (Witness.linear .positive case_54_53_15).check 54 53 15 = true := by
  change case_54_53_15.check 54 53 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_16_checked :
    (Witness.linear .positive case_54_53_16).check 54 53 16 = true := by
  change case_54_53_16.check 54 53 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_17_checked :
    (Witness.linear .positive case_54_53_17).check 54 53 17 = true := by
  change case_54_53_17.check 54 53 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_18_checked :
    (Witness.linear .positive case_54_53_18).check 54 53 18 = true := by
  change case_54_53_18.check 54 53 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_19_checked :
    (Witness.linear .positive case_54_53_19).check 54 53 19 = true := by
  change case_54_53_19.check 54 53 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_20_checked :
    (Witness.linear .positive case_54_53_20).check 54 53 20 = true := by
  change case_54_53_20.check 54 53 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_21_checked :
    (Witness.linear .positive case_54_53_21).check 54 53 21 = true := by
  change case_54_53_21.check 54 53 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_22_checked :
    (Witness.linear .positive case_54_53_22).check 54 53 22 = true := by
  change case_54_53_22.check 54 53 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_23_checked :
    (Witness.linear .positive case_54_53_23).check 54 53 23 = true := by
  change case_54_53_23.check 54 53 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_24_checked :
    (Witness.linear .positive case_54_53_24).check 54 53 24 = true := by
  change case_54_53_24.check 54 53 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_25_checked :
    (Witness.linear .positive case_54_53_25).check 54 53 25 = true := by
  change case_54_53_25.check 54 53 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_26_checked :
    (Witness.linear .positive case_54_53_26).check 54 53 26 = true := by
  change case_54_53_26.check 54 53 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_27_checked :
    (Witness.linear .negative case_54_53_27).check 54 53 27 = true := by
  change case_54_53_27.check 54 53 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_28_checked :
    (Witness.linear .negative case_54_53_28).check 54 53 28 = true := by
  change case_54_53_28.check 54 53 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_29_checked :
    (Witness.linear .negative case_54_53_29).check 54 53 29 = true := by
  change case_54_53_29.check 54 53 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_30_checked :
    (Witness.linear .negative case_54_53_30).check 54 53 30 = true := by
  change case_54_53_30.check 54 53 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_31_checked :
    (Witness.linear .negative case_54_53_31).check 54 53 31 = true := by
  change case_54_53_31.check 54 53 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_32_checked :
    (Witness.linear .negative case_54_53_32).check 54 53 32 = true := by
  change case_54_53_32.check 54 53 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_33_checked :
    (Witness.linear .negative case_54_53_33).check 54 53 33 = true := by
  change case_54_53_33.check 54 53 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_54_53_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_54_53_34_checked :
    (Witness.linear .negative case_54_53_34).check 54 53 34 = true := by
  change case_54_53_34.check 54 53 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_54 (a k : ℕ) (h : Domain 54 a k) :
    ∃ w : Witness, w.check 54 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 27 ≤ a := by omega
  have haHi : a ≤ 53 := by omega
  interval_cases a

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_27_1_checked⟩

    · exact ⟨Witness.rising, case_54_27_2_checked⟩

    · exact ⟨Witness.rising, case_54_27_3_checked⟩

    · exact ⟨Witness.rising, case_54_27_4_checked⟩

    · exact ⟨Witness.rising, case_54_27_5_checked⟩

    · exact ⟨Witness.rising, case_54_27_6_checked⟩

    · exact ⟨Witness.rising, case_54_27_7_checked⟩

    · exact ⟨Witness.rising, case_54_27_8_checked⟩

    · exact ⟨Witness.rising, case_54_27_9_checked⟩

    · exact ⟨Witness.rising, case_54_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_27_11, case_54_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_27_12, case_54_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_27_13, case_54_27_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_27_14, case_54_27_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_27_15, case_54_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_54_27_16, case_54_27_16_checked⟩

    · exact ⟨Witness.linear .conditional case_54_27_17, case_54_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_28_1_checked⟩

    · exact ⟨Witness.rising, case_54_28_2_checked⟩

    · exact ⟨Witness.rising, case_54_28_3_checked⟩

    · exact ⟨Witness.rising, case_54_28_4_checked⟩

    · exact ⟨Witness.rising, case_54_28_5_checked⟩

    · exact ⟨Witness.rising, case_54_28_6_checked⟩

    · exact ⟨Witness.rising, case_54_28_7_checked⟩

    · exact ⟨Witness.rising, case_54_28_8_checked⟩

    · exact ⟨Witness.rising, case_54_28_9_checked⟩

    · exact ⟨Witness.rising, case_54_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_28_11, case_54_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_28_12, case_54_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_28_13, case_54_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_28_14, case_54_28_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_28_15, case_54_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_54_28_16, case_54_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_54_28_17, case_54_28_17_checked⟩

    · exact ⟨Witness.linear .conditional case_54_28_18, case_54_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_29_1_checked⟩

    · exact ⟨Witness.rising, case_54_29_2_checked⟩

    · exact ⟨Witness.rising, case_54_29_3_checked⟩

    · exact ⟨Witness.rising, case_54_29_4_checked⟩

    · exact ⟨Witness.rising, case_54_29_5_checked⟩

    · exact ⟨Witness.rising, case_54_29_6_checked⟩

    · exact ⟨Witness.rising, case_54_29_7_checked⟩

    · exact ⟨Witness.rising, case_54_29_8_checked⟩

    · exact ⟨Witness.rising, case_54_29_9_checked⟩

    · exact ⟨Witness.rising, case_54_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_29_11, case_54_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_29_12, case_54_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_29_13, case_54_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_29_14, case_54_29_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_29_15, case_54_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_54_29_16, case_54_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_54_29_17, case_54_29_17_checked⟩

    · exact ⟨Witness.linear .conditional case_54_29_18, case_54_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_30_1_checked⟩

    · exact ⟨Witness.rising, case_54_30_2_checked⟩

    · exact ⟨Witness.rising, case_54_30_3_checked⟩

    · exact ⟨Witness.rising, case_54_30_4_checked⟩

    · exact ⟨Witness.rising, case_54_30_5_checked⟩

    · exact ⟨Witness.rising, case_54_30_6_checked⟩

    · exact ⟨Witness.rising, case_54_30_7_checked⟩

    · exact ⟨Witness.rising, case_54_30_8_checked⟩

    · exact ⟨Witness.rising, case_54_30_9_checked⟩

    · exact ⟨Witness.rising, case_54_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_30_11, case_54_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_30_12, case_54_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_30_13, case_54_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_30_14, case_54_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_30_15, case_54_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_54_30_16, case_54_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_54_30_17, case_54_30_17_checked⟩

    · exact ⟨Witness.linear .conditional case_54_30_18, case_54_30_18_checked⟩

    · exact ⟨Witness.linear .conditional case_54_30_19, case_54_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_31_1_checked⟩

    · exact ⟨Witness.rising, case_54_31_2_checked⟩

    · exact ⟨Witness.rising, case_54_31_3_checked⟩

    · exact ⟨Witness.rising, case_54_31_4_checked⟩

    · exact ⟨Witness.rising, case_54_31_5_checked⟩

    · exact ⟨Witness.rising, case_54_31_6_checked⟩

    · exact ⟨Witness.rising, case_54_31_7_checked⟩

    · exact ⟨Witness.rising, case_54_31_8_checked⟩

    · exact ⟨Witness.rising, case_54_31_9_checked⟩

    · exact ⟨Witness.rising, case_54_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_31_11, case_54_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_31_12, case_54_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_31_13, case_54_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_31_14, case_54_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_31_15, case_54_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_54_31_16, case_54_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_54_31_17, case_54_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_54_31_18, case_54_31_18_checked⟩

    · exact ⟨Witness.linear .conditional case_54_31_19, case_54_31_19_checked⟩

    · exact ⟨Witness.linear .conditional case_54_31_20, case_54_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_32_1_checked⟩

    · exact ⟨Witness.rising, case_54_32_2_checked⟩

    · exact ⟨Witness.rising, case_54_32_3_checked⟩

    · exact ⟨Witness.rising, case_54_32_4_checked⟩

    · exact ⟨Witness.rising, case_54_32_5_checked⟩

    · exact ⟨Witness.rising, case_54_32_6_checked⟩

    · exact ⟨Witness.rising, case_54_32_7_checked⟩

    · exact ⟨Witness.rising, case_54_32_8_checked⟩

    · exact ⟨Witness.rising, case_54_32_9_checked⟩

    · exact ⟨Witness.rising, case_54_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_32_11, case_54_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_32_12, case_54_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_32_13, case_54_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_32_14, case_54_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_32_15, case_54_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_54_32_16, case_54_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_54_32_17, case_54_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_54_32_18, case_54_32_18_checked⟩

    · exact ⟨Witness.linear .conditional case_54_32_19, case_54_32_19_checked⟩

    · exact ⟨Witness.linear .conditional case_54_32_20, case_54_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_33_1_checked⟩

    · exact ⟨Witness.rising, case_54_33_2_checked⟩

    · exact ⟨Witness.rising, case_54_33_3_checked⟩

    · exact ⟨Witness.rising, case_54_33_4_checked⟩

    · exact ⟨Witness.rising, case_54_33_5_checked⟩

    · exact ⟨Witness.rising, case_54_33_6_checked⟩

    · exact ⟨Witness.rising, case_54_33_7_checked⟩

    · exact ⟨Witness.rising, case_54_33_8_checked⟩

    · exact ⟨Witness.rising, case_54_33_9_checked⟩

    · exact ⟨Witness.rising, case_54_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_33_11, case_54_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_33_12, case_54_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_33_13, case_54_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_33_14, case_54_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_33_15, case_54_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_33_16, case_54_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_54_33_17, case_54_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_54_33_18, case_54_33_18_checked⟩

    · exact ⟨Witness.linear .conditional case_54_33_19, case_54_33_19_checked⟩

    · exact ⟨Witness.linear .conditional case_54_33_20, case_54_33_20_checked⟩

    · exact ⟨Witness.linear .conditional case_54_33_21, case_54_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_34_1_checked⟩

    · exact ⟨Witness.rising, case_54_34_2_checked⟩

    · exact ⟨Witness.rising, case_54_34_3_checked⟩

    · exact ⟨Witness.rising, case_54_34_4_checked⟩

    · exact ⟨Witness.rising, case_54_34_5_checked⟩

    · exact ⟨Witness.rising, case_54_34_6_checked⟩

    · exact ⟨Witness.rising, case_54_34_7_checked⟩

    · exact ⟨Witness.rising, case_54_34_8_checked⟩

    · exact ⟨Witness.rising, case_54_34_9_checked⟩

    · exact ⟨Witness.rising, case_54_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_34_11, case_54_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_34_12, case_54_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_34_13, case_54_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_34_14, case_54_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_34_15, case_54_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_34_16, case_54_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_54_34_17, case_54_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_54_34_18, case_54_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_54_34_19, case_54_34_19_checked⟩

    · exact ⟨Witness.linear .conditional case_54_34_20, case_54_34_20_checked⟩

    · exact ⟨Witness.linear .conditional case_54_34_21, case_54_34_21_checked⟩

    · exact ⟨Witness.linear .conditional case_54_34_22, case_54_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_35_1_checked⟩

    · exact ⟨Witness.rising, case_54_35_2_checked⟩

    · exact ⟨Witness.rising, case_54_35_3_checked⟩

    · exact ⟨Witness.rising, case_54_35_4_checked⟩

    · exact ⟨Witness.rising, case_54_35_5_checked⟩

    · exact ⟨Witness.rising, case_54_35_6_checked⟩

    · exact ⟨Witness.rising, case_54_35_7_checked⟩

    · exact ⟨Witness.rising, case_54_35_8_checked⟩

    · exact ⟨Witness.rising, case_54_35_9_checked⟩

    · exact ⟨Witness.rising, case_54_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_35_11, case_54_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_35_12, case_54_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_35_13, case_54_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_35_14, case_54_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_35_15, case_54_35_15_checked⟩

    · exact ⟨Witness.linear .conditional case_54_35_16, case_54_35_16_checked⟩

    · exact ⟨Witness.linear .conditional case_54_35_17, case_54_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_54_35_18, case_54_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_54_35_19, case_54_35_19_checked⟩

    · exact ⟨Witness.linear .conditional case_54_35_20, case_54_35_20_checked⟩

    · exact ⟨Witness.linear .conditional case_54_35_21, case_54_35_21_checked⟩

    · exact ⟨Witness.linear .conditional case_54_35_22, case_54_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_36_1_checked⟩

    · exact ⟨Witness.rising, case_54_36_2_checked⟩

    · exact ⟨Witness.rising, case_54_36_3_checked⟩

    · exact ⟨Witness.rising, case_54_36_4_checked⟩

    · exact ⟨Witness.rising, case_54_36_5_checked⟩

    · exact ⟨Witness.rising, case_54_36_6_checked⟩

    · exact ⟨Witness.rising, case_54_36_7_checked⟩

    · exact ⟨Witness.rising, case_54_36_8_checked⟩

    · exact ⟨Witness.rising, case_54_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_36_10, case_54_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_36_11, case_54_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_36_12, case_54_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_36_13, case_54_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_36_14, case_54_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_36_15, case_54_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_36_16, case_54_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_36_17, case_54_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_54_36_18, case_54_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_54_36_19, case_54_36_19_checked⟩

    · exact ⟨Witness.linear .conditional case_54_36_20, case_54_36_20_checked⟩

    · exact ⟨Witness.linear .conditional case_54_36_21, case_54_36_21_checked⟩

    · exact ⟨Witness.linear .conditional case_54_36_22, case_54_36_22_checked⟩

    · exact ⟨Witness.linear .conditional case_54_36_23, case_54_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_37_1_checked⟩

    · exact ⟨Witness.rising, case_54_37_2_checked⟩

    · exact ⟨Witness.rising, case_54_37_3_checked⟩

    · exact ⟨Witness.rising, case_54_37_4_checked⟩

    · exact ⟨Witness.rising, case_54_37_5_checked⟩

    · exact ⟨Witness.rising, case_54_37_6_checked⟩

    · exact ⟨Witness.rising, case_54_37_7_checked⟩

    · exact ⟨Witness.rising, case_54_37_8_checked⟩

    · exact ⟨Witness.rising, case_54_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_37_10, case_54_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_37_11, case_54_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_37_12, case_54_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_37_13, case_54_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_37_14, case_54_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_37_15, case_54_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_37_16, case_54_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_37_17, case_54_37_17_checked⟩

    · exact ⟨Witness.linear .conditional case_54_37_18, case_54_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_54_37_19, case_54_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_54_37_20, case_54_37_20_checked⟩

    · exact ⟨Witness.linear .conditional case_54_37_21, case_54_37_21_checked⟩

    · exact ⟨Witness.linear .conditional case_54_37_22, case_54_37_22_checked⟩

    · exact ⟨Witness.linear .conditional case_54_37_23, case_54_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_54_37_24, case_54_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_38_1_checked⟩

    · exact ⟨Witness.rising, case_54_38_2_checked⟩

    · exact ⟨Witness.rising, case_54_38_3_checked⟩

    · exact ⟨Witness.rising, case_54_38_4_checked⟩

    · exact ⟨Witness.rising, case_54_38_5_checked⟩

    · exact ⟨Witness.rising, case_54_38_6_checked⟩

    · exact ⟨Witness.rising, case_54_38_7_checked⟩

    · exact ⟨Witness.rising, case_54_38_8_checked⟩

    · exact ⟨Witness.rising, case_54_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_38_10, case_54_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_38_11, case_54_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_38_12, case_54_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_38_13, case_54_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_38_14, case_54_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_38_15, case_54_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_38_16, case_54_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_38_17, case_54_38_17_checked⟩

    · exact ⟨Witness.linear .conditional case_54_38_18, case_54_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_54_38_19, case_54_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_54_38_20, case_54_38_20_checked⟩

    · exact ⟨Witness.linear .conditional case_54_38_21, case_54_38_21_checked⟩

    · exact ⟨Witness.linear .conditional case_54_38_22, case_54_38_22_checked⟩

    · exact ⟨Witness.linear .conditional case_54_38_23, case_54_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_54_38_24, case_54_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_39_1_checked⟩

    · exact ⟨Witness.rising, case_54_39_2_checked⟩

    · exact ⟨Witness.rising, case_54_39_3_checked⟩

    · exact ⟨Witness.rising, case_54_39_4_checked⟩

    · exact ⟨Witness.rising, case_54_39_5_checked⟩

    · exact ⟨Witness.rising, case_54_39_6_checked⟩

    · exact ⟨Witness.rising, case_54_39_7_checked⟩

    · exact ⟨Witness.rising, case_54_39_8_checked⟩

    · exact ⟨Witness.rising, case_54_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_39_10, case_54_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_39_11, case_54_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_39_12, case_54_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_39_13, case_54_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_39_14, case_54_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_39_15, case_54_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_39_16, case_54_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_39_17, case_54_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_39_18, case_54_39_18_checked⟩

    · exact ⟨Witness.linear .conditional case_54_39_19, case_54_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_54_39_20, case_54_39_20_checked⟩

    · exact ⟨Witness.linear .conditional case_54_39_21, case_54_39_21_checked⟩

    · exact ⟨Witness.linear .conditional case_54_39_22, case_54_39_22_checked⟩

    · exact ⟨Witness.linear .conditional case_54_39_23, case_54_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_54_39_24, case_54_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_54_39_25, case_54_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_40_1_checked⟩

    · exact ⟨Witness.rising, case_54_40_2_checked⟩

    · exact ⟨Witness.rising, case_54_40_3_checked⟩

    · exact ⟨Witness.rising, case_54_40_4_checked⟩

    · exact ⟨Witness.rising, case_54_40_5_checked⟩

    · exact ⟨Witness.rising, case_54_40_6_checked⟩

    · exact ⟨Witness.rising, case_54_40_7_checked⟩

    · exact ⟨Witness.rising, case_54_40_8_checked⟩

    · exact ⟨Witness.rising, case_54_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_40_10, case_54_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_40_11, case_54_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_40_12, case_54_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_40_13, case_54_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_40_14, case_54_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_40_15, case_54_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_40_16, case_54_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_40_17, case_54_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_40_18, case_54_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_40_19, case_54_40_19_checked⟩

    · exact ⟨Witness.linear .conditional case_54_40_20, case_54_40_20_checked⟩

    · exact ⟨Witness.linear .conditional case_54_40_21, case_54_40_21_checked⟩

    · exact ⟨Witness.linear .conditional case_54_40_22, case_54_40_22_checked⟩

    · exact ⟨Witness.linear .conditional case_54_40_23, case_54_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_54_40_24, case_54_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_54_40_25, case_54_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_40_26, case_54_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_41_1_checked⟩

    · exact ⟨Witness.rising, case_54_41_2_checked⟩

    · exact ⟨Witness.rising, case_54_41_3_checked⟩

    · exact ⟨Witness.rising, case_54_41_4_checked⟩

    · exact ⟨Witness.rising, case_54_41_5_checked⟩

    · exact ⟨Witness.rising, case_54_41_6_checked⟩

    · exact ⟨Witness.rising, case_54_41_7_checked⟩

    · exact ⟨Witness.rising, case_54_41_8_checked⟩

    · exact ⟨Witness.rising, case_54_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_41_10, case_54_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_41_11, case_54_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_41_12, case_54_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_41_13, case_54_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_41_14, case_54_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_41_15, case_54_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_41_16, case_54_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_41_17, case_54_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_41_18, case_54_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_41_19, case_54_41_19_checked⟩

    · exact ⟨Witness.linear .conditional case_54_41_20, case_54_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_54_41_21, case_54_41_21_checked⟩

    · exact ⟨Witness.linear .conditional case_54_41_22, case_54_41_22_checked⟩

    · exact ⟨Witness.linear .conditional case_54_41_23, case_54_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_54_41_24, case_54_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_54_41_25, case_54_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_41_26, case_54_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_42_1_checked⟩

    · exact ⟨Witness.rising, case_54_42_2_checked⟩

    · exact ⟨Witness.rising, case_54_42_3_checked⟩

    · exact ⟨Witness.rising, case_54_42_4_checked⟩

    · exact ⟨Witness.rising, case_54_42_5_checked⟩

    · exact ⟨Witness.rising, case_54_42_6_checked⟩

    · exact ⟨Witness.rising, case_54_42_7_checked⟩

    · exact ⟨Witness.rising, case_54_42_8_checked⟩

    · exact ⟨Witness.rising, case_54_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_42_10, case_54_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_42_11, case_54_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_42_12, case_54_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_42_13, case_54_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_42_14, case_54_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_42_15, case_54_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_42_16, case_54_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_42_17, case_54_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_42_18, case_54_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_42_19, case_54_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_42_20, case_54_42_20_checked⟩

    · exact ⟨Witness.linear .conditional case_54_42_21, case_54_42_21_checked⟩

    · exact ⟨Witness.linear .conditional case_54_42_22, case_54_42_22_checked⟩

    · exact ⟨Witness.linear .conditional case_54_42_23, case_54_42_23_checked⟩

    · exact ⟨Witness.linear .conditional case_54_42_24, case_54_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_54_42_25, case_54_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_42_26, case_54_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_42_27, case_54_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_43_1_checked⟩

    · exact ⟨Witness.rising, case_54_43_2_checked⟩

    · exact ⟨Witness.rising, case_54_43_3_checked⟩

    · exact ⟨Witness.rising, case_54_43_4_checked⟩

    · exact ⟨Witness.rising, case_54_43_5_checked⟩

    · exact ⟨Witness.rising, case_54_43_6_checked⟩

    · exact ⟨Witness.rising, case_54_43_7_checked⟩

    · exact ⟨Witness.rising, case_54_43_8_checked⟩

    · exact ⟨Witness.rising, case_54_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_10, case_54_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_11, case_54_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_12, case_54_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_13, case_54_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_14, case_54_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_15, case_54_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_16, case_54_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_17, case_54_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_18, case_54_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_19, case_54_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_20, case_54_43_20_checked⟩

    · exact ⟨Witness.linear .positive case_54_43_21, case_54_43_21_checked⟩

    · exact ⟨Witness.linear .conditional case_54_43_22, case_54_43_22_checked⟩

    · exact ⟨Witness.linear .conditional case_54_43_23, case_54_43_23_checked⟩

    · exact ⟨Witness.linear .conditional case_54_43_24, case_54_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_54_43_25, case_54_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_43_26, case_54_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_43_27, case_54_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_54_43_28, case_54_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_44_1_checked⟩

    · exact ⟨Witness.rising, case_54_44_2_checked⟩

    · exact ⟨Witness.rising, case_54_44_3_checked⟩

    · exact ⟨Witness.rising, case_54_44_4_checked⟩

    · exact ⟨Witness.rising, case_54_44_5_checked⟩

    · exact ⟨Witness.rising, case_54_44_6_checked⟩

    · exact ⟨Witness.rising, case_54_44_7_checked⟩

    · exact ⟨Witness.rising, case_54_44_8_checked⟩

    · exact ⟨Witness.rising, case_54_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_10, case_54_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_11, case_54_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_12, case_54_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_13, case_54_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_14, case_54_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_15, case_54_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_16, case_54_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_17, case_54_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_18, case_54_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_19, case_54_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_20, case_54_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_54_44_21, case_54_44_21_checked⟩

    · exact ⟨Witness.linear .conditional case_54_44_22, case_54_44_22_checked⟩

    · exact ⟨Witness.linear .conditional case_54_44_23, case_54_44_23_checked⟩

    · exact ⟨Witness.linear .conditional case_54_44_24, case_54_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_54_44_25, case_54_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_44_26, case_54_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_44_27, case_54_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_54_44_28, case_54_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_45_1_checked⟩

    · exact ⟨Witness.rising, case_54_45_2_checked⟩

    · exact ⟨Witness.rising, case_54_45_3_checked⟩

    · exact ⟨Witness.rising, case_54_45_4_checked⟩

    · exact ⟨Witness.rising, case_54_45_5_checked⟩

    · exact ⟨Witness.rising, case_54_45_6_checked⟩

    · exact ⟨Witness.rising, case_54_45_7_checked⟩

    · exact ⟨Witness.rising, case_54_45_8_checked⟩

    · exact ⟨Witness.rising, case_54_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_10, case_54_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_11, case_54_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_12, case_54_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_13, case_54_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_14, case_54_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_15, case_54_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_16, case_54_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_17, case_54_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_18, case_54_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_19, case_54_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_20, case_54_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_21, case_54_45_21_checked⟩

    · exact ⟨Witness.linear .positive case_54_45_22, case_54_45_22_checked⟩

    · exact ⟨Witness.linear .conditional case_54_45_23, case_54_45_23_checked⟩

    · exact ⟨Witness.linear .conditional case_54_45_24, case_54_45_24_checked⟩

    · exact ⟨Witness.linear .negative case_54_45_25, case_54_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_45_26, case_54_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_45_27, case_54_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_54_45_28, case_54_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_54_45_29, case_54_45_29_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_46_1_checked⟩

    · exact ⟨Witness.rising, case_54_46_2_checked⟩

    · exact ⟨Witness.rising, case_54_46_3_checked⟩

    · exact ⟨Witness.rising, case_54_46_4_checked⟩

    · exact ⟨Witness.rising, case_54_46_5_checked⟩

    · exact ⟨Witness.rising, case_54_46_6_checked⟩

    · exact ⟨Witness.rising, case_54_46_7_checked⟩

    · exact ⟨Witness.rising, case_54_46_8_checked⟩

    · exact ⟨Witness.rising, case_54_46_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_10, case_54_46_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_11, case_54_46_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_12, case_54_46_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_13, case_54_46_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_14, case_54_46_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_15, case_54_46_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_16, case_54_46_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_17, case_54_46_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_18, case_54_46_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_19, case_54_46_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_20, case_54_46_20_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_21, case_54_46_21_checked⟩

    · exact ⟨Witness.linear .positive case_54_46_22, case_54_46_22_checked⟩

    · exact ⟨Witness.linear .conditional case_54_46_23, case_54_46_23_checked⟩

    · exact ⟨Witness.linear .conditional case_54_46_24, case_54_46_24_checked⟩

    · exact ⟨Witness.linear .negative case_54_46_25, case_54_46_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_46_26, case_54_46_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_46_27, case_54_46_27_checked⟩

    · exact ⟨Witness.linear .negative case_54_46_28, case_54_46_28_checked⟩

    · exact ⟨Witness.linear .negative case_54_46_29, case_54_46_29_checked⟩

    · exact ⟨Witness.linear .negative case_54_46_30, case_54_46_30_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_47_1_checked⟩

    · exact ⟨Witness.rising, case_54_47_2_checked⟩

    · exact ⟨Witness.rising, case_54_47_3_checked⟩

    · exact ⟨Witness.rising, case_54_47_4_checked⟩

    · exact ⟨Witness.rising, case_54_47_5_checked⟩

    · exact ⟨Witness.rising, case_54_47_6_checked⟩

    · exact ⟨Witness.rising, case_54_47_7_checked⟩

    · exact ⟨Witness.rising, case_54_47_8_checked⟩

    · exact ⟨Witness.rising, case_54_47_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_10, case_54_47_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_11, case_54_47_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_12, case_54_47_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_13, case_54_47_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_14, case_54_47_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_15, case_54_47_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_16, case_54_47_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_17, case_54_47_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_18, case_54_47_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_19, case_54_47_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_20, case_54_47_20_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_21, case_54_47_21_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_22, case_54_47_22_checked⟩

    · exact ⟨Witness.linear .positive case_54_47_23, case_54_47_23_checked⟩

    · exact ⟨Witness.linear .conditional case_54_47_24, case_54_47_24_checked⟩

    · exact ⟨Witness.linear .negative case_54_47_25, case_54_47_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_47_26, case_54_47_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_47_27, case_54_47_27_checked⟩

    · exact ⟨Witness.linear .negative case_54_47_28, case_54_47_28_checked⟩

    · exact ⟨Witness.linear .negative case_54_47_29, case_54_47_29_checked⟩

    · exact ⟨Witness.linear .negative case_54_47_30, case_54_47_30_checked⟩

  · have hkHi : k ≤ 31 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_48_1_checked⟩

    · exact ⟨Witness.rising, case_54_48_2_checked⟩

    · exact ⟨Witness.rising, case_54_48_3_checked⟩

    · exact ⟨Witness.rising, case_54_48_4_checked⟩

    · exact ⟨Witness.rising, case_54_48_5_checked⟩

    · exact ⟨Witness.rising, case_54_48_6_checked⟩

    · exact ⟨Witness.rising, case_54_48_7_checked⟩

    · exact ⟨Witness.rising, case_54_48_8_checked⟩

    · exact ⟨Witness.rising, case_54_48_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_10, case_54_48_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_11, case_54_48_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_12, case_54_48_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_13, case_54_48_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_14, case_54_48_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_15, case_54_48_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_16, case_54_48_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_17, case_54_48_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_18, case_54_48_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_19, case_54_48_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_20, case_54_48_20_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_21, case_54_48_21_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_22, case_54_48_22_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_23, case_54_48_23_checked⟩

    · exact ⟨Witness.linear .positive case_54_48_24, case_54_48_24_checked⟩

    · exact ⟨Witness.linear .negative case_54_48_25, case_54_48_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_48_26, case_54_48_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_48_27, case_54_48_27_checked⟩

    · exact ⟨Witness.linear .negative case_54_48_28, case_54_48_28_checked⟩

    · exact ⟨Witness.linear .negative case_54_48_29, case_54_48_29_checked⟩

    · exact ⟨Witness.linear .negative case_54_48_30, case_54_48_30_checked⟩

    · exact ⟨Witness.linear .negative case_54_48_31, case_54_48_31_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_49_1_checked⟩

    · exact ⟨Witness.rising, case_54_49_2_checked⟩

    · exact ⟨Witness.rising, case_54_49_3_checked⟩

    · exact ⟨Witness.rising, case_54_49_4_checked⟩

    · exact ⟨Witness.rising, case_54_49_5_checked⟩

    · exact ⟨Witness.rising, case_54_49_6_checked⟩

    · exact ⟨Witness.rising, case_54_49_7_checked⟩

    · exact ⟨Witness.rising, case_54_49_8_checked⟩

    · exact ⟨Witness.rising, case_54_49_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_10, case_54_49_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_11, case_54_49_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_12, case_54_49_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_13, case_54_49_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_14, case_54_49_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_15, case_54_49_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_16, case_54_49_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_17, case_54_49_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_18, case_54_49_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_19, case_54_49_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_20, case_54_49_20_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_21, case_54_49_21_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_22, case_54_49_22_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_23, case_54_49_23_checked⟩

    · exact ⟨Witness.linear .positive case_54_49_24, case_54_49_24_checked⟩

    · exact ⟨Witness.linear .conditional case_54_49_25, case_54_49_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_49_26, case_54_49_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_49_27, case_54_49_27_checked⟩

    · exact ⟨Witness.linear .negative case_54_49_28, case_54_49_28_checked⟩

    · exact ⟨Witness.linear .negative case_54_49_29, case_54_49_29_checked⟩

    · exact ⟨Witness.linear .negative case_54_49_30, case_54_49_30_checked⟩

    · exact ⟨Witness.linear .negative case_54_49_31, case_54_49_31_checked⟩

    · exact ⟨Witness.linear .negative case_54_49_32, case_54_49_32_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_50_1_checked⟩

    · exact ⟨Witness.rising, case_54_50_2_checked⟩

    · exact ⟨Witness.rising, case_54_50_3_checked⟩

    · exact ⟨Witness.rising, case_54_50_4_checked⟩

    · exact ⟨Witness.rising, case_54_50_5_checked⟩

    · exact ⟨Witness.rising, case_54_50_6_checked⟩

    · exact ⟨Witness.rising, case_54_50_7_checked⟩

    · exact ⟨Witness.rising, case_54_50_8_checked⟩

    · exact ⟨Witness.rising, case_54_50_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_10, case_54_50_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_11, case_54_50_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_12, case_54_50_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_13, case_54_50_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_14, case_54_50_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_15, case_54_50_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_16, case_54_50_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_17, case_54_50_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_18, case_54_50_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_19, case_54_50_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_20, case_54_50_20_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_21, case_54_50_21_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_22, case_54_50_22_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_23, case_54_50_23_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_24, case_54_50_24_checked⟩

    · exact ⟨Witness.linear .positive case_54_50_25, case_54_50_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_50_26, case_54_50_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_50_27, case_54_50_27_checked⟩

    · exact ⟨Witness.linear .negative case_54_50_28, case_54_50_28_checked⟩

    · exact ⟨Witness.linear .negative case_54_50_29, case_54_50_29_checked⟩

    · exact ⟨Witness.linear .negative case_54_50_30, case_54_50_30_checked⟩

    · exact ⟨Witness.linear .negative case_54_50_31, case_54_50_31_checked⟩

    · exact ⟨Witness.linear .negative case_54_50_32, case_54_50_32_checked⟩

  · have hkHi : k ≤ 33 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_51_1_checked⟩

    · exact ⟨Witness.rising, case_54_51_2_checked⟩

    · exact ⟨Witness.rising, case_54_51_3_checked⟩

    · exact ⟨Witness.rising, case_54_51_4_checked⟩

    · exact ⟨Witness.rising, case_54_51_5_checked⟩

    · exact ⟨Witness.rising, case_54_51_6_checked⟩

    · exact ⟨Witness.rising, case_54_51_7_checked⟩

    · exact ⟨Witness.rising, case_54_51_8_checked⟩

    · exact ⟨Witness.rising, case_54_51_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_10, case_54_51_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_11, case_54_51_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_12, case_54_51_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_13, case_54_51_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_14, case_54_51_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_15, case_54_51_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_16, case_54_51_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_17, case_54_51_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_18, case_54_51_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_19, case_54_51_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_20, case_54_51_20_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_21, case_54_51_21_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_22, case_54_51_22_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_23, case_54_51_23_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_24, case_54_51_24_checked⟩

    · exact ⟨Witness.linear .positive case_54_51_25, case_54_51_25_checked⟩

    · exact ⟨Witness.linear .negative case_54_51_26, case_54_51_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_51_27, case_54_51_27_checked⟩

    · exact ⟨Witness.linear .negative case_54_51_28, case_54_51_28_checked⟩

    · exact ⟨Witness.linear .negative case_54_51_29, case_54_51_29_checked⟩

    · exact ⟨Witness.linear .negative case_54_51_30, case_54_51_30_checked⟩

    · exact ⟨Witness.linear .negative case_54_51_31, case_54_51_31_checked⟩

    · exact ⟨Witness.linear .negative case_54_51_32, case_54_51_32_checked⟩

    · exact ⟨Witness.linear .negative case_54_51_33, case_54_51_33_checked⟩

  · have hkHi : k ≤ 34 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_52_1_checked⟩

    · exact ⟨Witness.rising, case_54_52_2_checked⟩

    · exact ⟨Witness.rising, case_54_52_3_checked⟩

    · exact ⟨Witness.rising, case_54_52_4_checked⟩

    · exact ⟨Witness.rising, case_54_52_5_checked⟩

    · exact ⟨Witness.rising, case_54_52_6_checked⟩

    · exact ⟨Witness.rising, case_54_52_7_checked⟩

    · exact ⟨Witness.rising, case_54_52_8_checked⟩

    · exact ⟨Witness.rising, case_54_52_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_10, case_54_52_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_11, case_54_52_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_12, case_54_52_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_13, case_54_52_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_14, case_54_52_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_15, case_54_52_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_16, case_54_52_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_17, case_54_52_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_18, case_54_52_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_19, case_54_52_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_20, case_54_52_20_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_21, case_54_52_21_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_22, case_54_52_22_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_23, case_54_52_23_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_24, case_54_52_24_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_25, case_54_52_25_checked⟩

    · exact ⟨Witness.linear .positive case_54_52_26, case_54_52_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_52_27, case_54_52_27_checked⟩

    · exact ⟨Witness.linear .negative case_54_52_28, case_54_52_28_checked⟩

    · exact ⟨Witness.linear .negative case_54_52_29, case_54_52_29_checked⟩

    · exact ⟨Witness.linear .negative case_54_52_30, case_54_52_30_checked⟩

    · exact ⟨Witness.linear .negative case_54_52_31, case_54_52_31_checked⟩

    · exact ⟨Witness.linear .negative case_54_52_32, case_54_52_32_checked⟩

    · exact ⟨Witness.linear .negative case_54_52_33, case_54_52_33_checked⟩

    · exact ⟨Witness.linear .negative case_54_52_34, case_54_52_34_checked⟩

  · have hkHi : k ≤ 34 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_54_53_1_checked⟩

    · exact ⟨Witness.rising, case_54_53_2_checked⟩

    · exact ⟨Witness.rising, case_54_53_3_checked⟩

    · exact ⟨Witness.rising, case_54_53_4_checked⟩

    · exact ⟨Witness.rising, case_54_53_5_checked⟩

    · exact ⟨Witness.rising, case_54_53_6_checked⟩

    · exact ⟨Witness.rising, case_54_53_7_checked⟩

    · exact ⟨Witness.rising, case_54_53_8_checked⟩

    · exact ⟨Witness.rising, case_54_53_9_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_10, case_54_53_10_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_11, case_54_53_11_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_12, case_54_53_12_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_13, case_54_53_13_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_14, case_54_53_14_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_15, case_54_53_15_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_16, case_54_53_16_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_17, case_54_53_17_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_18, case_54_53_18_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_19, case_54_53_19_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_20, case_54_53_20_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_21, case_54_53_21_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_22, case_54_53_22_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_23, case_54_53_23_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_24, case_54_53_24_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_25, case_54_53_25_checked⟩

    · exact ⟨Witness.linear .positive case_54_53_26, case_54_53_26_checked⟩

    · exact ⟨Witness.linear .negative case_54_53_27, case_54_53_27_checked⟩

    · exact ⟨Witness.linear .negative case_54_53_28, case_54_53_28_checked⟩

    · exact ⟨Witness.linear .negative case_54_53_29, case_54_53_29_checked⟩

    · exact ⟨Witness.linear .negative case_54_53_30, case_54_53_30_checked⟩

    · exact ⟨Witness.linear .negative case_54_53_31, case_54_53_31_checked⟩

    · exact ⟨Witness.linear .negative case_54_53_32, case_54_53_32_checked⟩

    · exact ⟨Witness.linear .negative case_54_53_33, case_54_53_33_checked⟩

    · exact ⟨Witness.linear .negative case_54_53_34, case_54_53_34_checked⟩


#print axioms coverage_54
end ForestUnimodality.FiniteRows.FiniteData
