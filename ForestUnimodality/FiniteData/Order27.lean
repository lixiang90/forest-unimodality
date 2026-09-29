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

theorem case_27_14_1_checked :
    (Witness.rising).check 27 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_14_2_checked :
    (Witness.rising).check 27 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_14_3_checked :
    (Witness.rising).check 27 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_14_4_checked :
    (Witness.rising).check 27 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_14_5_checked :
    (Witness.rising).check 27 14 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_14_6_checked :
    (Witness.rising).check 27 14 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_14_7 : Certificate := {
  objectiveScale := 312814656000
  eta := 80518492454400
  rows := #[⟨.count 2, 17226312087600⟩, ⟨.count 3, 3208305315600⟩, ⟨.count 4, 875099000160⟩, ⟨.count 5, 354523276800⟩, ⟨.count 6, 312814656000⟩, ⟨.path 7, 41472931500⟩, ⟨.path 8, 83655576576⟩, ⟨.privateRow 7 0, 16321523625⟩, ⟨.privateRow 8 0, 11940023700⟩, ⟨.hall 5 3, 2976601100⟩, ⟨.hall 4 5, 679627080⟩, ⟨.hall 5 5, 253437800⟩, ⟨.hall 4 8, 20437224192⟩, ⟨.hall 3 9, 22607968320⟩]
  caps := #[0, 4539980016, 12049584624, 106993656, 77614416, 0, 334600728, 0, 75410676, 0, 0, 0, 0, 0] }

theorem case_27_14_7_checked :
    (Witness.linear .positive case_27_14_7).check 27 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_14_8 : Certificate := {
  objectiveScale := 924000000
  eta := 472949215200
  rows := #[⟨.count 2, 112058100000⟩, ⟨.count 3, 27313070400⟩, ⟨.count 4, 8145023040⟩, ⟨.count 5, 3127924800⟩, ⟨.count 6, 1772555400⟩, ⟨.count 7, 1708522200⟩, ⟨.path 8, 506510928⟩, ⟨.privateRow 6 3, 41071800⟩, ⟨.privateRow 7 1, 65518200⟩, ⟨.privateRow 8 0, 162716400⟩, ⟨.privateRow 9 0, 153938400⟩, ⟨.hall 6 3, 29074815⟩, ⟨.hall 5 5, 32124400⟩, ⟨.hall 6 6, 21049875⟩, ⟨.hall 4 7, 90150984⟩, ⟨.hall 5 8, 548055200⟩, ⟨.hall 3 9, 248300640⟩, ⟨.assumptionRow 8, 1772827056⟩]
  caps := #[0, 0, 0, 0, 776160, 347424, 338184, 0, 0, 369600, 0, 0, 0, 0] }

theorem case_27_14_8_checked :
    (Witness.linear .conditional case_27_14_8).check 27 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_15_1_checked :
    (Witness.rising).check 27 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_15_2_checked :
    (Witness.rising).check 27 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_15_3_checked :
    (Witness.rising).check 27 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_15_4_checked :
    (Witness.rising).check 27 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_15_5_checked :
    (Witness.rising).check 27 15 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_15_6_checked :
    (Witness.rising).check 27 15 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_15_7 : Certificate := {
  objectiveScale := 155013264000
  eta := 52752951405000
  rows := #[⟨.count 2, 9506188414800⟩, ⟨.count 3, 1790403199200⟩, ⟨.count 4, 454705574400⟩, ⟨.count 5, 182355881400⟩, ⟨.count 6, 155290073400⟩, ⟨.path 7, 27064699200⟩, ⟨.path 8, 36907151085⟩, ⟨.privateRow 5 5, 16814633220⟩, ⟨.privateRow 5 6, 5257533204⟩, ⟨.privateRow 6 3, 14451208200⟩, ⟨.privateRow 7 0, 3383226000⟩, ⟨.privateRow 8 0, 4618103490⟩, ⟨.hall 6 2, 808215100⟩, ⟨.hall 4 6, 191101008⟩, ⟨.hall 3 9, 2712732120⟩]
  caps := #[0, 19405552320, 0, 740509560, 916596450, 0, 0, 778741880, 0, 0, 0, 0, 0] }

theorem case_27_15_7_checked :
    (Witness.linear .positive case_27_15_7).check 27 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_15_8 : Certificate := {
  objectiveScale := 896000
  eta := 439084800
  rows := #[⟨.count 2, 101344320⟩, ⟨.count 3, 26877312⟩, ⟨.count 4, 7170240⟩, ⟨.count 5, 2430120⟩, ⟨.count 6, 1021680⟩, ⟨.count 7, 896280⟩, ⟨.path 8, 128016⟩, ⟨.path 9, 128000⟩, ⟨.privateRow 8 0, 924⟩, ⟨.privateRow 9 0, 18480⟩, ⟨.hall 9 1, 48048⟩, ⟨.hall 7 3, 2409⟩]
  caps := #[0, 266112, 46464, 4704, 0, 1944, 2336, 0, 11896, 0, 0, 0, 0] }

theorem case_27_15_8_checked :
    (Witness.linear .positive case_27_15_8).check 27 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_15_9 : Certificate := {
  objectiveScale := 145431000000
  eta := 65375015706000
  rows := #[⟨.count 2, 15956805664800⟩, ⟨.count 3, 4345792410960⟩, ⟨.count 4, 1343130909120⟩, ⟨.count 5, 457496839800⟩, ⟨.count 6, 171637666200⟩, ⟨.count 7, 69123354300⟩, ⟨.count 8, 84373248960⟩, ⟨.count 10, 145372827600⟩, ⟨.path 6, 87259372200⟩, ⟨.privateRow 4 8, 49455265860⟩, ⟨.privateRow 4 9, 280198999080⟩, ⟨.privateRow 5 6, 51507588132⟩, ⟨.privateRow 5 7, 145194674625⟩, ⟨.privateRow 5 8, 242145523620⟩, ⟨.privateRow 6 4, 33051618600⟩, ⟨.privateRow 6 5, 87773425740⟩, ⟨.privateRow 6 6, 122747399775⟩, ⟨.privateRow 7 2, 15648375600⟩, ⟨.privateRow 7 3, 60368408100⟩, ⟨.privateRow 7 4, 25185740580⟩, ⟨.privateRow 8 1, 36139603500⟩, ⟨.privateRow 9 0, 11686835160⟩, ⟨.hall 4 10, 148534233120⟩, ⟨.hall 3 11, 820501341660⟩, ⟨.hall 2 12, 1227446589600⟩, ⟨.assumptionRow 9, 84555360890⟩]
  caps := #[0, 16066260210, 3979798680, 2508712800, 14354340, 0, 177066890, 194231180, 719398680, 0, 58172400, 0, 0] }

theorem case_27_15_9_checked :
    (Witness.linear .conditional case_27_15_9).check 27 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_16_1_checked :
    (Witness.rising).check 27 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_16_2_checked :
    (Witness.rising).check 27 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_16_3_checked :
    (Witness.rising).check 27 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_16_4_checked :
    (Witness.rising).check 27 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_16_5_checked :
    (Witness.rising).check 27 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_16_6_checked :
    (Witness.rising).check 27 16 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_16_7 : Certificate := {
  objectiveScale := 2800000
  eta := 1401800400
  rows := #[⟨.count 2, 277116840⟩, ⟨.count 3, 58858800⟩, ⟨.count 4, 13993980⟩, ⟨.count 5, 4204200⟩, ⟨.count 6, 2788500⟩, ⟨.path 7, 1399944⟩, ⟨.privateRow 8 0, 50050⟩, ⟨.hall 8 5, 19305⟩, ⟨.hall 6 8, 28600⟩]
  caps := #[0, 0, 57288, 0, 5460, 0, 11500, 1344, 0, 0, 0, 0] }

theorem case_27_16_7_checked :
    (Witness.linear .positive case_27_16_7).check 27 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_16_8 : Certificate := {
  objectiveScale := 15000
  eta := 8275410
  rows := #[⟨.count 2, 1979406⟩, ⟨.count 3, 539682⟩, ⟨.count 4, 150150⟩, ⟨.count 5, 47190⟩, ⟨.count 6, 19305⟩, ⟨.count 7, 15015⟩, ⟨.path 8, 4286⟩]
  caps := #[0, 0, 858, 354, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_27_16_8_checked :
    (Witness.linear .positive case_27_16_8).check 27 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_16_9 : Certificate := {
  objectiveScale := 21798000000
  eta := 12507779592000
  rows := #[⟨.count 2, 3059874195840⟩, ⟨.count 3, 784707073920⟩, ⟨.count 4, 242501878080⟩, ⟨.count 5, 81716342400⟩, ⟨.count 6, 29924294400⟩, ⟨.count 7, 15307427520⟩, ⟨.count 10, 24169622400⟩, ⟨.path 6, 13661524800⟩, ⟨.privateRow 2 14, 265865846400⟩, ⟨.privateRow 3 11, 69286250880⟩, ⟨.privateRow 3 12, 143003599200⟩, ⟨.privateRow 4 9, 61632537120⟩, ⟨.privateRow 4 10, 78719117400⟩, ⟨.privateRow 4 11, 86557460220⟩, ⟨.privateRow 5 6, 4690057680⟩, ⟨.privateRow 5 7, 34044639552⟩, ⟨.privateRow 5 8, 48209764680⟩, ⟨.privateRow 5 9, 23862706560⟩, ⟨.privateRow 6 4, 4761306000⟩, ⟨.privateRow 6 5, 19925551800⟩, ⟨.privateRow 6 6, 23085825840⟩, ⟨.privateRow 7 2, 3006816120⟩, ⟨.privateRow 7 3, 14460668640⟩, ⟨.privateRow 7 4, 661787280⟩, ⟨.privateRow 8 0, 1253239680⟩, ⟨.privateRow 8 1, 4972396275⟩, ⟨.privateRow 9 0, 1779152760⟩, ⟨.hall 2 13, 109971781920⟩, ⟨.assumptionRow 9, 16274483680⟩]
  caps := #[0, 5297846400, 930726720, 221390400, 25821180, 0, 214546200, 0, 22930285, 647739680, 0, 0] }

theorem case_27_16_9_checked :
    (Witness.linear .conditional case_27_16_9).check 27 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_16_10 : Certificate := {
  objectiveScale := 340409193600000
  eta := 206786330381030400
  rows := #[⟨.count 2, 52791849175665600⟩, ⟨.count 3, 13712737586708160⟩, ⟨.count 4, 3745811704995360⟩, ⟨.count 5, 1079619914973600⟩, ⟨.count 6, 265993312384800⟩, ⟨.path 5, 11850020582400⟩, ⟨.path 6, 267603200504640⟩, ⟨.privateRow 2 14, 6856368793354080⟩, ⟨.privateRow 3 11, 1262396147492480⟩, ⟨.privateRow 3 12, 3027803613394560⟩, ⟨.privateRow 4 9, 983001755916180⟩, ⟨.privateRow 4 10, 1642291389178440⟩, ⟨.privateRow 4 11, 2144897053299000⟩, ⟨.privateRow 5 6, 12169628671200⟩, ⟨.privateRow 5 7, 539914268589696⟩, ⟨.privateRow 5 8, 923414038386840⟩, ⟨.privateRow 5 9, 1234348050936000⟩, ⟨.privateRow 6 4, 16143384972000⟩, ⟨.privateRow 6 5, 264254794003200⟩, ⟨.privateRow 6 6, 553544252701440⟩, ⟨.privateRow 6 7, 472007740604400⟩, ⟨.privateRow 7 2, 6519443931000⟩, ⟨.privateRow 7 3, 130686910342560⟩, ⟨.privateRow 7 4, 347529824481840⟩, ⟨.privateRow 7 5, 81779904670464⟩, ⟨.privateRow 8 0, 3245234312320⟩, ⟨.privateRow 8 1, 39018871927035⟩, ⟨.privateRow 8 2, 184109096611440⟩, ⟨.privateRow 9 0, 80319549229920⟩, ⟨.privateRow 10 0, 28163997781920⟩, ⟨.hall 3 12, 503260951818240⟩, ⟨.hall 2 13, 2832046443626400⟩]
  caps := #[0, 67544838641280, 27776689691520, 5195450198400, 12037766132700, 2642907627360, 8050742683440, 0, 2764938215725, 19573528632000, 0, 340409193600000] }

theorem case_27_16_10_checked :
    (Witness.linear .negative case_27_16_10).check 27 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_17_1_checked :
    (Witness.rising).check 27 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_17_2_checked :
    (Witness.rising).check 27 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_17_3_checked :
    (Witness.rising).check 27 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_17_4_checked :
    (Witness.rising).check 27 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_17_5_checked :
    (Witness.rising).check 27 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_17_6_checked :
    (Witness.rising).check 27 17 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_27_17_7_checked :
    (Witness.linear .positive case_27_17_7).check 27 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_17_8 : Certificate := {
  objectiveScale := 9
  eta := 1419
  rows := #[⟨.assumptionRow 8, 22⟩]
  caps := #[0, 0, 492, 182, 74, 35, 22, 117, 50, 9, 0] }

theorem case_27_17_8_checked :
    (Witness.linear .conditional case_27_17_8).check 27 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_17_9 : Certificate := {
  objectiveScale := 1757921407200000
  eta := 1979639244683100000
  rows := #[⟨.count 2, 423026910597170880⟩, ⟨.count 3, 105844711615723080⟩, ⟨.count 4, 27224753041165680⟩, ⟨.count 5, 8358476810884200⟩, ⟨.count 6, 2714933821279680⟩, ⟨.count 7, 1055807597164320⟩, ⟨.path 5, 744536401408800⟩, ⟨.path 6, 1158322906540800⟩, ⟨.privateRow 2 15, 37129233833611920⟩, ⟨.privateRow 3 12, 17024897504274660⟩, ⟨.privateRow 3 13, 18014717126616210⟩, ⟨.privateRow 4 9, 3634994727380016⟩, ⟨.privateRow 4 10, 10294124072352120⟩, ⟨.privateRow 4 11, 10388392607813220⟩, ⟨.privateRow 4 12, 1244344668086520⟩, ⟨.privateRow 5 6, 41298596487720⟩, ⟨.privateRow 5 7, 3795879694566960⟩, ⟨.privateRow 5 8, 5806941784403760⟩, ⟨.privateRow 5 9, 2388136231681200⟩, ⟨.privateRow 6 4, 216817631560530⟩, ⟨.privateRow 6 5, 2860376704562520⟩, ⟨.privateRow 6 6, 1879086140191260⟩, ⟨.privateRow 7 2, 207390778014420⟩, ⟨.privateRow 7 3, 1588424822519535⟩, ⟨.privateRow 8 0, 52790379858216⟩, ⟨.privateRow 8 1, 523015800447140⟩, ⟨.privateRow 9 0, 175967932860720⟩, ⟨.privateRow 10 0, 197963924468310⟩, ⟨.hall 2 14, 6499082320322592⟩, ⟨.assumptionRow 9, 1576196281730700⟩]
  caps := #[0, 1346270982736680, 162274727815200, 220406173791804, 15422628408840, 0, 19585366991820, 84050617281750, 172005773333492, 0, 174210011453520] }

theorem case_27_17_9_checked :
    (Witness.linear .conditional case_27_17_9).check 27 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_17_10 : Certificate := {
  objectiveScale := 141120000
  eta := 167999832000
  rows := #[⟨.count 2, 24256552320⟩, ⟨.count 3, 2875672800⟩, ⟨.count 9, 2815132320⟩, ⟨.count 10, 908107200⟩, ⟨.path 3, 2874551680⟩, ⟨.privateRow 2 12, 479278800⟩, ⟨.privateRow 2 13, 4338734400⟩, ⟨.privateRow 2 14, 6407200800⟩, ⟨.privateRow 2 15, 6407200800⟩, ⟨.privateRow 3 9, 176996820⟩, ⟨.privateRow 3 10, 1388899512⟩, ⟨.privateRow 3 11, 1587295710⟩, ⟨.privateRow 3 12, 3129606480⟩, ⟨.privateRow 3 13, 2266484220⟩, ⟨.privateRow 4 6, 70675605⟩, ⟨.privateRow 4 7, 299150280⟩, ⟨.privateRow 4 8, 480720240⟩, ⟨.privateRow 4 9, 1018161144⟩, ⟨.privateRow 4 10, 1293782490⟩, ⟨.privateRow 4 11, 908827920⟩, ⟨.privateRow 5 3, 23567544⟩, ⟨.privateRow 5 4, 61661600⟩, ⟨.privateRow 5 5, 123243120⟩, ⟨.privateRow 5 6, 334414080⟩, ⟨.privateRow 5 7, 550990440⟩, ⟨.privateRow 5 8, 579603024⟩, ⟨.privateRow 6 1, 40622400⟩, ⟨.privateRow 6 2, 27531504⟩, ⟨.privateRow 6 3, 98578480⟩, ⟨.privateRow 6 4, 228828600⟩, ⟨.privateRow 6 5, 259562160⟩, ⟨.privateRow 7 0, 98771400⟩, ⟨.privateRow 7 1, 132324192⟩, ⟨.privateRow 8 0, 92828736⟩, ⟨.hall 2 14, 492395904⟩]
  caps := #[0, 16816800, 7181440, 812812, 567441, 45136, 774920, 4144392, 0, 7267680, 0] }

theorem case_27_17_10_checked :
    (Witness.linear .negative case_27_17_10).check 27 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_18_1_checked :
    (Witness.rising).check 27 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_18_2_checked :
    (Witness.rising).check 27 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_18_3_checked :
    (Witness.rising).check 27 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_18_4_checked :
    (Witness.rising).check 27 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_18_5_checked :
    (Witness.rising).check 27 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_18_6_checked :
    (Witness.rising).check 27 18 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_27_18_7_checked :
    (Witness.linear .positive case_27_18_7).check 27 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_18_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_27_18_8_checked :
    (Witness.linear .positive case_27_18_8).check 27 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_18_9 : Certificate := {
  objectiveScale := 13
  eta := 3256
  rows := #[⟨.assumptionRow 9, 23⟩]
  caps := #[0, 0, 1095, 384, 142, 63, 33, 418, 248, 81] }

theorem case_27_18_9_checked :
    (Witness.linear .conditional case_27_18_9).check 27 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_18_10 : Certificate := {
  objectiveScale := 86368800000
  eta := 518056662483360
  rows := #[⟨.count 2, 70754910145920⟩, ⟨.count 3, 9087055777800⟩, ⟨.count 4, 870727057200⟩, ⟨.count 5, 33346993680⟩, ⟨.path 3, 2697960545280⟩, ⟨.path 4, 790807691520⟩, ⟨.privateRow 2 16, 4156332240060⟩, ⟨.privateRow 3 12, 1292659157790⟩, ⟨.privateRow 3 13, 2146558333920⟩, ⟨.privateRow 3 14, 1922083663500⟩, ⟨.privateRow 4 9, 324978804150⟩, ⟨.privateRow 4 10, 1035424153764⟩, ⟨.privateRow 4 11, 1196554974615⟩, ⟨.privateRow 4 12, 362185403580⟩, ⟨.privateRow 5 6, 26121811716⟩, ⟨.privateRow 5 7, 317061098640⟩, ⟨.privateRow 5 8, 656071223808⟩, ⟨.privateRow 5 9, 317166962112⟩, ⟨.privateRow 6 4, 22643020400⟩, ⟨.privateRow 6 5, 285765209730⟩, ⟨.privateRow 6 6, 237134177280⟩, ⟨.privateRow 7 2, 19081890828⟩, ⟨.privateRow 7 3, 190613062640⟩, ⟨.privateRow 8 0, 38315358900⟩, ⟨.privateRow 8 1, 33717515832⟩, ⟨.privateRow 9 0, 25936550640⟩, ⟨.assumptionRow 10, 33446934720⟩]
  caps := #[0, 0, 0, 1723394040, 3587064327, 156779936, 1259390770, 2791809768, 1460064564, 0] }

theorem case_27_18_10_checked :
    (Witness.linear .conditional case_27_18_10).check 27 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_18_11 : Certificate := {
  objectiveScale := 43
  eta := 604
  rows := #[⟨.assumptionRow 11, 19⟩]
  caps := #[0, 0, 278, 169, 79, 52, 33, 2541, 2445, 1551] }

theorem case_27_18_11_checked :
    (Witness.linear .conditional case_27_18_11).check 27 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_19_1_checked :
    (Witness.rising).check 27 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_19_2_checked :
    (Witness.rising).check 27 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_19_3_checked :
    (Witness.rising).check 27 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_19_4_checked :
    (Witness.rising).check 27 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_19_5_checked :
    (Witness.rising).check 27 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_19_6_checked :
    (Witness.rising).check 27 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_19_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0] }

theorem case_27_19_7_checked :
    (Witness.linear .positive case_27_19_7).check 27 19 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_27_19_8_checked :
    (Witness.linear .positive case_27_19_8).check 27 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_19_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_27_19_9_checked :
    (Witness.linear .positive case_27_19_9).check 27 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_19_10 : Certificate := {
  objectiveScale := 758
  eta := 106678
  rows := #[⟨.assumptionRow 10, 755⟩]
  caps := #[0, 0, 41195, 15774, 6022, 3005, 109681, 92180, 50160] }

theorem case_27_19_10_checked :
    (Witness.linear .conditional case_27_19_10).check 27 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_19_11 : Certificate := {
  objectiveScale := 379
  eta := 4482
  rows := #[⟨.assumptionRow 11, 162⟩]
  caps := #[0, 0, 2259, 1342, 593, 431, 69927, 68013, 44715] }

theorem case_27_19_11_checked :
    (Witness.linear .conditional case_27_19_11).check 27 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_19_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 132, 132] }

theorem case_27_19_12_checked :
    (Witness.linear .negative case_27_19_12).check 27 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_20_1_checked :
    (Witness.rising).check 27 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_20_2_checked :
    (Witness.rising).check 27 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_20_3_checked :
    (Witness.rising).check 27 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_20_4_checked :
    (Witness.rising).check 27 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_20_5_checked :
    (Witness.rising).check 27 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_20_6_checked :
    (Witness.rising).check 27 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_20_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_27_20_7_checked :
    (Witness.linear .positive case_27_20_7).check 27 20 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_27_20_8_checked :
    (Witness.linear .positive case_27_20_8).check 27 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_27_20_9_checked :
    (Witness.linear .positive case_27_20_9).check 27 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_20_10 : Certificate := {
  objectiveScale := 214
  eta := 121121
  rows := #[⟨.assumptionRow 10, 335⟩]
  caps := #[0, 0, 40645, 14100, 5100, 1945, 819, 22126] }

theorem case_27_20_10_checked :
    (Witness.linear .conditional case_27_20_10).check 27 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_20_11 : Certificate := {
  objectiveScale := 504
  eta := 49179
  rows := #[⟨.assumptionRow 11, 359⟩]
  caps := #[0, 0, 21109, 9285, 3652, 2002, 145145, 134277] }

theorem case_27_20_11_checked :
    (Witness.linear .conditional case_27_20_11).check 27 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_20_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 429, 429] }

theorem case_27_20_12_checked :
    (Witness.linear .negative case_27_20_12).check 27 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_21_1_checked :
    (Witness.rising).check 27 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_21_2_checked :
    (Witness.rising).check 27 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_21_3_checked :
    (Witness.rising).check 27 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_21_4_checked :
    (Witness.rising).check 27 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_21_5_checked :
    (Witness.rising).check 27 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_21_6_checked :
    (Witness.rising).check 27 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_21_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_27_21_7_checked :
    (Witness.linear .positive case_27_21_7).check 27 21 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_27_21_8_checked :
    (Witness.linear .positive case_27_21_8).check 27 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_27_21_9_checked :
    (Witness.linear .positive case_27_21_9).check 27 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_21_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_27_21_10_checked :
    (Witness.linear .positive case_27_21_10).check 27 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_21_11 : Certificate := {
  objectiveScale := 998
  eta := 304213
  rows := #[⟨.assumptionRow 11, 939⟩]
  caps := #[0, 0, 108966, 45155, 18126, 7176, 459914] }

theorem case_27_21_11_checked :
    (Witness.linear .conditional case_27_21_11).check 27 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_21_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 1430, 1430] }

theorem case_27_21_12_checked :
    (Witness.linear .negative case_27_21_12).check 27 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_21_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_27_21_13_checked :
    (Witness.linear .negative case_27_21_13).check 27 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_22_1_checked :
    (Witness.rising).check 27 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_22_2_checked :
    (Witness.rising).check 27 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_22_3_checked :
    (Witness.rising).check 27 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_22_4_checked :
    (Witness.rising).check 27 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_22_5_checked :
    (Witness.rising).check 27 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_22_6_checked :
    (Witness.rising).check 27 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_22_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_27_22_7_checked :
    (Witness.linear .positive case_27_22_7).check 27 22 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_27_22_8_checked :
    (Witness.linear .positive case_27_22_8).check 27 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_27_22_9_checked :
    (Witness.linear .positive case_27_22_9).check 27 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_27_22_10_checked :
    (Witness.linear .positive case_27_22_10).check 27 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_22_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_27_22_11_checked :
    (Witness.linear .positive case_27_22_11).check 27 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_22_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 4862, 4862] }

theorem case_27_22_12_checked :
    (Witness.linear .negative case_27_22_12).check 27 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_22_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_27_22_13_checked :
    (Witness.linear .negative case_27_22_13).check 27 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_22_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_27_22_14_checked :
    (Witness.linear .negative case_27_22_14).check 27 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_23_1_checked :
    (Witness.rising).check 27 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_23_2_checked :
    (Witness.rising).check 27 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_23_3_checked :
    (Witness.rising).check 27 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_23_4_checked :
    (Witness.rising).check 27 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_23_5_checked :
    (Witness.rising).check 27 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_23_6_checked :
    (Witness.rising).check 27 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_23_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_27_23_7_checked :
    (Witness.linear .positive case_27_23_7).check 27 23 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_27_23_8_checked :
    (Witness.linear .positive case_27_23_8).check 27 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_27_23_9_checked :
    (Witness.linear .positive case_27_23_9).check 27 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_27_23_10_checked :
    (Witness.linear .positive case_27_23_10).check 27 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_23_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_27_23_11_checked :
    (Witness.linear .positive case_27_23_11).check 27 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_23_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 16796, 16796] }

theorem case_27_23_12_checked :
    (Witness.linear .negative case_27_23_12).check 27 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_23_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_27_23_13_checked :
    (Witness.linear .negative case_27_23_13).check 27 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_23_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_27_23_14_checked :
    (Witness.linear .negative case_27_23_14).check 27 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_24_1_checked :
    (Witness.rising).check 27 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_24_2_checked :
    (Witness.rising).check 27 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_24_3_checked :
    (Witness.rising).check 27 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_24_4_checked :
    (Witness.rising).check 27 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_24_5_checked :
    (Witness.rising).check 27 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_24_6_checked :
    (Witness.rising).check 27 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_24_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_27_24_7_checked :
    (Witness.linear .positive case_27_24_7).check 27 24 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_27_24_8_checked :
    (Witness.linear .positive case_27_24_8).check 27 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_27_24_9_checked :
    (Witness.linear .positive case_27_24_9).check 27 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_27_24_10_checked :
    (Witness.linear .positive case_27_24_10).check 27 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_27_24_11_checked :
    (Witness.linear .positive case_27_24_11).check 27 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_24_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_27_24_12_checked :
    (Witness.linear .positive case_27_24_12).check 27 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_24_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_27_24_13_checked :
    (Witness.linear .negative case_27_24_13).check 27 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_24_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_27_24_14_checked :
    (Witness.linear .negative case_27_24_14).check 27 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_24_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_27_24_15_checked :
    (Witness.linear .negative case_27_24_15).check 27 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_25_1_checked :
    (Witness.rising).check 27 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_25_2_checked :
    (Witness.rising).check 27 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_25_3_checked :
    (Witness.rising).check 27 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_25_4_checked :
    (Witness.rising).check 27 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_25_5_checked :
    (Witness.rising).check 27 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_25_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_27_25_6_checked :
    (Witness.linear .positive case_27_25_6).check 27 25 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_25_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_27_25_7_checked :
    (Witness.linear .positive case_27_25_7).check 27 25 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_27_25_8_checked :
    (Witness.linear .positive case_27_25_8).check 27 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_27_25_9_checked :
    (Witness.linear .positive case_27_25_9).check 27 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_27_25_10_checked :
    (Witness.linear .positive case_27_25_10).check 27 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_27_25_11_checked :
    (Witness.linear .positive case_27_25_11).check 27 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_25_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_27_25_12_checked :
    (Witness.linear .positive case_27_25_12).check 27 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_25_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_27_25_13_checked :
    (Witness.linear .negative case_27_25_13).check 27 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_25_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_27_25_14_checked :
    (Witness.linear .negative case_27_25_14).check 27 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_25_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_27_25_15_checked :
    (Witness.linear .negative case_27_25_15).check 27 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_27_25_16_checked :
    (Witness.linear .negative case_27_25_16).check 27 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_26_1_checked :
    (Witness.rising).check 27 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_26_2_checked :
    (Witness.rising).check 27 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_26_3_checked :
    (Witness.rising).check 27 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_26_4_checked :
    (Witness.rising).check 27 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_27_26_5_checked :
    (Witness.rising).check 27 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_26_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_27_26_6_checked :
    (Witness.linear .positive case_27_26_6).check 27 26 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_26_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_27_26_7_checked :
    (Witness.linear .positive case_27_26_7).check 27 26 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_27_26_8_checked :
    (Witness.linear .positive case_27_26_8).check 27 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_27_26_9_checked :
    (Witness.linear .positive case_27_26_9).check 27 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_27_26_10_checked :
    (Witness.linear .positive case_27_26_10).check 27 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_27_26_11_checked :
    (Witness.linear .positive case_27_26_11).check 27 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_27_26_12_checked :
    (Witness.linear .positive case_27_26_12).check 27 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_26_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_27_26_13_checked :
    (Witness.linear .positive case_27_26_13).check 27 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_26_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_27_26_14_checked :
    (Witness.linear .negative case_27_26_14).check 27 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_26_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_27_26_15_checked :
    (Witness.linear .negative case_27_26_15).check 27 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_27_26_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_27_26_16_checked :
    (Witness.linear .negative case_27_26_16).check 27 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_27 (a k : ℕ) (h : Domain 27 a k) :
    ∃ w : Witness, w.check 27 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 14 ≤ a := by omega
  have haHi : a ≤ 26 := by omega
  interval_cases a

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_14_1_checked⟩

    · exact ⟨Witness.rising, case_27_14_2_checked⟩

    · exact ⟨Witness.rising, case_27_14_3_checked⟩

    · exact ⟨Witness.rising, case_27_14_4_checked⟩

    · exact ⟨Witness.rising, case_27_14_5_checked⟩

    · exact ⟨Witness.rising, case_27_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_14_7, case_27_14_7_checked⟩

    · exact ⟨Witness.linear .conditional case_27_14_8, case_27_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_15_1_checked⟩

    · exact ⟨Witness.rising, case_27_15_2_checked⟩

    · exact ⟨Witness.rising, case_27_15_3_checked⟩

    · exact ⟨Witness.rising, case_27_15_4_checked⟩

    · exact ⟨Witness.rising, case_27_15_5_checked⟩

    · exact ⟨Witness.rising, case_27_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_15_7, case_27_15_7_checked⟩

    · exact ⟨Witness.linear .positive case_27_15_8, case_27_15_8_checked⟩

    · exact ⟨Witness.linear .conditional case_27_15_9, case_27_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_16_1_checked⟩

    · exact ⟨Witness.rising, case_27_16_2_checked⟩

    · exact ⟨Witness.rising, case_27_16_3_checked⟩

    · exact ⟨Witness.rising, case_27_16_4_checked⟩

    · exact ⟨Witness.rising, case_27_16_5_checked⟩

    · exact ⟨Witness.rising, case_27_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_16_7, case_27_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_27_16_8, case_27_16_8_checked⟩

    · exact ⟨Witness.linear .conditional case_27_16_9, case_27_16_9_checked⟩

    · exact ⟨Witness.linear .negative case_27_16_10, case_27_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_17_1_checked⟩

    · exact ⟨Witness.rising, case_27_17_2_checked⟩

    · exact ⟨Witness.rising, case_27_17_3_checked⟩

    · exact ⟨Witness.rising, case_27_17_4_checked⟩

    · exact ⟨Witness.rising, case_27_17_5_checked⟩

    · exact ⟨Witness.rising, case_27_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_17_7, case_27_17_7_checked⟩

    · exact ⟨Witness.linear .conditional case_27_17_8, case_27_17_8_checked⟩

    · exact ⟨Witness.linear .conditional case_27_17_9, case_27_17_9_checked⟩

    · exact ⟨Witness.linear .negative case_27_17_10, case_27_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_18_1_checked⟩

    · exact ⟨Witness.rising, case_27_18_2_checked⟩

    · exact ⟨Witness.rising, case_27_18_3_checked⟩

    · exact ⟨Witness.rising, case_27_18_4_checked⟩

    · exact ⟨Witness.rising, case_27_18_5_checked⟩

    · exact ⟨Witness.rising, case_27_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_18_7, case_27_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_27_18_8, case_27_18_8_checked⟩

    · exact ⟨Witness.linear .conditional case_27_18_9, case_27_18_9_checked⟩

    · exact ⟨Witness.linear .conditional case_27_18_10, case_27_18_10_checked⟩

    · exact ⟨Witness.linear .conditional case_27_18_11, case_27_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_19_1_checked⟩

    · exact ⟨Witness.rising, case_27_19_2_checked⟩

    · exact ⟨Witness.rising, case_27_19_3_checked⟩

    · exact ⟨Witness.rising, case_27_19_4_checked⟩

    · exact ⟨Witness.rising, case_27_19_5_checked⟩

    · exact ⟨Witness.rising, case_27_19_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_19_7, case_27_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_27_19_8, case_27_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_27_19_9, case_27_19_9_checked⟩

    · exact ⟨Witness.linear .conditional case_27_19_10, case_27_19_10_checked⟩

    · exact ⟨Witness.linear .conditional case_27_19_11, case_27_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_27_19_12, case_27_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_20_1_checked⟩

    · exact ⟨Witness.rising, case_27_20_2_checked⟩

    · exact ⟨Witness.rising, case_27_20_3_checked⟩

    · exact ⟨Witness.rising, case_27_20_4_checked⟩

    · exact ⟨Witness.rising, case_27_20_5_checked⟩

    · exact ⟨Witness.rising, case_27_20_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_20_7, case_27_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_27_20_8, case_27_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_27_20_9, case_27_20_9_checked⟩

    · exact ⟨Witness.linear .conditional case_27_20_10, case_27_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_27_20_11, case_27_20_11_checked⟩

    · exact ⟨Witness.linear .negative case_27_20_12, case_27_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_21_1_checked⟩

    · exact ⟨Witness.rising, case_27_21_2_checked⟩

    · exact ⟨Witness.rising, case_27_21_3_checked⟩

    · exact ⟨Witness.rising, case_27_21_4_checked⟩

    · exact ⟨Witness.rising, case_27_21_5_checked⟩

    · exact ⟨Witness.rising, case_27_21_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_21_7, case_27_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_27_21_8, case_27_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_27_21_9, case_27_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_27_21_10, case_27_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_27_21_11, case_27_21_11_checked⟩

    · exact ⟨Witness.linear .negative case_27_21_12, case_27_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_27_21_13, case_27_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_22_1_checked⟩

    · exact ⟨Witness.rising, case_27_22_2_checked⟩

    · exact ⟨Witness.rising, case_27_22_3_checked⟩

    · exact ⟨Witness.rising, case_27_22_4_checked⟩

    · exact ⟨Witness.rising, case_27_22_5_checked⟩

    · exact ⟨Witness.rising, case_27_22_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_22_7, case_27_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_27_22_8, case_27_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_27_22_9, case_27_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_27_22_10, case_27_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_27_22_11, case_27_22_11_checked⟩

    · exact ⟨Witness.linear .negative case_27_22_12, case_27_22_12_checked⟩

    · exact ⟨Witness.linear .negative case_27_22_13, case_27_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_27_22_14, case_27_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_23_1_checked⟩

    · exact ⟨Witness.rising, case_27_23_2_checked⟩

    · exact ⟨Witness.rising, case_27_23_3_checked⟩

    · exact ⟨Witness.rising, case_27_23_4_checked⟩

    · exact ⟨Witness.rising, case_27_23_5_checked⟩

    · exact ⟨Witness.rising, case_27_23_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_23_7, case_27_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_27_23_8, case_27_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_27_23_9, case_27_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_27_23_10, case_27_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_27_23_11, case_27_23_11_checked⟩

    · exact ⟨Witness.linear .negative case_27_23_12, case_27_23_12_checked⟩

    · exact ⟨Witness.linear .negative case_27_23_13, case_27_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_27_23_14, case_27_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_24_1_checked⟩

    · exact ⟨Witness.rising, case_27_24_2_checked⟩

    · exact ⟨Witness.rising, case_27_24_3_checked⟩

    · exact ⟨Witness.rising, case_27_24_4_checked⟩

    · exact ⟨Witness.rising, case_27_24_5_checked⟩

    · exact ⟨Witness.rising, case_27_24_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_24_7, case_27_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_27_24_8, case_27_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_27_24_9, case_27_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_27_24_10, case_27_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_27_24_11, case_27_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_27_24_12, case_27_24_12_checked⟩

    · exact ⟨Witness.linear .negative case_27_24_13, case_27_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_27_24_14, case_27_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_27_24_15, case_27_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_25_1_checked⟩

    · exact ⟨Witness.rising, case_27_25_2_checked⟩

    · exact ⟨Witness.rising, case_27_25_3_checked⟩

    · exact ⟨Witness.rising, case_27_25_4_checked⟩

    · exact ⟨Witness.rising, case_27_25_5_checked⟩

    · exact ⟨Witness.linear .positive case_27_25_6, case_27_25_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_25_7, case_27_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_27_25_8, case_27_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_27_25_9, case_27_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_27_25_10, case_27_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_27_25_11, case_27_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_27_25_12, case_27_25_12_checked⟩

    · exact ⟨Witness.linear .negative case_27_25_13, case_27_25_13_checked⟩

    · exact ⟨Witness.linear .negative case_27_25_14, case_27_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_27_25_15, case_27_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_27_25_16, case_27_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_27_26_1_checked⟩

    · exact ⟨Witness.rising, case_27_26_2_checked⟩

    · exact ⟨Witness.rising, case_27_26_3_checked⟩

    · exact ⟨Witness.rising, case_27_26_4_checked⟩

    · exact ⟨Witness.rising, case_27_26_5_checked⟩

    · exact ⟨Witness.linear .positive case_27_26_6, case_27_26_6_checked⟩

    · exact ⟨Witness.linear .positive case_27_26_7, case_27_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_27_26_8, case_27_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_27_26_9, case_27_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_27_26_10, case_27_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_27_26_11, case_27_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_27_26_12, case_27_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_27_26_13, case_27_26_13_checked⟩

    · exact ⟨Witness.linear .negative case_27_26_14, case_27_26_14_checked⟩

    · exact ⟨Witness.linear .negative case_27_26_15, case_27_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_27_26_16, case_27_26_16_checked⟩


#print axioms coverage_27
end ForestUnimodality.FiniteRows.FiniteData
