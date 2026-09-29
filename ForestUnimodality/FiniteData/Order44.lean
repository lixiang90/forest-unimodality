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

theorem case_44_22_1_checked :
    (Witness.rising).check 44 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_22_2_checked :
    (Witness.rising).check 44 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_22_3_checked :
    (Witness.rising).check 44 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_22_4_checked :
    (Witness.rising).check 44 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_22_5_checked :
    (Witness.rising).check 44 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_22_6_checked :
    (Witness.rising).check 44 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_22_7_checked :
    (Witness.rising).check 44 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_22_8_checked :
    (Witness.rising).check 44 22 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_22_9_checked :
    (Witness.rising).check 44 22 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_22_10 : Certificate := {
  objectiveScale := 268125000
  eta := 0
  rows := #[⟨.count 2, 325909584000⟩, ⟨.count 3, 460929268800⟩, ⟨.count 4, 73145872800⟩, ⟨.count 5, 13579566000⟩, ⟨.count 6, 2954952000⟩, ⟨.count 7, 804053250⟩, ⟨.count 8, 319519200⟩, ⟨.count 9, 270270000⟩, ⟨.count 11, 34303500⟩, ⟨.path 10, 52457328⟩, ⟨.path 11, 53616750⟩, ⟨.privateRow 9 2, 100100⟩, ⟨.privateRow 11 0, 1645875⟩, ⟨.privateRow 12 0, 1480500⟩, ⟨.hall 9 1, 4608450⟩, ⟨.hall 8 3, 867300⟩, ⟨.hall 9 3, 49140⟩, ⟨.hall 12 3, 212850⟩, ⟨.hall 0 4, 4492488000⟩, ⟨.hall 1 4, 237837600⟩, ⟨.hall 7 4, 70350⟩, ⟨.hall 7 5, 389550⟩, ⟨.hall 0 6, 135135000⟩, ⟨.hall 6 7, 88550⟩, ⟨.hall 6 8, 248500⟩, ⟨.hall 5 12, 2158200⟩, ⟨.hall 4 16, 239038800⟩]
  caps := #[0, 59323304040, 0, 0, 3044184, 34158036, 12972960, 0, 12060048, 0, 3617328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_22_10_checked :
    (Witness.linear .positive case_44_22_10).check 44 22 10 = true := by
  change case_44_22_10.check 44 22 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_22_11 : Certificate := {
  objectiveScale := 396000000
  eta := 342205063200
  rows := #[⟨.count 2, 651819168000⟩, ⟨.count 3, 1119499421040⟩, ⟨.count 4, 208925196480⟩, ⟨.count 5, 43168725600⟩, ⟨.count 6, 10190980800⟩, ⟨.count 7, 2736934200⟩, ⟨.count 8, 941740800⟩, ⟨.count 9, 393513120⟩, ⟨.count 10, 395841600⟩, ⟨.path 11, 1524600⟩, ⟨.path 12, 118893600⟩, ⟨.privateRow 10 2, 14288400⟩, ⟨.privateRow 12 0, 10848600⟩, ⟨.privateRow 13 0, 11875248⟩, ⟨.hall 10 1, 15082200⟩, ⟨.hall 10 2, 652680⟩, ⟨.hall 9 3, 1857492⟩, ⟨.hall 1 4, 228708480⟩, ⟨.hall 8 4, 1982736⟩, ⟨.hall 0 5, 3464260800⟩, ⟨.hall 1 5, 87237150⟩, ⟨.hall 8 5, 223440⟩, ⟨.hall 7 6, 994700⟩, ⟨.hall 13 6, 5585580⟩, ⟨.hall 7 7, 382445⟩, ⟨.hall 6 9, 761040⟩, ⟨.hall 6 10, 1610700⟩, ⟨.hall 5 13, 23183160⟩, ⟨.hall 4 16, 682762080⟩]
  caps := #[0, 30686292000, 21283891200, 2061876960, 105019200, 163363200, 0, 0, 0, 4011480, 5439600, 6217200, 0, 6286896, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_22_11_checked :
    (Witness.linear .positive case_44_22_11).check 44 22 11 = true := by
  change case_44_22_11.check 44 22 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_22_12 : Certificate := {
  objectiveScale := 38500000
  eta := 0
  rows := #[⟨.count 2, 9311702400⟩, ⟨.count 3, 178086308400⟩, ⟨.count 4, 41314553280⟩, ⟨.count 5, 9801792000⟩, ⟨.count 6, 2407204800⟩, ⟨.count 7, 706305600⟩, ⟨.count 8, 225345120⟩, ⟨.count 9, 82162080⟩, ⟨.count 10, 38253600⟩, ⟨.count 11, 38115000⟩, ⟨.path 13, 4469220⟩, ⟨.path 14, 5654600⟩, ⟨.privateRow 8 8, 2522520⟩, ⟨.privateRow 9 6, 6366360⟩, ⟨.privateRow 9 7, 3672240⟩, ⟨.privateRow 10 4, 2975280⟩, ⟨.privateRow 13 0, 449064⟩, ⟨.privateRow 14 0, 640640⟩, ⟨.privateRow 15 4, 1996995⟩, ⟨.privateRow 16 3, 1126125⟩, ⟨.privateRow 16 4, 3003000⟩, ⟨.hall 2 1, 85765680⟩, ⟨.hall 11 1, 1663200⟩, ⟨.hall 12 1, 462000⟩, ⟨.hall 10 3, 462000⟩, ⟨.hall 11 3, 101640⟩, ⟨.hall 2 4, 540540⟩, ⟨.hall 10 4, 64680⟩, ⟨.hall 0 5, 446846400⟩, ⟨.hall 1 5, 29279250⟩, ⟨.hall 9 5, 327600⟩, ⟨.hall 0 6, 53153100⟩, ⟨.hall 8 7, 355740⟩, ⟨.hall 7 9, 666330⟩, ⟨.hall 6 12, 4791600⟩, ⟨.hall 5 15, 169068900⟩, ⟨.hall 4 17, 2009367360⟩, ⟨.hall 2 19, 1163962800⟩]
  caps := #[0, 19970508600, 1168106940, 845342680, 122522400, 0, 7607600, 3069360, 1961960, 408980, 304920, 385000, 1190000, 208908, 0, 2732730, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_22_12_checked :
    (Witness.linear .positive case_44_22_12).check 44 22 12 = true := by
  change case_44_22_12.check 44 22 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_22_13 : Certificate := {
  objectiveScale := 10080000
  eta := 0
  rows := #[⟨.count 2, 72631278720⟩, ⟨.count 3, 33312615336⟩, ⟨.count 4, 9130369248⟩, ⟨.count 5, 2609727120⟩, ⟨.count 6, 782701920⟩, ⟨.count 7, 253513260⟩, ⟨.count 8, 91819728⟩, ⟨.count 9, 38918880⟩, ⟨.count 10, 18960480⟩, ⟨.count 11, 13721400⟩, ⟨.count 12, 13471920⟩, ⟨.path 12, 1972080⟩, ⟨.privateRow 11 3, 919380⟩, ⟨.privateRow 14 0, 1121120⟩, ⟨.hall 12 1, 1180872⟩, ⟨.hall 11 2, 460152⟩, ⟨.hall 12 2, 45738⟩, ⟨.hall 11 3, 76923⟩, ⟨.hall 0 4, 112720608⟩, ⟨.hall 1 4, 6630624⟩, ⟨.hall 10 4, 234864⟩, ⟨.hall 9 5, 182763⟩, ⟨.hall 0 6, 8648640⟩, ⟨.hall 9 6, 72792⟩, ⟨.hall 8 7, 217056⟩, ⟨.hall 8 8, 60704⟩, ⟨.hall 7 9, 146097⟩, ⟨.hall 7 10, 536004⟩, ⟨.hall 6 12, 2895156⟩, ⟨.hall 5 14, 14672658⟩, ⟨.hall 4 16, 106954848⟩, ⟨.hall 3 18, 1069620552⟩, ⟨.assumptionRow 13, 11635785⟩]
  caps := #[0, 0, 0, 0, 31462002, 11158290, 2522520, 2522520, 999999, 122949, 559350, 0, 135945, 247527, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_22_13_checked :
    (Witness.linear .conditional case_44_22_13).check 44 22 13 = true := by
  change case_44_22_13.check 44 22 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_22_14 : Certificate := {
  objectiveScale := 15120000
  eta := 58663725120
  rows := #[⟨.count 2, 72631278720⟩, ⟨.count 3, 21579870312⟩, ⟨.count 4, 6616209600⟩, ⟨.count 5, 2156394240⟩, ⟨.count 6, 748107360⟩, ⟨.count 7, 272432160⟩, ⟨.count 8, 102918816⟩, ⟨.count 9, 40216176⟩, ⟨.count 10, 18461520⟩, ⟨.count 11, 10062360⟩, ⟨.count 12, 7484400⟩, ⟨.count 13, 7135128⟩, ⟨.path 11, 2556180⟩, ⟨.privateRow 3 19, 3142699560⟩, ⟨.privateRow 15 0, 1891890⟩, ⟨.hall 0 1, 9777287520⟩, ⟨.hall 13 1, 1855854⟩, ⟨.hall 12 2, 948024⟩, ⟨.hall 11 3, 658350⟩, ⟨.hall 13 3, 14157⟩, ⟨.hall 10 4, 129906⟩, ⟨.hall 12 4, 23364⟩, ⟨.hall 10 5, 458460⟩, ⟨.hall 11 5, 95370⟩, ⟨.hall 9 6, 397116⟩, ⟨.hall 9 7, 232344⟩, ⟨.hall 8 8, 774928⟩, ⟨.hall 7 10, 1370628⟩, ⟨.hall 8 10, 221256⟩, ⟨.hall 6 12, 6320754⟩, ⟨.hall 7 12, 5119884⟩, ⟨.hall 5 14, 33549516⟩, ⟨.hall 4 16, 286990704⟩, ⟨.hall 3 18, 4587238656⟩, ⟨.assumptionRow 14, 7451136⟩]
  caps := #[0, 0, 0, 0, 0, 12252240, 0, 0, 720720, 463320, 403920, 0, 30240, 316008, 515088, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_22_14_checked :
    (Witness.linear .conditional case_44_22_14).check 44 22 14 = true := by
  change case_44_22_14.check 44 22 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_23_1_checked :
    (Witness.rising).check 44 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_23_2_checked :
    (Witness.rising).check 44 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_23_3_checked :
    (Witness.rising).check 44 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_23_4_checked :
    (Witness.rising).check 44 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_23_5_checked :
    (Witness.rising).check 44 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_23_6_checked :
    (Witness.rising).check 44 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_23_7_checked :
    (Witness.rising).check 44 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_23_8_checked :
    (Witness.rising).check 44 23 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_23_9_checked :
    (Witness.rising).check 44 23 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_23_10 : Certificate := {
  objectiveScale := 3938150216000000
  eta := 210189001166464320000
  rows := #[⟨.count 2, 49184226272952650880⟩, ⟨.count 3, 7633179516045283200⟩, ⟨.count 4, 1209508638291233280⟩, ⟨.count 5, 225589846453171200⟩, ⟨.count 6, 47992070699773200⟩, ⟨.count 7, 12526743877567920⟩, ⟨.count 8, 4772092905740160⟩, ⟨.count 9, 3904439650151040⟩, ⟨.path 10, 902946397466880⟩, ⟨.path 11, 710658680846400⟩, ⟨.privateRow 4 19, 40562789698791360⟩, ⟨.privateRow 6 11, 1452544512705000⟩, ⟨.privateRow 7 8, 662790681352800⟩, ⟨.privateRow 7 9, 1098123651604980⟩, ⟨.privateRow 7 10, 526789476607680⟩, ⟨.privateRow 8 5, 253887174220680⟩, ⟨.privateRow 8 6, 436538044218276⟩, ⟨.privateRow 8 7, 557346709319400⟩, ⟨.privateRow 8 8, 335537782434855⟩, ⟨.privateRow 9 2, 109098412315200⟩, ⟨.privateRow 9 3, 201618144327600⟩, ⟨.privateRow 9 4, 87978826615680⟩, ⟨.privateRow 10 0, 107264825553600⟩, ⟨.privateRow 11 0, 54257499172800⟩, ⟨.hall 6 9, 2174932960200⟩, ⟨.hall 5 12, 12093583273200⟩, ⟨.hall 7 15, 1708192346941080⟩, ⟨.hall 4 16, 687526410130560⟩]
  caps := #[0, 0, 0, 0, 0, 59871215564160, 511635730197800, 56013501332880, 69003707726720, 171673159268800, 0, 5311191600000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_23_10_checked :
    (Witness.linear .positive case_44_23_10).check 44 23 10 = true := by
  change case_44_23_10.check 44 23 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_23_11 : Certificate := {
  objectiveScale := 119208375000
  eta := 9032062665225600
  rows := #[⟨.count 2, 2439829914762240⟩, ⟨.count 3, 450059718588480⟩, ⟨.count 4, 78611254001280⟩, ⟨.count 5, 15857829187200⟩, ⟨.count 6, 3540774837600⟩, ⟨.count 7, 910917287280⟩, ⟨.count 8, 302630328000⟩, ⟨.count 9, 125707982400⟩, ⟨.count 10, 118724205600⟩, ⟨.path 11, 7238088000⟩, ⟨.path 12, 31456339200⟩, ⟨.privateRow 4 19, 1646308984320⟩, ⟨.privateRow 7 9, 7944046110⟩, ⟨.privateRow 7 10, 73063607760⟩, ⟨.privateRow 8 7, 23537914400⟩, ⟨.privateRow 8 8, 37072215180⟩, ⟨.privateRow 8 9, 55554281640⟩, ⟨.privateRow 9 4, 5333065920⟩, ⟨.privateRow 9 5, 9497936448⟩, ⟨.privateRow 9 6, 31452861440⟩, ⟨.privateRow 9 7, 18390612240⟩, ⟨.privateRow 10 2, 7449361920⟩, ⟨.privateRow 10 3, 7872621120⟩, ⟨.privateRow 11 0, 4346546400⟩, ⟨.privateRow 12 0, 2618916300⟩, ⟨.hall 7 8, 58639035⟩, ⟨.hall 6 9, 148685355⟩, ⟨.hall 7 9, 67721472⟩, ⟨.hall 6 10, 143383500⟩, ⟨.hall 5 13, 2356617120⟩, ⟨.hall 8 14, 20175355200⟩, ⟨.hall 4 17, 322522520320⟩]
  caps := #[0, 49737294406800, 1609993344960, 0, 0, 8079271200, 15131516400, 3933169955, 2724661940, 855766080, 484169400, 1685068200, 29343600, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_23_11_checked :
    (Witness.linear .positive case_44_23_11).check 44 23 11 = true := by
  change case_44_23_11.check 44 23 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_23_12 : Certificate := {
  objectiveScale := 62073000000
  eta := 6451473332304000
  rows := #[⟨.count 2, 1965218030455680⟩, ⟨.count 3, 421565909244480⟩, ⟨.count 4, 86019644430720⟩, ⟨.count 5, 18744456931200⟩, ⟨.count 6, 4724525005200⟩, ⟨.count 7, 1236826871280⟩, ⟨.count 8, 389229160320⟩, ⟨.count 9, 134733170880⟩, ⟨.count 10, 65002845600⟩, ⟨.count 11, 65002845600⟩, ⟨.path 13, 11883875850⟩, ⟨.path 14, 4846338189⟩, ⟨.privateRow 4 19, 1044773009280⟩, ⟨.privateRow 8 8, 4641301665⟩, ⟨.privateRow 8 9, 43532208720⟩, ⟨.privateRow 9 6, 8316862400⟩, ⟨.privateRow 9 7, 21175169400⟩, ⟨.privateRow 9 8, 44798497920⟩, ⟨.privateRow 10 4, 6677565048⟩, ⟨.privateRow 10 5, 12803590800⟩, ⟨.privateRow 10 6, 20830457340⟩, ⟨.privateRow 10 7, 12494053440⟩, ⟨.privateRow 11 2, 5176785600⟩, ⟨.privateRow 11 3, 7897039920⟩, ⟨.privateRow 11 4, 1611640800⟩, ⟨.privateRow 12 0, 3348631440⟩, ⟨.privateRow 13 0, 1074427200⟩, ⟨.privateRow 14 0, 512143632⟩, ⟨.hall 8 8, 176001408⟩, ⟨.hall 7 9, 450587907⟩, ⟨.hall 8 9, 72992832⟩, ⟨.hall 13 9, 4097149056⟩, ⟨.hall 6 12, 2517680880⟩, ⟨.hall 9 13, 53690662080⟩, ⟨.hall 5 15, 46528081600⟩, ⟨.hall 4 17, 308544075840⟩]
  caps := #[0, 0, 1875929745690, 403063689600, 94206992022, 15874300728, 29981741790, 4230162090, 1001543257, 4221800836, 0, 0, 0, 1540275660, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_23_12_checked :
    (Witness.linear .positive case_44_23_12).check 44 23 12 = true := by
  change case_44_23_12.check 44 23 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_23_13 : Certificate := {
  objectiveScale := 60465600000
  eta := 5864975756640000
  rows := #[⟨.count 2, 1489703842186560⟩, ⟨.count 3, 374123716686720⟩, ⟨.count 4, 94251189352320⟩, ⟨.count 5, 25299895420800⟩, ⟨.count 6, 7490100618000⟩, ⟨.count 7, 2351437648560⟩, ⟨.count 8, 811049279040⟩, ⟨.count 9, 310079689920⟩, ⟨.count 10, 146659312800⟩, ⟨.count 11, 139675536000⟩, ⟨.count 12, 41902660800⟩, ⟨.path 12, 14290333200⟩, ⟨.privateRow 8 9, 51663320280⟩, ⟨.privateRow 8 10, 43629205620⟩, ⟨.privateRow 9 7, 26072766720⟩, ⟨.privateRow 9 8, 89525367360⟩, ⟨.privateRow 10 5, 13269175920⟩, ⟨.privateRow 10 6, 45743738040⟩, ⟨.privateRow 10 7, 82308798000⟩, ⟨.privateRow 11 3, 7110754560⟩, ⟨.privateRow 11 4, 24549033600⟩, ⟨.privateRow 11 5, 43489882800⟩, ⟨.privateRow 12 0, 4597653060⟩, ⟨.privateRow 12 2, 15364308960⟩, ⟨.privateRow 12 3, 2483120640⟩, ⟨.privateRow 13 0, 7195406400⟩, ⟨.privateRow 14 0, 6052606560⟩, ⟨.hall 8 8, 1031946240⟩, ⟨.hall 9 8, 327909600⟩, ⟨.hall 8 9, 172125408⟩, ⟨.hall 9 9, 602795520⟩, ⟨.hall 7 10, 2619357195⟩, ⟨.hall 6 12, 8013737160⟩, ⟨.hall 10 12, 82730894400⟩, ⟨.hall 5 14, 31449818400⟩, ⟨.hall 4 17, 1385162018240⟩, ⟨.hall 3 19, 18706185834336⟩, ⟨.assumptionRow 13, 82431845496⟩]
  caps := #[0, 38681417030256, 0, 98869721184, 216164520000, 0, 22567575888, 22481110080, 0, 4929920424, 4917415536, 5631183216, 0, 3368840904, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_23_13_checked :
    (Witness.linear .conditional case_44_23_13).check 44 23 13 = true := by
  change case_44_23_13.check 44 23 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_23_14 : Certificate := {
  objectiveScale := 83721600000
  eta := 4457381575046400
  rows := #[⟨.count 2, 1184725102841280⟩, ⟨.count 3, 318560788465920⟩, ⟨.count 4, 88900685153280⟩, ⟨.count 5, 26873573126400⟩, ⟨.count 6, 8397991602000⟩, ⟨.count 7, 2732751861840⟩, ⟨.count 8, 968417049600⟩, ⟨.count 9, 385504479360⟩, ⟨.count 10, 167610643200⟩, ⟨.count 11, 76821544800⟩, ⟨.count 12, 67044257280⟩, ⟨.count 13, 60526065600⟩, ⟨.count 15, 90789098400⟩, ⟨.path 11, 15076089600⟩, ⟨.privateRow 3 20, 28398829979520⟩, ⟨.privateRow 8 9, 2593974240⟩, ⟨.privateRow 9 8, 77952251520⟩, ⟨.privateRow 9 9, 130829418720⟩, ⟨.privateRow 10 6, 27324026730⟩, ⟨.privateRow 10 7, 99269398800⟩, ⟨.privateRow 11 4, 9734961600⟩, ⟨.privateRow 11 5, 46823049000⟩, ⟨.privateRow 11 6, 96684494400⟩, ⟨.privateRow 11 7, 42960808800⟩, ⟨.privateRow 12 2, 1955457504⟩, ⟨.privateRow 12 3, 23589646080⟩, ⟨.privateRow 12 4, 51330759480⟩, ⟨.privateRow 12 5, 20452489200⟩, ⟨.privateRow 13 1, 11453393952⟩, ⟨.privateRow 13 2, 12519066560⟩, ⟨.privateRow 14 0, 4690770084⟩, ⟨.hall 9 7, 1852340400⟩, ⟨.hall 9 8, 365119200⟩, ⟨.hall 10 8, 514422720⟩, ⟨.hall 8 9, 3997179264⟩, ⟨.hall 10 9, 1938852720⟩, ⟨.hall 7 10, 1708027230⟩, ⟨.hall 7 11, 8494988502⟩, ⟨.hall 6 13, 48756225375⟩, ⟨.hall 5 14, 57776678960⟩, ⟨.hall 4 17, 2665624561600⟩, ⟨.hall 3 19, 43987318174800⟩, ⟨.assumptionRow 14, 64444236480⟩]
  caps := #[0, 35124853399680, 2805064610880, 67842403200, 259651379520, 0, 0, 652040100, 5850589440, 2065016520, 9609621450, 3862123920, 0, 3918170880, 9600762852, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_23_14_checked :
    (Witness.linear .conditional case_44_23_14).check 44 23 14 = true := by
  change case_44_23_14.check 44 23 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_24_1_checked :
    (Witness.rising).check 44 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_24_2_checked :
    (Witness.rising).check 44 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_24_3_checked :
    (Witness.rising).check 44 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_24_4_checked :
    (Witness.rising).check 44 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_24_5_checked :
    (Witness.rising).check 44 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_24_6_checked :
    (Witness.rising).check 44 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_24_7_checked :
    (Witness.rising).check 44 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_24_8_checked :
    (Witness.rising).check 44 24 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_24_9_checked :
    (Witness.rising).check 44 24 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_24_10 : Certificate := {
  objectiveScale := 9759750000
  eta := 668607236256960
  rows := #[⟨.count 2, 138289954682880⟩, ⟨.count 3, 19549919188800⟩, ⟨.count 4, 3123144984960⟩, ⟨.count 5, 582563381400⟩, ⟨.count 6, 124078434480⟩, ⟨.count 7, 31776184440⟩, ⟨.count 8, 12105213120⟩, ⟨.count 9, 9777287520⟩, ⟨.path 10, 2354207856⟩, ⟨.path 11, 1692340650⟩, ⟨.privateRow 5 15, 27841990176⟩, ⟨.privateRow 5 16, 36693927270⟩, ⟨.privateRow 6 11, 3467639175⟩, ⟨.privateRow 6 12, 6052606560⟩, ⟨.privateRow 6 13, 16476540080⟩, ⟨.privateRow 6 14, 13013104104⟩, ⟨.privateRow 6 15, 17275147890⟩, ⟨.privateRow 7 8, 1642850352⟩, ⟨.privateRow 7 9, 3194431240⟩, ⟨.privateRow 7 11, 12753706680⟩, ⟨.privateRow 7 12, 2233700040⟩, ⟨.privateRow 8 5, 640179540⟩, ⟨.privateRow 8 6, 1301522040⟩, ⟨.privateRow 8 7, 1711025316⟩, ⟨.privateRow 8 8, 1034633600⟩, ⟨.privateRow 9 2, 282676680⟩, ⟨.privateRow 9 3, 602873040⟩, ⟨.privateRow 9 4, 71131060⟩, ⟨.privateRow 10 0, 237025152⟩, ⟨.privateRow 11 0, 122442840⟩, ⟨.privateRow 12 1, 148728580⟩, ⟨.hall 12 3, 11110554⟩, ⟨.hall 4 17, 269004736⟩, ⟨.hall 4 18, 9047054016⟩, ⟨.hall 5 18, 35439604200⟩, ⟨.hall 3 20, 318482392800⟩]
  caps := #[0, 1149238670580, 0, 11651267628, 10857917070, 10289431152, 0, 975394992, 321946352, 0, 8678124, 123258330, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_24_10_checked :
    (Witness.linear .positive case_44_24_10).check 44 24 10 = true := by
  change case_44_24_10.check 44 24 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_24_11 : Certificate := {
  objectiveScale := 204954750000
  eta := 20691634469425920
  rows := #[⟨.count 2, 4745074070056320⟩, ⟨.count 3, 782202556175040⟩, ⟨.count 4, 139306792584960⟩, ⟨.count 5, 28280804151600⟩, ⟨.count 6, 6228132150240⟩, ⟨.count 7, 1652361590880⟩, ⟨.count 8, 508418951040⟩, ⟨.count 9, 234654900480⟩, ⟨.count 10, 213322636800⟩, ⟨.path 11, 15389173800⟩, ⟨.path 12, 51793641900⟩, ⟨.privateRow 5 16, 1890682974180⟩, ⟨.privateRow 6 12, 54473459040⟩, ⟨.privateRow 6 13, 515480325360⟩, ⟨.privateRow 6 14, 677891934720⟩, ⟨.privateRow 6 15, 1212791039460⟩, ⟨.privateRow 7 9, 10087677600⟩, ⟨.privateRow 7 10, 152071739820⟩, ⟨.privateRow 7 11, 237348642960⟩, ⟨.privateRow 7 12, 355590635400⟩, ⟨.privateRow 7 13, 423077198544⟩, ⟨.privateRow 7 14, 442596854700⟩, ⟨.privateRow 8 7, 42042336336⟩, ⟨.privateRow 8 8, 82020578640⟩, ⟨.privateRow 8 9, 14054850810⟩, ⟨.privateRow 8 10, 360362882880⟩, ⟨.privateRow 9 4, 9234104880⟩, ⟨.privateRow 9 5, 30813269760⟩, ⟨.privateRow 9 6, 46605070512⟩, ⟨.privateRow 9 7, 34401567200⟩, ⟨.privateRow 10 2, 14563372320⟩, ⟨.privateRow 10 3, 11110554000⟩, ⟨.privateRow 11 0, 6666332400⟩, ⟨.privateRow 12 0, 4011194880⟩, ⟨.hall 5 14, 1677896220⟩, ⟨.hall 5 15, 717341625⟩, ⟨.hall 6 17, 458989330800⟩, ⟨.hall 4 18, 794739097152⟩, ⟨.hall 3 20, 14405203612800⟩]
  caps := #[0, 0, 0, 1905057914760, 0, 63552368880, 61569668160, 0, 39561143622, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_24_11_checked :
    (Witness.linear .positive case_44_24_11).check 44 24 11 = true := by
  change case_44_24_11.check 44 24 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_24_12 : Certificate := {
  objectiveScale := 12269400000
  eta := 1711338189200640
  rows := #[⟨.count 2, 387803244628800⟩, ⟨.count 3, 84649525440480⟩, ⟨.count 4, 18445796328960⟩, ⟨.count 5, 4169927361600⟩, ⟨.count 6, 1042481840400⟩, ⟨.count 7, 263686583160⟩, ⟨.count 8, 79247488320⟩, ⟨.count 9, 28302674400⟩, ⟨.count 10, 12864852000⟩, ⟨.count 11, 11321069760⟩, ⟨.path 13, 3145897755⟩, ⟨.privateRow 11 3, 93562560⟩, ⟨.privateRow 12 3, 440263824⟩, ⟨.privateRow 13 0, 275164890⟩, ⟨.privateRow 14 0, 477837360⟩, ⟨.hall 11 3, 1099560⟩, ⟨.hall 10 4, 17221680⟩, ⟨.hall 9 5, 18566856⟩, ⟨.hall 8 7, 17446352⟩]
  caps := #[0, 0, 536279523780, 0, 0, 13630996665, 0, 568828260, 974898210, 0, 0, 1383226767, 1316449662, 315630315, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_24_12_checked :
    (Witness.linear .positive case_44_24_12).check 44 24 12 = true := by
  change case_44_24_12.check 44 24 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_24_13 : Certificate := {
  objectiveScale := 6336618750
  eta := 1076899779315360
  rows := #[⟨.count 2, 250484328974880⟩, ⟨.count 3, 56678935753440⟩, ⟨.count 4, 14698522238400⟩, ⟨.count 5, 3831474546900⟩, ⟨.count 6, 1030689059400⟩, ⟨.count 7, 318169231380⟩, ⟨.count 8, 107550162720⟩, ⟨.count 9, 39297174840⟩, ⟨.count 10, 18802476000⟩, ⟨.count 11, 10341361800⟩, ⟨.count 12, 11030785920⟩, ⟨.path 12, 1766693775⟩, ⟨.privateRow 3 21, 2437803688320⟩, ⟨.privateRow 5 16, 157964301495⟩, ⟨.privateRow 6 14, 100977652776⟩, ⟨.privateRow 6 15, 263273835825⟩, ⟨.privateRow 7 11, 1463267520⟩, ⟨.privateRow 7 12, 48546948450⟩, ⟨.privateRow 7 13, 116768748096⟩, ⟨.privateRow 7 14, 180850720050⟩, ⟨.privateRow 8 9, 3447120600⟩, ⟨.privateRow 8 10, 20042544060⟩, ⟨.privateRow 8 11, 51821713020⟩, ⟨.privateRow 8 12, 79559543448⟩, ⟨.privateRow 8 13, 92296654065⟩, ⟨.privateRow 9 7, 2527888440⟩, ⟨.privateRow 9 8, 9795567705⟩, ⟨.privateRow 9 9, 22488358200⟩, ⟨.privateRow 9 10, 36692683720⟩, ⟨.privateRow 9 11, 43111988304⟩, ⟨.privateRow 9 12, 8962513560⟩, ⟨.privateRow 10 5, 1504198080⟩, ⟨.privateRow 10 6, 5160235080⟩, ⟨.privateRow 10 7, 11116963935⟩, ⟨.privateRow 10 8, 17298277920⟩, ⟨.privateRow 10 9, 2412984420⟩, ⟨.privateRow 11 3, 888844320⟩, ⟨.privateRow 11 4, 2933186256⟩, ⟨.privateRow 11 5, 6058575600⟩, ⟨.privateRow 11 6, 188024760⟩, ⟨.privateRow 12 1, 612821440⟩, ⟨.privateRow 12 2, 1754897760⟩, ⟨.privateRow 13 0, 689424120⟩, ⟨.privateRow 14 0, 581981400⟩, ⟨.hall 6 15, 3917438525⟩, ⟨.hall 7 15, 11796249465⟩, ⟨.hall 6 16, 37578120580⟩, ⟨.hall 7 16, 102014492580⟩, ⟨.hall 5 17, 153961307500⟩, ⟨.hall 4 18, 254346700608⟩, ⟨.hall 3 20, 4861096640400⟩, ⟨.assumptionRow 13, 9565421712⟩]
  caps := #[0, 0, 1004249644398, 103587788304, 0, 0, 7056013965, 2024196174, 0, 2969218637, 0, 2950034955, 30516563, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_24_13_checked :
    (Witness.linear .conditional case_44_24_13).check 44 24 13 = true := by
  change case_44_24_13.check 44 24 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_24_14 : Certificate := {
  objectiveScale := 5426400000
  eta := 269788884805440
  rows := #[⟨.count 2, 74083904294400⟩, ⟨.count 3, 20578862304000⟩, ⟨.count 4, 5955764855040⟩, ⟨.count 5, 1815781968000⟩, ⟨.count 6, 581050229760⟩, ⟨.count 7, 196709713200⟩, ⟨.count 8, 72631278720⟩, ⟨.count 9, 29331862560⟩, ⟨.count 10, 12697776000⟩, ⟨.count 11, 5587021440⟩, ⟨.count 12, 5587021440⟩, ⟨.count 13, 6052606560⟩, ⟨.path 11, 775760700⟩, ⟨.privateRow 2 22, 7408390429440⟩, ⟨.privateRow 5 16, 336676239900⟩, ⟨.privateRow 6 14, 118227581472⟩, ⟨.privateRow 6 15, 333649936620⟩, ⟨.privateRow 7 12, 41431533000⟩, ⟨.privateRow 7 13, 127450600992⟩, ⟨.privateRow 7 14, 228269733120⟩, ⟨.privateRow 8 10, 14566163040⟩, ⟨.privateRow 8 11, 49817607840⟩, ⟨.privateRow 8 12, 95351832576⟩, ⟨.privateRow 8 13, 130014644760⟩, ⟨.privateRow 9 8, 5121436320⟩, ⟨.privateRow 9 9, 20020160160⟩, ⟨.privateRow 9 10, 41488807360⟩, ⟨.privateRow 9 11, 61053728736⟩, ⟨.privateRow 9 12, 66772665960⟩, ⟨.privateRow 10 6, 1791797280⟩, ⟨.privateRow 10 7, 8348787720⟩, ⟨.privateRow 10 8, 13314525120⟩, ⟨.privateRow 10 9, 41183120160⟩, ⟨.privateRow 10 10, 14678629056⟩, ⟨.privateRow 11 4, 571399920⟩, ⟨.privateRow 11 5, 3668246400⟩, ⟨.privateRow 11 6, 9142398720⟩, ⟨.privateRow 11 7, 11863350720⟩, ⟨.privateRow 12 2, 56434560⟩, ⟨.privateRow 12 3, 1784742960⟩, ⟨.privateRow 12 4, 4759314560⟩, ⟨.privateRow 12 5, 504383880⟩, ⟨.privateRow 13 1, 761866560⟩, ⟨.privateRow 13 2, 931170240⟩, ⟨.privateRow 14 0, 314421120⟩, ⟨.hall 7 13, 680600349⟩, ⟨.hall 7 14, 2609444838⟩, ⟨.hall 6 15, 7162745590⟩, ⟨.hall 8 15, 97190893800⟩, ⟨.hall 6 16, 52673500880⟩, ⟨.hall 5 17, 216973556800⟩, ⟨.hall 4 18, 363283816896⟩, ⟨.hall 3 19, 502712207712⟩, ⟨.hall 2 21, 9821729736000⟩, ⟨.assumptionRow 14, 4907472570⟩]
  caps := #[0, 5545232190960, 0, 0, 9287413200, 0, 0, 3002071072, 0, 0, 789403134, 97460700, 721229740, 0, 0, 5426400000, 0, 0, 0, 0, 0] }

theorem case_44_24_14_checked :
    (Witness.linear .conditional case_44_24_14).check 44 24 14 = true := by
  change case_44_24_14.check 44 24 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_24_15 : Certificate := {
  objectiveScale := 13513500000
  eta := 738986945336640
  rows := #[⟨.count 2, 194470248772800⟩, ⟨.count 3, 52167415940640⟩, ⟨.count 4, 14526255744000⟩, ⟨.count 5, 4176298526400⟩, ⟨.count 6, 1243810648080⟩, ⟨.count 7, 381314213280⟩, ⟨.count 8, 120120960960⟩, ⟨.count 9, 35617261680⟩, ⟨.count 10, 13332664800⟩, ⟨.count 11, 6285399120⟩, ⟨.count 12, 5587021440⟩, ⟨.count 13, 4539454920⟩, ⟨.count 14, 9078909840⟩, ⟨.path 10, 3410447040⟩, ⟨.privateRow 2 22, 22225171288320⟩, ⟨.privateRow 5 16, 869305617180⟩, ⟨.privateRow 6 14, 277814641104⟩, ⟨.privateRow 6 15, 881032542390⟩, ⟨.privateRow 7 12, 85817314440⟩, ⟨.privateRow 7 13, 313741184328⟩, ⟨.privateRow 7 14, 646710202710⟩, ⟨.privateRow 8 10, 25041828240⟩, ⟨.privateRow 8 11, 111333041820⟩, ⟨.privateRow 8 12, 254977690968⟩, ⟨.privateRow 8 13, 411606345150⟩, ⟨.privateRow 9 8, 6401795400⟩, ⟨.privateRow 9 9, 38909613600⟩, ⟨.privateRow 9 10, 102700317720⟩, ⟨.privateRow 9 11, 183068069184⟩, ⟨.privateRow 9 12, 240707507040⟩, ⟨.privateRow 10 6, 973496160⟩, ⟨.privateRow 10 7, 12999348180⟩, ⟨.privateRow 10 8, 41957079840⟩, ⟨.privateRow 10 9, 84313232640⟩, ⟨.privateRow 10 10, 124565182560⟩, ⟨.privateRow 10 11, 112232467620⟩, ⟨.privateRow 11 5, 3301421760⟩, ⟨.privateRow 11 6, 17165805930⟩, ⟨.privateRow 11 7, 33576547680⟩, ⟨.privateRow 11 8, 80948322000⟩, ⟨.privateRow 12 3, 186234048⟩, ⟨.privateRow 12 4, 6311264960⟩, ⟨.privateRow 12 5, 19932862950⟩, ⟨.privateRow 12 6, 20286208800⟩, ⟨.privateRow 13 2, 1187242056⟩, ⟨.privateRow 13 3, 9544494960⟩, ⟨.privateRow 13 4, 3579185610⟩, ⟨.privateRow 14 1, 3631563936⟩, ⟨.privateRow 15 0, 756575820⟩, ⟨.hall 8 12, 720633672⟩, ⟨.hall 7 13, 86783697⟩, ⟨.hall 8 13, 5858058492⟩, ⟨.hall 7 14, 24210426240⟩, ⟨.hall 6 16, 384844900440⟩, ⟨.hall 5 17, 685962076800⟩, ⟨.hall 4 18, 1083161727648⟩, ⟨.hall 3 19, 1466243939160⟩, ⟨.hall 2 21, 29044257933600⟩, ⟨.assumptionRow 15, 5940280080⟩]
  caps := #[0, 0, 0, 133411299840, 0, 0, 0, 706982562, 2668231566, 1047246480, 978386760, 733133700, 415634688, 3231087552, 0, 0, 13513500000, 0, 0, 0, 0] }

theorem case_44_24_15_checked :
    (Witness.linear .conditional case_44_24_15).check 44 24 15 = true := by
  change case_44_24_15.check 44 24 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_25_1_checked :
    (Witness.rising).check 44 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_25_2_checked :
    (Witness.rising).check 44 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_25_3_checked :
    (Witness.rising).check 44 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_25_4_checked :
    (Witness.rising).check 44 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_25_5_checked :
    (Witness.rising).check 44 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_25_6_checked :
    (Witness.rising).check 44 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_25_7_checked :
    (Witness.rising).check 44 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_25_8_checked :
    (Witness.rising).check 44 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_25_9_checked :
    (Witness.rising).check 44 25 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_25_10_checked :
    (Witness.linear .positive case_44_25_10).check 44 25 10 = true := by
  change case_44_25_10.check 44 25 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_25_11 : Certificate := {
  objectiveScale := 501000500000
  eta := 62749066937356800
  rows := #[⟨.count 2, 11725835740819200⟩, ⟨.count 3, 1957412961504000⟩, ⟨.count 4, 353033409128400⟩, ⟨.count 5, 71072732530800⟩, ⟨.count 6, 15978881318400⟩, ⟨.count 7, 4033131102000⟩, ⟨.count 8, 1254751898400⟩, ⟨.count 9, 586637251200⟩, ⟨.count 10, 439977938400⟩, ⟨.path 11, 43136143050⟩, ⟨.path 12, 122569772325⟩, ⟨.privateRow 4 19, 13398957772200⟩, ⟨.privateRow 5 16, 5079952685808⟩, ⟨.privateRow 5 17, 7107273253080⟩, ⟨.privateRow 5 18, 10874516452800⟩, ⟨.privateRow 6 12, 93626257725⟩, ⟨.privateRow 6 13, 1379129637600⟩, ⟨.privateRow 6 14, 2247030185400⟩, ⟨.privateRow 6 15, 3262354935840⟩, ⟨.privateRow 6 16, 4098749504850⟩, ⟨.privateRow 6 17, 3578603628600⟩, ⟨.privateRow 7 9, 11523231720⟩, ⟨.privateRow 7 10, 405447042000⟩, ⟨.privateRow 7 11, 739407368700⟩, ⟨.privateRow 7 12, 1070014374000⟩, ⟨.privateRow 7 13, 1229144716800⟩, ⟨.privateRow 7 14, 1582523822880⟩, ⟨.privateRow 7 15, 38410772400⟩, ⟨.privateRow 8 7, 105920614800⟩, ⟨.privateRow 8 8, 255431636460⟩, ⟨.privateRow 8 9, 388375587600⟩, ⟨.privateRow 8 10, 476133532875⟩, ⟨.privateRow 8 11, 147241294200⟩, ⟨.privateRow 9 4, 22562971200⟩, ⟨.privateRow 9 5, 39380741400⟩, ⟨.privateRow 9 6, 254802038400⟩, ⟨.privateRow 10 2, 40855094280⟩, ⟨.privateRow 10 3, 21434822640⟩, ⟨.privateRow 11 0, 14122748640⟩, ⟨.privateRow 12 0, 8002244250⟩, ⟨.hall 13 8, 252191940⟩, ⟨.hall 12 11, 6894241200⟩, ⟨.hall 4 19, 416116701000⟩, ⟨.hall 5 19, 3553636626540⟩, ⟨.hall 4 20, 16811114720400⟩, ⟨.hall 3 21, 59739226747200⟩]
  caps := #[0, 273675330728800, 0, 4175037566700, 0, 0, 0, 734730367800, 42363446125, 46537064000, 61022561600, 0, 10538352825, 76821544800, 0, 0, 0, 0, 0, 0] }

theorem case_44_25_11_checked :
    (Witness.linear .positive case_44_25_11).check 44 25 11 = true := by
  change case_44_25_11.check 44 25 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_25_12 : Certificate := {
  objectiveScale := 390390000
  eta := 78714148312800
  rows := #[⟨.count 2, 16360195531680⟩, ⟨.count 3, 3740510854080⟩, ⟨.count 4, 817101885600⟩, ⟨.count 5, 196709713200⟩, ⟨.count 6, 46043042760⟩, ⟨.count 7, 12221609400⟩, ⟨.count 8, 3259095840⟩, ⟨.count 9, 1142799840⟩, ⟨.count 10, 380933280⟩, ⟨.count 11, 465585120⟩, ⟨.path 12, 68630562⟩, ⟨.path 13, 42894852⟩, ⟨.privateRow 11 9, 116396280⟩, ⟨.privateRow 12 0, 4157010⟩, ⟨.privateRow 12 4, 5819814⟩, ⟨.privateRow 13 0, 3837240⟩, ⟨.hall 13 1, 9006855⟩, ⟨.hall 12 2, 6395400⟩, ⟨.hall 11 4, 1540710⟩, ⟨.hall 9 5, 3148281⟩, ⟨.hall 8 8, 1655584⟩, ⟨.hall 9 11, 10430316⟩, ⟨.hall 10 11, 43884072⟩, ⟨.hall 8 13, 23303709⟩, ⟨.hall 7 14, 63561498⟩, ⟨.hall 5 15, 84831747⟩, ⟨.hall 4 17, 346052850⟩]
  caps := #[0, 0, 27135852744, 4993400412, 0, 166306140, 0, 29008980, 153969816, 0, 183073800, 0, 0, 1004982, 0, 0, 0, 0, 0, 0] }

theorem case_44_25_12_checked :
    (Witness.linear .positive case_44_25_12).check 44 25 12 = true := by
  change case_44_25_12.check 44 25 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_25_13 : Certificate := {
  objectiveScale := 198198000000
  eta := 52053203254852800
  rows := #[⟨.count 2, 11012778161985600⟩, ⟨.count 3, 2600562934569600⟩, ⟨.count 4, 604700789893200⟩, ⟨.count 5, 159622366503600⟩, ⟨.count 6, 42943243543200⟩, ⟨.count 7, 12099393306000⟩, ⟨.count 8, 3943505966400⟩, ⟨.count 9, 1466593128000⟩, ⟨.count 10, 586637251200⟩, ⟨.count 11, 358500542400⟩, ⟨.count 12, 268875406800⟩, ⟨.path 12, 64253314125⟩, ⟨.privateRow 3 22, 256327887816000⟩, ⟨.privateRow 4 19, 33788676121200⟩, ⟨.privateRow 5 16, 512655775632⟩, ⟨.privateRow 5 17, 20331462010860⟩, ⟨.privateRow 5 18, 40934786933040⟩, ⟨.privateRow 6 14, 2177677401900⟩, ⟨.privateRow 6 15, 7822993978800⟩, ⟨.privateRow 6 16, 17726571462600⟩, ⟨.privateRow 6 17, 23663169730200⟩, ⟨.privateRow 7 12, 1525456389600⟩, ⟨.privateRow 7 13, 3546594651600⟩, ⟨.privateRow 7 14, 7067582121600⟩, ⟨.privateRow 7 15, 9977198130900⟩, ⟨.privateRow 7 16, 10038015187200⟩, ⟨.privateRow 8 9, 19916696800⟩, ⟨.privateRow 8 10, 801024649425⟩, ⟨.privateRow 8 11, 1709279371800⟩, ⟨.privateRow 8 12, 2875473100500⟩, ⟨.privateRow 8 13, 4727725902900⟩, ⟨.privateRow 8 14, 4167568805400⟩, ⟨.privateRow 9 7, 50515985520⟩, ⟨.privateRow 9 8, 367553586400⟩, ⟨.privateRow 9 9, 839217178800⟩, ⟨.privateRow 9 10, 1522463342400⟩, ⟨.privateRow 9 11, 1873980108000⟩, ⟨.privateRow 10 5, 45331060320⟩, ⟨.privateRow 10 6, 196523479152⟩, ⟨.privateRow 10 7, 409016527920⟩, ⟨.privateRow 10 8, 733296564000⟩, ⟨.privateRow 11 3, 32590958400⟩, ⟨.privateRow 11 4, 121475390400⟩, ⟨.privateRow 11 5, 200434394160⟩, ⟨.privateRow 12 1, 24129844200⟩, ⟨.privateRow 12 2, 52281329100⟩, ⟨.privateRow 13 0, 20682723600⟩, ⟨.privateRow 14 0, 13870556700⟩, ⟨.hall 6 18, 14296893811200⟩, ⟨.hall 5 19, 62101256457240⟩, ⟨.hall 4 20, 150134905720800⟩, ⟨.hall 3 21, 253573951831200⟩, ⟨.assumptionRow 13, 321277306350⟩]
  caps := #[0, 275223853905000, 25292960142450, 12816394390800, 1558393546710, 713881051884, 0, 31527639000, 28470316875, 206147101160, 50479303875, 27030078075, 252803899425, 0, 31751319600, 0, 0, 0, 0, 0] }

theorem case_44_25_13_checked :
    (Witness.linear .conditional case_44_25_13).check 44 25 13 = true := by
  change case_44_25_13.check 44 25 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_25_14 : Certificate := {
  objectiveScale := 10363892000000
  eta := 1410427890932860800
  rows := #[⟨.count 2, 353518101861724800⟩, ⟨.count 3, 88754696283052800⟩, ⟨.count 4, 24600486469759200⟩, ⟨.count 5, 7074649703721600⟩, ⟨.count 6, 2090237412463200⟩, ⟨.count 7, 655518241778400⟩, ⟨.count 8, 214383324355200⟩, ⟨.count 9, 80955940665600⟩, ⟨.count 10, 33731641944000⟩, ⟨.count 11, 16491024950400⟩, ⟨.count 12, 12368268712800⟩, ⟨.path 11, 2259432094920⟩, ⟨.privateRow 2 23, 16400324313172800⟩, ⟨.privateRow 4 19, 3765107133988200⟩, ⟨.privateRow 5 16, 150068327048640⟩, ⟨.privateRow 5 17, 1345255360328880⟩, ⟨.privateRow 5 18, 3269345696416800⟩, ⟨.privateRow 6 14, 102087297312000⟩, ⟨.privateRow 6 15, 514519978452480⟩, ⟨.privateRow 6 16, 1250888414876100⟩, ⟨.privateRow 6 17, 1958800017174000⟩, ⟨.privateRow 7 12, 50482729440000⟩, ⟨.privateRow 7 13, 206432294468400⟩, ⟨.privateRow 7 14, 499324676891040⟩, ⟨.privateRow 7 15, 799520227506000⟩, ⟨.privateRow 7 16, 950000830178400⟩, ⟨.privateRow 8 10, 22030978644675⟩, ⟨.privateRow 8 11, 86136157107000⟩, ⟨.privateRow 8 12, 210088786607700⟩, ⟨.privateRow 8 13, 345074697087120⟩, ⟨.privateRow 8 14, 430312682299500⟩, ⟨.privateRow 8 15, 377232195740400⟩, ⟨.privateRow 9 8, 9078392523200⟩, ⟨.privateRow 9 9, 37104806138400⟩, ⟨.privateRow 9 10, 93591920822400⟩, ⟨.privateRow 9 11, 124432279171200⟩, ⟨.privateRow 9 12, 280197505748160⟩, ⟨.privateRow 10 6, 3575554046064⟩, ⟨.privateRow 10 7, 16640943359040⟩, ⟨.privateRow 10 8, 23696478465660⟩, ⟨.privateRow 10 9, 121915791597600⟩, ⟨.privateRow 10 10, 20014107553440⟩, ⟨.privateRow 11 4, 1226605161600⟩, ⟨.privateRow 11 5, 7795757249280⟩, ⟨.privateRow 11 6, 22571049300800⟩, ⟨.privateRow 11 7, 25954624495800⟩, ⟨.privateRow 12 2, 85890754950⟩, ⟨.privateRow 12 3, 4029057232200⟩, ⟨.privateRow 12 4, 11234510747460⟩, ⟨.privateRow 13 1, 1619654236200⟩, ⟨.privateRow 13 2, 1766895530400⟩, ⟨.privateRow 14 0, 638045608200⟩, ⟨.hall 6 16, 363468705600⟩, ⟨.hall 6 17, 113706443650800⟩, ⟨.hall 7 17, 135363829801200⟩, ⟨.hall 5 19, 6080447037024360⟩, ⟨.hall 4 20, 13092695880264000⟩, ⟨.hall 3 21, 23124164940676800⟩, ⟨.hall 2 22, 29473046591788800⟩, ⟨.assumptionRow 14, 10646047011600⟩]
  caps := #[0, 1309517758823120, 0, 0, 62954177766480, 0, 17235411493300, 1392944321340, 2956349285120, 0, 0, 0, 0, 23789410167600, 0, 10363892000000, 0, 0, 0, 0] }

theorem case_44_25_14_checked :
    (Witness.linear .conditional case_44_25_14).check 44 25 14 = true := by
  change case_44_25_14.check 44 25 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_25_15 : Certificate := {
  objectiveScale := 1541736000000
  eta := 208731400349472000
  rows := #[⟨.count 2, 51354550879632000⟩, ⟨.count 3, 12804531281942400⟩, ⟨.count 4, 3464239627648800⟩, ⟨.count 5, 950107914756000⟩, ⟨.count 6, 267283105689600⟩, ⟨.count 7, 76458388406400⟩, ⟨.count 8, 21738169252800⟩, ⟨.count 9, 7359630969600⟩, ⟨.count 10, 2453210323200⟩, ⟨.count 11, 1499184086400⟩, ⟨.count 12, 1124388064800⟩, ⟨.path 10, 491598607500⟩, ⟨.privateRow 2 23, 3644516514038400⟩, ⟨.privateRow 4 19, 598080751468200⟩, ⟨.privateRow 5 16, 14032363048704⟩, ⟨.privateRow 5 17, 202689688481280⟩, ⟨.privateRow 5 18, 541480305606240⟩, ⟨.privateRow 6 14, 8294592906600⟩, ⟨.privateRow 6 15, 71414704801440⟩, ⟨.privateRow 6 16, 199418254635600⟩, ⟨.privateRow 6 17, 350693067925200⟩, ⟨.privateRow 7 12, 3258430718400⟩, ⟨.privateRow 7 13, 25646756335200⟩, ⟨.privateRow 7 14, 75398251088160⟩, ⟨.privateRow 7 15, 140106784217400⟩, ⟨.privateRow 7 16, 196660826762400⟩, ⟨.privateRow 8 10, 948702429675⟩, ⟨.privateRow 8 11, 9195888101400⟩, ⟨.privateRow 8 12, 29327788690200⟩, ⟨.privateRow 8 13, 58318260960960⟩, ⟨.privateRow 8 14, 86367058227450⟩, ⟨.privateRow 8 15, 95947781529600⟩, ⟨.privateRow 9 8, 121146188800⟩, ⟨.privateRow 9 9, 3194284275000⟩, ⟨.privateRow 9 10, 11691688881600⟩, ⟨.privateRow 9 11, 25463414558400⟩, ⟨.privateRow 9 12, 40505228225280⟩, ⟨.privateRow 9 13, 49064206464000⟩, ⟨.privateRow 9 14, 12515915630400⟩, ⟨.privateRow 10 7, 879067032480⟩, ⟨.privateRow 10 8, 4714763589900⟩, ⟨.privateRow 10 9, 11670271966080⟩, ⟨.privateRow 10 10, 20433197650320⟩, ⟨.privateRow 10 11, 15994931307264⟩, ⟨.privateRow 11 5, 156732881760⟩, ⟨.privateRow 11 6, 1733904827200⟩, ⟨.privateRow 11 7, 5000119651800⟩, ⟨.privateRow 11 8, 12227111769600⟩, ⟨.privateRow 12 4, 543454231320⟩, ⟨.privateRow 12 5, 2571517148200⟩, ⟨.privateRow 12 6, 3326314691700⟩, ⟨.privateRow 13 2, 87614654400⟩, ⟨.privateRow 13 3, 1124388064800⟩, ⟨.privateRow 13 4, 678202324800⟩, ⟨.privateRow 14 1, 411302127600⟩, ⟨.privateRow 14 2, 34802487720⟩, ⟨.privateRow 15 0, 88588150560⟩, ⟨.hall 7 17, 135676159819200⟩, ⟨.hall 6 18, 533577088044000⟩, ⟨.hall 5 19, 1267785022664160⟩, ⟨.hall 4 20, 2459839832049600⟩, ⟨.hall 3 21, 4103403133939200⟩, ⟨.hall 2 22, 5243494115059200⟩, ⟨.assumptionRow 15, 948484552400⟩]
  caps := #[0, 0, 6996119599000, 7646749933200, 20094177612600, 3313164950368, 1379903765240, 281841777360, 513112104505, 283264275840, 290590493900, 0, 0, 948484552400, 948484552400, 0, 1541736000000, 0, 0, 0] }

theorem case_44_25_15_checked :
    (Witness.linear .conditional case_44_25_15).check 44 25 15 = true := by
  change case_44_25_15.check 44 25 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_25_16 : Certificate := {
  objectiveScale := 89258400000
  eta := 11010007930521600
  rows := #[⟨.count 2, 2854446500505600⟩, ⟨.count 3, 764583884064000⟩, ⟨.count 4, 214758120376800⟩, ⟨.count 5, 61091751520800⟩, ⟨.count 6, 17508328437600⟩, ⟨.count 7, 5189483376000⟩, ⟨.count 8, 1556845012800⟩, ⟨.count 9, 471771216000⟩, ⟨.count 10, 141531364800⟩, ⟨.path 10, 4910805900⟩, ⟨.path 11, 25170124980⟩, ⟨.privateRow 2 23, 344062747828800⟩, ⟨.privateRow 4 19, 42164552430000⟩, ⟨.privateRow 5 16, 299836817280⟩, ⟨.privateRow 5 17, 13736274191640⟩, ⟨.privateRow 5 18, 39353582268000⟩, ⟨.privateRow 6 14, 129393864600⟩, ⟨.privateRow 6 15, 4518969174720⟩, ⟨.privateRow 6 16, 14074929168300⟩, ⟨.privateRow 6 17, 26842534118400⟩, ⟨.privateRow 7 12, 26476956000⟩, ⟨.privateRow 7 13, 1478590898400⟩, ⟨.privateRow 7 14, 5080751343360⟩, ⟨.privateRow 7 15, 10465458141600⟩, ⟨.privateRow 7 16, 16173889855200⟩, ⟨.privateRow 8 11, 462317070600⟩, ⟨.privateRow 8 12, 1846350914100⟩, ⟨.privateRow 8 13, 4183300210320⟩, ⟨.privateRow 8 14, 6933726399600⟩, ⟨.privateRow 8 15, 8694787193400⟩, ⟨.privateRow 9 9, 133013273400⟩, ⟨.privateRow 9 10, 662726232000⟩, ⟨.privateRow 9 11, 1714102084800⟩, ⟨.privateRow 9 12, 3114738406080⟩, ⟨.privateRow 9 13, 4324569480000⟩, ⟨.privateRow 9 14, 4231962537600⟩, ⟨.privateRow 10 7, 35644936320⟩, ⟨.privateRow 10 8, 228809039760⟩, ⟨.privateRow 10 9, 711026618400⟩, ⟨.privateRow 10 10, 1246262295600⟩, ⟨.privateRow 10 11, 2713628034432⟩, ⟨.privateRow 10 12, 789037358760⟩, ⟨.privateRow 11 5, 7338663360⟩, ⟨.privateRow 11 6, 75133934400⟩, ⟨.privateRow 11 7, 292236058800⟩, ⟨.privateRow 11 8, 717391785600⟩, ⟨.privateRow 11 9, 1127882666400⟩, ⟨.privateRow 12 4, 20181324240⟩, ⟨.privateRow 12 5, 117724391400⟩, ⟨.privateRow 12 6, 357677934075⟩, ⟨.privateRow 12 7, 340817261400⟩, ⟨.privateRow 13 3, 42010103520⟩, ⟨.privateRow 13 4, 179847175200⟩, ⟨.privateRow 13 5, 64868542200⟩, ⟨.privateRow 14 2, 82990547640⟩, ⟨.privateRow 14 3, 2974571600⟩, ⟨.privateRow 15 1, 22487761296⟩, ⟨.hall 7 16, 525731976000⟩, ⟨.hall 8 16, 335790100800⟩, ⟨.hall 7 17, 8745240504000⟩, ⟨.hall 6 18, 50605916961600⟩, ⟨.hall 5 19, 107678897005680⟩, ⟨.hall 4 20, 196125403874400⟩, ⟨.hall 3 21, 315441960724800⟩, ⟨.hall 2 22, 408886164086400⟩]
  caps := #[0, 0, 7659293056800, 1783862526600, 934369102800, 0, 112455580380, 0, 36245392260, 5456673180, 0, 25170124980, 58207660665, 0, 66885923720, 65708463744, 714067200000, 89258400000, 0, 0] }

theorem case_44_25_16_checked :
    (Witness.linear .negative case_44_25_16).check 44 25 16 = true := by
  change case_44_25_16.check 44 25 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_26_1_checked :
    (Witness.rising).check 44 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_26_2_checked :
    (Witness.rising).check 44 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_26_3_checked :
    (Witness.rising).check 44 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_26_4_checked :
    (Witness.rising).check 44 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_26_5_checked :
    (Witness.rising).check 44 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_26_6_checked :
    (Witness.rising).check 44 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_26_7_checked :
    (Witness.rising).check 44 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_26_8_checked :
    (Witness.rising).check 44 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_26_9_checked :
    (Witness.linear .positive case_44_26_9).check 44 26 9 = true := by
  change case_44_26_9.check 44 26 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_26_10_checked :
    (Witness.linear .positive case_44_26_10).check 44 26 10 = true := by
  change case_44_26_10.check 44 26 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_26_11_checked :
    (Witness.linear .positive case_44_26_11).check 44 26 11 = true := by
  change case_44_26_11.check 44 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_26_12 : Certificate := {
  objectiveScale := 2683931250
  eta := 625906096976160
  rows := #[⟨.count 2, 133290501664320⟩, ⟨.count 3, 31283653581180⟩, ⟨.count 4, 7037365647312⟩, ⟨.count 5, 1681111472040⟩, ⟨.count 6, 407154187440⟩, ⟨.count 7, 103068905940⟩, ⟨.count 8, 29331862560⟩, ⟨.count 9, 8799558768⟩, ⟨.count 10, 3259095840⟩, ⟨.count 11, 4481256780⟩, ⟨.path 12, 825791967⟩, ⟨.hall 11 3, 12662892⟩, ⟨.hall 12 3, 38692170⟩, ⟨.hall 11 4, 3751968⟩, ⟨.hall 9 5, 3054744⟩, ⟨.hall 8 9, 21450240⟩, ⟨.hall 10 9, 3947706⟩, ⟨.hall 6 13, 56797884⟩, ⟨.hall 7 14, 379989610⟩]
  caps := #[0, 0, 201955305552, 0, 0, 1600052454, 3841077240, 980881902, 0, 0, 250627377, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_26_12_checked :
    (Witness.linear .positive case_44_26_12).check 44 26 12 = true := by
  change case_44_26_12.check 44 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_26_13 : Certificate := {
  objectiveScale := 5720000
  eta := 2232015065280
  rows := #[⟨.count 2, 522386504640⟩, ⟨.count 3, 131993381520⟩, ⟨.count 4, 33382453104⟩, ⟨.count 5, 8430416280⟩, ⟨.count 6, 2095133040⟩, ⟨.count 7, 590934960⟩, ⟨.count 8, 166047840⟩, ⟨.count 9, 52744608⟩, ⟨.count 10, 19535040⟩, ⟨.count 11, 13430340⟩, ⟨.path 10, 1001520⟩, ⟨.path 11, 1080261⟩, ⟨.hall 11 8, 11628⟩]
  caps := #[0, 6316068616, 0, 119495142, 21274344, 0, 11249667, 0, 2569336, 0, 0, 0, 5720000, 0, 0, 0, 0, 0, 0] }

theorem case_44_26_13_checked :
    (Witness.linear .positive case_44_26_13).check 44 26 13 = true := by
  change case_44_26_13.check 44 26 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_26_14 : Certificate := {
  objectiveScale := 17787000000
  eta := 6259060969761600
  rows := #[⟨.count 2, 1351547044848000⟩, ⟨.count 3, 328565747109600⟩, ⟨.count 4, 79228619870400⟩, ⟨.count 5, 19474261606800⟩, ⟨.count 6, 5300686591200⟩, ⟨.count 7, 1478814737400⟩, ⟨.count 8, 423682459200⟩, ⟨.count 9, 146659312800⟩, ⟨.count 10, 65181916800⟩, ⟨.path 10, 8994585600⟩, ⟨.privateRow 2 24, 65247098716800⟩, ⟨.privateRow 4 19, 3641021133750⟩, ⟨.privateRow 4 20, 14602922093760⟩, ⟨.privateRow 5 17, 2463410869920⟩, ⟨.privateRow 5 18, 5684154135660⟩, ⟨.privateRow 5 19, 11407145830080⟩, ⟨.privateRow 6 14, 42068941200⟩, ⟨.privateRow 6 15, 1160858899200⟩, ⟨.privateRow 6 16, 2371225016160⟩, ⟨.privateRow 6 17, 4490859473100⟩, ⟨.privateRow 6 18, 5987812630800⟩, ⟨.privateRow 7 12, 70419749400⟩, ⟨.privateRow 7 13, 465501979800⟩, ⟨.privateRow 7 14, 1016818502700⟩, ⟨.privateRow 7 15, 1891090361160⟩, ⟨.privateRow 7 16, 2511104245650⟩, ⟨.privateRow 7 17, 2537244910200⟩, ⟨.privateRow 8 10, 47981133200⟩, ⟨.privateRow 8 11, 201147321375⟩, ⟨.privateRow 8 12, 433576143000⟩, ⟨.privateRow 8 13, 851438788200⟩, ⟨.privateRow 8 14, 1156979023200⟩, ⟨.privateRow 8 15, 848383385850⟩, ⟨.privateRow 9 8, 25095037968⟩, ⟨.privateRow 9 9, 95238022880⟩, ⟨.privateRow 9 10, 200841781140⟩, ⟨.privateRow 9 11, 401334373440⟩, ⟨.privateRow 9 12, 511134864240⟩, ⟨.privateRow 10 6, 11554976160⟩, ⟨.privateRow 10 7, 47908708848⟩, ⟨.privateRow 10 8, 103928945120⟩, ⟨.privateRow 10 9, 210619068660⟩, ⟨.privateRow 10 10, 26072766720⟩, ⟨.privateRow 11 4, 4752848100⟩, ⟨.privateRow 11 5, 25554274200⟩, ⟨.privateRow 11 6, 59885886060⟩, ⟨.privateRow 11 7, 27611784200⟩, ⟨.privateRow 12 2, 984891600⟩, ⟨.privateRow 12 3, 14404039650⟩, ⟨.privateRow 12 4, 14549535000⟩, ⟨.privateRow 13 1, 6894241200⟩, ⟨.privateRow 14 0, 2560718160⟩, ⟨.hall 6 19, 1736166912480⟩, ⟨.hall 5 20, 11849418438000⟩, ⟨.hall 4 21, 32665917604320⟩, ⟨.hall 3 22, 68159915623800⟩, ⟨.hall 2 23, 104473033064400⟩, ⟨.assumptionRow 14, 19261674432⟩]
  caps := #[0, 11890924584000, 2685523623552, 46837863072, 270817284738, 63086783760, 0, 61233480, 49893146303, 0, 0, 19261674432, 91412591886, 12367433232, 0, 17787000000, 0, 0, 0] }

theorem case_44_26_14_checked :
    (Witness.linear .conditional case_44_26_14).check 44 26 14 = true := by
  change case_44_26_14.check 44 26 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_26_15 : Certificate := {
  objectiveScale := 46160148919500000
  eta := 14255703932011340198400
  rows := #[⟨.count 2, 3193019658979915564800⟩, ⟨.count 3, 743828443285093966800⟩, ⟨.count 4, 172552072480227760320⟩, ⟨.count 5, 40027934036634944400⟩, ⟨.count 6, 9968218216096140000⟩, ⟨.count 7, 2480978756006150400⟩, ⟨.count 8, 620244689001537600⟩, ⟨.count 9, 202989170945957760⟩, ⟨.count 10, 112771761636643200⟩, ⟨.count 11, 77530586125192200⟩, ⟨.path 9, 36406009177836480⟩, ⟨.privateRow 2 24, 306400876366759574400⟩, ⟨.privateRow 3 21, 16462327787249143800⟩, ⟨.privateRow 4 19, 13556222983989856170⟩, ⟨.privateRow 4 20, 43406790818624273040⟩, ⟨.privateRow 5 17, 6657883704510790752⟩, ⟨.privateRow 5 18, 16198354601156227500⟩, ⟨.privateRow 5 19, 34633282015390618560⟩, ⟨.privateRow 6 15, 2724646312399611600⟩, ⟨.privateRow 6 16, 6322065508608529680⟩, ⟨.privateRow 6 17, 13346336611550943000⟩, ⟨.privateRow 6 18, 19921668701501767200⟩, ⟨.privateRow 7 12, 42918717319302825⟩, ⟨.privateRow 7 13, 971505711854449200⟩, ⟨.privateRow 7 14, 2519744049068746500⟩, ⟨.privateRow 7 15, 5418280390349146320⟩, ⟨.privateRow 7 16, 8326231159944748050⟩, ⟨.privateRow 7 17, 9960834350750883600⟩, ⟨.privateRow 8 10, 20361568073282800⟩, ⟨.privateRow 8 11, 352411755114510000⟩, ⟨.privateRow 8 12, 991787367965121000⟩, ⟨.privateRow 8 13, 2320044054503857500⟩, ⟨.privateRow 8 14, 3744022486336554240⟩, ⟨.privateRow 8 15, 4713507224656571250⟩, ⟨.privateRow 8 16, 2802848159010736200⟩, ⟨.privateRow 9 8, 563858808183216⟩, ⟨.privateRow 9 9, 128434506308399200⟩, ⟨.privateRow 9 10, 405273518381686500⟩, ⟨.privateRow 9 11, 1026223030893453120⟩, ⟨.privateRow 9 12, 1826902538513619840⟩, ⟨.privateRow 9 13, 2285883608374757664⟩, ⟨.privateRow 10 7, 35523104915542608⟩, ⟨.privateRow 10 8, 171663681602445760⟩, ⟨.privateRow 10 9, 483508928017107720⟩, ⟨.privateRow 10 10, 952115873246516160⟩, ⟨.privateRow 10 11, 481159516316344320⟩, ⟨.privateRow 11 5, 7048235102290200⟩, ⟨.privateRow 11 6, 64138939430840820⟩, ⟨.privateRow 11 7, 242772542412218000⟩, ⟨.privateRow 11 8, 418488959198480625⟩, ⟨.privateRow 12 4, 20137814577972000⟩, ⟨.privateRow 12 5, 114080719584211380⟩, ⟨.privateRow 12 6, 99682182160961400⟩, ⟨.privateRow 13 2, 1845966336314100⟩, ⟨.privateRow 13 3, 50344536444930000⟩, ⟨.privateRow 13 4, 11075798017884600⟩, ⟨.privateRow 14 1, 14398537423249980⟩, ⟨.hall 6 19, 13370703367190289120⟩, ⟨.hall 5 20, 47857995816326124000⟩, ⟨.hall 4 21, 112408072705365025680⟩, ⟨.hall 3 22, 217968815653355566800⟩, ⟨.hall 2 23, 331262350984237873200⟩, ⟨.assumptionRow 15, 32921418209387400⟩]
  caps := #[0, 0, 0, 703429755804829620, 0, 0, 152677110344514600, 22339967443099410, 6310706172402240, 28260557060667344, 0, 0, 32921418209387400, 157433444215374600, 32921418209387400, 428680070985612600, 46160148919500000, 0, 0] }

theorem case_44_26_15_checked :
    (Witness.linear .conditional case_44_26_15).check 44 26 15 = true := by
  change case_44_26_15.check 44 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_26_16 : Certificate := {
  objectiveScale := 362946651076566414000000
  eta := 267103393095745431391961995200
  rows := #[⟨.count 2, 51019077992343233819891644800⟩, ⟨.count 3, 10439793769510515351318577200⟩, ⟨.count 4, 1995359724759091346117542080⟩, ⟨.count 5, 401120218407516224411995200⟩, ⟨.count 6, 73856014027570499584860000⟩, ⟨.count 7, 11488713293177633268756000⟩, ⟨.count 8, 1253314177437559992955200⟩, ⟨.path 8, 1236134019796906402972800⟩, ⟨.path 9, 12653362195919100976320⟩, ⟨.privateRow 2 24, 2090945819358329254913592000⟩, ⟨.privateRow 3 21, 37338318202827308123457000⟩, ⟨.privateRow 4 19, 139271926896545859300494610⟩, ⟨.privateRow 4 20, 464488678443171713055805080⟩, ⟨.privateRow 5 17, 79114562226333519155302032⟩, ⟨.privateRow 5 18, 170689454641496265707232000⟩, ⟨.privateRow 5 19, 374663352938084303227374240⟩, ⟨.privateRow 6 14, 4337575427016045213714000⟩, ⟨.privateRow 6 15, 28174701647554672063854000⟩, ⟨.privateRow 6 16, 66306288149196626293963200⟩, ⟨.privateRow 6 17, 140367457771288155044336700⟩, ⟨.privateRow 6 18, 220473878911932676538508000⟩, ⟨.privateRow 7 12, 2759342746307842276156575⟩, ⟨.privateRow 7 13, 10210887018732365894986200⟩, ⟨.privateRow 7 14, 24522932065080352917713700⟩, ⟨.privateRow 7 15, 55720259471911521353466600⟩, ⟨.privateRow 7 16, 89919697078567083244567050⟩, ⟨.privateRow 7 17, 116801918480639271565686000⟩, ⟨.privateRow 8 10, 1137266568415563697311200⟩, ⟨.privateRow 8 11, 3936189838514836852874925⟩, ⟨.privateRow 8 12, 9392396127344571613872600⟩, ⟨.privateRow 8 13, 22481323057786232373633900⟩, ⟨.privateRow 8 14, 39479396589283139778088800⟩, ⟨.privateRow 8 15, 54166672106129545945532550⟩, ⟨.privateRow 8 16, 55685445189204922464773400⟩, ⟨.privateRow 9 8, 363461111456892397957008⟩, ⟨.privateRow 9 9, 1527186534729471250675040⟩, ⟨.privateRow 9 10, 3859163238026486811641220⟩, ⟨.privateRow 9 11, 9602773864271590612690080⟩, ⟨.privateRow 9 12, 18284461277505736341668640⟩, ⟨.privateRow 9 13, 27539490192227984911868928⟩, ⟨.privateRow 9 14, 14862217287447065583127080⟩, ⟨.privateRow 10 6, 91150121995458908578560⟩, ⟨.privateRow 10 7, 555635951997318263543472⟩, ⟨.privateRow 10 8, 1661801761194986953622080⟩, ⟨.privateRow 10 9, 4470153899527297308206880⟩, ⟨.privateRow 10 10, 9161129820793593281839200⟩, ⟨.privateRow 10 11, 13737715956023921478336720⟩, ⟨.privateRow 11 4, 17407141353299444346600⟩, ⟨.privateRow 11 5, 170906478741485453584800⟩, ⟨.privateRow 11 6, 704989224808627496037300⟩, ⟨.privateRow 11 7, 2245521234575628320711400⟩, ⟨.privateRow 11 8, 5104644201855062054640450⟩, ⟨.privateRow 11 9, 3110904833282514982513800⟩, ⟨.privateRow 12 2, 6312479831416282015800⟩, ⟨.privateRow 12 3, 34192599086838194252250⟩, ⟨.privateRow 12 4, 253646916862363331907600⟩, ⟨.privateRow 12 5, 1140665105536922160255060⟩, ⟨.privateRow 12 6, 2580401477753389059569800⟩, ⟨.privateRow 13 1, 12624959662832564031600⟩, ⟨.privateRow 13 2, 41031118904205833102700⟩, ⟨.privateRow 13 3, 522214240598983330398000⟩, ⟨.privateRow 13 4, 754972587837387329089680⟩, ⟨.privateRow 14 0, 32824895123364666482160⟩, ⟨.privateRow 14 1, 106680909150935166067020⟩, ⟨.privateRow 14 2, 271551405111471331806960⟩, ⟨.privateRow 15 0, 124461060676091027078190⟩, ⟨.hall 7 18, 2207042290531492706892600⟩, ⟨.hall 6 19, 191730212415573016922296560⟩, ⟨.hall 5 20, 579328137122506968489664800⟩, ⟨.hall 4 21, 1287153660228374112764990400⟩, ⟨.hall 3 22, 2439003881214249901073121600⟩, ⟨.hall 2 23, 3629284529314814349600020400⟩, ⟨.assumptionRow 16, 57525648246977789825100⟩]
  caps := #[0, 23762577114587970767797920, 38143684512158612573835000, 0, 3721558108016497987708470, 0, 0, 189272458946867897747520, 128919025977757906676940, 110888874208885797308936, 726632729465944287007008, 9373076113315085417400, 0, 1821147817132474222653360, 0, 0, 3208994211442119936174900, 362946651076566414000000, 0] }

theorem case_44_26_16_checked :
    (Witness.linear .conditional case_44_26_16).check 44 26 16 = true := by
  change case_44_26_16.check 44 26 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_27_1_checked :
    (Witness.rising).check 44 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_27_2_checked :
    (Witness.rising).check 44 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_27_3_checked :
    (Witness.rising).check 44 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_27_4_checked :
    (Witness.rising).check 44 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_27_5_checked :
    (Witness.rising).check 44 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_27_6_checked :
    (Witness.rising).check 44 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_27_7_checked :
    (Witness.rising).check 44 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_27_8_checked :
    (Witness.rising).check 44 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_27_9_checked :
    (Witness.linear .positive case_44_27_9).check 44 27 9 = true := by
  change case_44_27_9.check 44 27 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_27_10_checked :
    (Witness.linear .positive case_44_27_10).check 44 27 10 = true := by
  change case_44_27_10.check 44 27 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_27_11_checked :
    (Witness.linear .positive case_44_27_11).check 44 27 11 = true := by
  change case_44_27_11.check 44 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_27_12 : Certificate := {
  objectiveScale := 1
  eta := 41990
  rows := #[⟨.assumptionRow 12, 4⟩]
  caps := #[0, 0, 12376, 3718, 1144, 363, 120, 42, 16, 7, 68, 44, 10, 1, 0, 0, 0, 0] }

theorem case_44_27_12_checked :
    (Witness.linear .conditional case_44_27_12).check 44 27 12 = true := by
  change case_44_27_12.check 44 27 12 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_27_13 : Certificate := {
  objectiveScale := 53392200000
  eta := 55393277849189280
  rows := #[⟨.count 2, 11745695041320240⟩, ⟨.count 3, 2341888579226196⟩, ⟨.count 4, 507530032649640⟩, ⟨.count 5, 105171058571040⟩, ⟨.count 6, 23105762867880⟩, ⟨.count 7, 5323741601220⟩, ⟨.count 8, 1216855223136⟩, ⟨.count 9, 405618407712⟩, ⟨.path 8, 97012592768⟩, ⟨.path 9, 44764380297⟩]
  caps := #[0, 0, 0, 721015698312, 361923416036, 73050243805, 193002320148, 0, 0, 0, 106784400000, 53392200000, 53392200000, 0, 0, 0, 0, 0] }

theorem case_44_27_13_checked :
    (Witness.linear .positive case_44_27_13).check 44 27 13 = true := by
  change case_44_27_13.check 44 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_27_14 : Certificate := {
  objectiveScale := 48841650000
  eta := 39875298330067200
  rows := #[⟨.count 2, 7999177790003400⟩, ⟨.count 3, 1615914307327320⟩, ⟨.count 4, 360623377754640⟩, ⟨.count 5, 77743403337600⟩, ⟨.count 6, 18552403069200⟩, ⟨.count 7, 4497552259200⟩, ⟨.count 8, 1124388064800⟩, ⟨.count 9, 224877612960⟩, ⟨.path 9, 70540740270⟩, ⟨.privateRow 2 25, 442165606482600⟩, ⟨.privateRow 3 22, 57168886494720⟩, ⟨.privateRow 3 23, 218403011686860⟩, ⟨.privateRow 4 20, 50963892954975⟩, ⟨.privateRow 4 21, 87093225519300⟩, ⟨.privateRow 4 22, 144421623416070⟩, ⟨.privateRow 5 17, 5359583108880⟩, ⟨.privateRow 5 18, 20920043079936⟩, ⟨.privateRow 5 19, 35956324043640⟩, ⟨.privateRow 5 20, 59014310715360⟩, ⟨.privateRow 5 21, 61046240575320⟩, ⟨.privateRow 6 15, 4038618355200⟩, ⟨.privateRow 6 16, 8613615710700⟩, ⟨.privateRow 6 17, 14532715737540⟩, ⟨.privateRow 6 18, 24018736116375⟩, ⟨.privateRow 6 19, 26454352524600⟩, ⟨.privateRow 6 20, 18331541127900⟩, ⟨.privateRow 7 12, 232016584800⟩, ⟨.privateRow 7 13, 1907444038500⟩, ⟨.privateRow 7 14, 3958304922000⟩, ⟨.privateRow 7 15, 6177441570300⟩, ⟨.privateRow 7 16, 10239962733000⟩, ⟨.privateRow 7 17, 11715722068050⟩, ⟨.privateRow 7 18, 2958211456200⟩, ⟨.privateRow 8 10, 205200821826⟩, ⟨.privateRow 8 11, 880770650760⟩, ⟨.privateRow 8 12, 1883350008540⟩, ⟨.privateRow 8 13, 2971597028400⟩, ⟨.privateRow 8 14, 4769279374860⟩, ⟨.privateRow 8 15, 2513007324828⟩, ⟨.privateRow 9 8, 127203498240⟩, ⟨.privateRow 9 9, 449755225920⟩, ⟨.privateRow 9 10, 957812055200⟩, ⟨.privateRow 9 11, 1580389891080⟩, ⟨.privateRow 9 12, 1295723388960⟩, ⟨.privateRow 10 6, 67931778915⟩, ⟨.privateRow 10 7, 255542742000⟩, ⟨.privateRow 10 8, 553761121914⟩, ⟨.privateRow 10 9, 474741627360⟩, ⟨.privateRow 11 4, 33978760200⟩, ⟨.privateRow 11 5, 160626866400⟩, ⟨.privateRow 11 6, 182530530000⟩, ⟨.privateRow 12 2, 15775852950⟩, ⟨.privateRow 12 3, 73620647100⟩, ⟨.privateRow 13 1, 25241364720⟩, ⟨.hall 5 21, 5983350773400⟩, ⟨.hall 4 22, 46338755823360⟩, ⟨.hall 3 23, 127960046724510⟩, ⟨.hall 2 24, 262083614024232⟩, ⟨.assumptionRow 14, 55354106808⟩]
  caps := #[0, 135341042458050, 21805097113800, 0, 535222104417, 183155366394, 457670865795, 0, 281111981436, 99641838582, 330018080301, 55354106808, 727800675030, 4871377368, 530745693192, 48841650000, 0, 0] }

theorem case_44_27_14_checked :
    (Witness.linear .conditional case_44_27_14).check 44 27 14 = true := by
  change case_44_27_14.check 44 27 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_27_15 : Certificate := {
  objectiveScale := 1554033373200000
  eta := 1119756260605862880000
  rows := #[⟨.count 2, 226750642772687233200⟩, ⟨.count 3, 44603624380800204720⟩, ⟨.count 4, 9277980445020006720⟩, ⟨.count 5, 1866260434343104800⟩, ⟨.count 6, 379404593795026800⟩, ⟨.count 7, 78304633608801600⟩, ⟨.count 8, 20881235629013760⟩, ⟨.count 9, 10440617814506880⟩, ⟨.count 10, 6525386134066800⟩, ⟨.path 8, 4261817397277440⟩, ⟨.privateRow 2 25, 25194515863631914800⟩, ⟨.privateRow 3 22, 3131170284286764720⟩, ⟨.privateRow 3 23, 8149337229964890960⟩, ⟨.privateRow 4 19, 130638230404017336⟩, ⟨.privateRow 4 20, 1792943060136768540⟩, ⟨.privateRow 4 21, 3225964465078795440⟩, ⟨.privateRow 4 22, 5572120439681555760⟩, ⟨.privateRow 5 17, 179106312746481120⟩, ⟨.privateRow 5 18, 684979104473183520⟩, ⟨.privateRow 5 19, 1270492680302805960⟩, ⟨.privateRow 5 20, 2288732576622972480⟩, ⟨.privateRow 5 21, 2614815443722482000⟩, ⟨.privateRow 6 15, 104250811808543400⟩, ⟨.privateRow 6 16, 266893471761216300⟩, ⟨.privateRow 6 17, 498353061038873040⟩, ⟨.privateRow 6 18, 919030722131872350⟩, ⟨.privateRow 6 19, 1167836962882590000⟩, ⟨.privateRow 6 20, 998927860690059300⟩, ⟨.privateRow 7 12, 725042903785200⟩, ⟨.privateRow 7 13, 45677702938467600⟩, ⟨.privateRow 7 14, 112929131463033600⟩, ⟨.privateRow 7 15, 205549663223104200⟩, ⟨.privateRow 7 16, 387048617552076480⟩, ⟨.privateRow 7 17, 518069049143946300⟩, ⟨.privateRow 7 18, 510844514495515200⟩, ⟨.privateRow 7 19, 16779564344743200⟩, ⟨.privateRow 8 10, 326269306703340⟩, ⟨.privateRow 8 11, 18126072594630000⟩, ⟨.privateRow 8 12, 50082338578962690⟩, ⟨.privateRow 8 13, 93313021717155240⟩, ⟨.privateRow 8 14, 112889180119355640⟩, ⟨.privateRow 8 15, 377950364885149056⟩, ⟨.privateRow 8 16, 46819645511929290⟩, ⟨.privateRow 9 9, 6786401579429472⟩, ⟨.privateRow 9 10, 22879131630555200⟩, ⟨.privateRow 9 11, 46402745842252800⟩, ⟨.privateRow 9 12, 90733940530833600⟩, ⟨.privateRow 9 13, 93385526007533760⟩, ⟨.privateRow 10 7, 2254224300859440⟩, ⟨.privateRow 10 8, 10701633259869552⟩, ⟨.privateRow 10 9, 24941475890210880⟩, ⟨.privateRow 10 10, 52937195012616915⟩, ⟨.privateRow 10 11, 559318811491440⟩, ⟨.privateRow 11 5, 621465346101600⟩, ⟨.privateRow 11 6, 4915225919167200⟩, ⟨.privateRow 11 7, 14169409891116480⟩, ⟨.privateRow 11 8, 10875643556778000⟩, ⟨.privateRow 12 4, 2136287127224250⟩, ⟨.privateRow 12 5, 6836118807117600⟩, ⟨.privateRow 13 2, 631026351426240⟩, ⟨.privateRow 13 3, 1709029701779400⟩, ⟨.hall 5 21, 553725623376525600⟩, ⟨.hall 4 22, 2234875849325159040⟩, ⟨.hall 3 23, 5404379174451907650⟩, ⟨.hall 2 24, 10637684475755697360⟩, ⟨.assumptionRow 15, 1238347350917820⟩]
  caps := #[0, 5070102467468266800, 49488555574347120, 27836277929127360, 35864788470779268, 36603502338803400, 3099736454884740, 9204501888204480, 378250855900632, 4574590664019376, 0, 1238347350917820, 13010728158177750, 607320999491580, 86152001046986160, 15856019754282180, 1554033373200000, 0] }

theorem case_44_27_15_checked :
    (Witness.linear .conditional case_44_27_15).check 44 27 15 = true := by
  change case_44_27_15.check 44 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_27_16 : Certificate := {
  objectiveScale := 455671954460408400000
  eta := 414021904694442286136294400
  rows := #[⟨.count 2, 80614842019831310521730400⟩, ⟨.count 3, 15127723440758468147287680⟩, ⟨.count 4, 2919385225409528940704640⟩, ⟨.count 5, 524964376197517691635200⟩, ⟨.count 6, 94785234591218472100800⟩, ⟨.count 7, 15079469139512029652400⟩, ⟨.count 8, 1855934663324557495680⟩, ⟨.path 7, 1061393207022769420800⟩, ⟨.path 8, 1228130712921504712320⟩, ⟨.privateRow 2 25, 9123078829404777939702000⟩, ⟨.privateRow 3 22, 1094769459528573352764240⟩, ⟨.privateRow 3 23, 2919385225409528940704640⟩, ⟨.privateRow 4 19, 49288321987433605492416⟩, ⟨.privateRow 4 20, 604255870519017759642600⟩, ⟨.privateRow 4 21, 1134263307274914382806240⟩, ⟨.privateRow 4 22, 2048545882602709228278540⟩, ⟨.privateRow 5 17, 60152168105965568833200⟩, ⟨.privateRow 5 18, 222818213008279731338496⟩, ⟨.privateRow 5 19, 434189286146696924123280⟩, ⟨.privateRow 5 20, 832894869087450522793440⟩, ⟨.privateRow 5 21, 1022951416395996279672480⟩, ⟨.privateRow 6 15, 32897073177721429419600⟩, ⟨.privateRow 6 16, 83494044786815844281100⟩, ⟨.privateRow 6 17, 164841244516651099236840⟩, ⟨.privateRow 6 18, 327495137465812541425200⟩, ⟨.privateRow 6 19, 457115971094829255409200⟩, ⟨.privateRow 6 20, 441875396515792524585300⟩, ⟨.privateRow 7 12, 865366360875537721200⟩, ⟨.privateRow 7 13, 12842405036397607671000⟩, ⟨.privateRow 7 14, 33780851588828361560400⟩, ⟨.privateRow 7 15, 65344366271218795160400⟩, ⟨.privateRow 7 16, 134024996044366259152320⟩, ⟨.privateRow 7 17, 199471549194369293341500⟩, ⟨.privateRow 7 18, 226578690147539727597600⟩, ⟨.privateRow 7 19, 119724356629642213449000⟩, ⟨.privateRow 8 10, 498782440768474826964⟩, ⟨.privateRow 8 11, 4768721009931154676400⟩, ⟨.privateRow 8 12, 13876011506262511901295⟩, ⟨.privateRow 8 13, 28253291080074736876200⟩, ⟨.privateRow 8 14, 58751931685868023222620⟩, ⟨.privateRow 8 15, 93585505398140811719664⟩, ⟨.privateRow 8 16, 113878990982430270086490⟩, ⟨.privateRow 9 8, 159347925638977158720⟩, ⟨.privateRow 9 9, 1783759426417491370848⟩, ⟨.privateRow 9 10, 5865670047050453319680⟩, ⟨.privateRow 9 11, 13043096383919806844640⟩, ⟨.privateRow 9 12, 23361209333593239588480⟩, ⟨.privateRow 9 13, 58857187239690827988000⟩, ⟨.privateRow 9 14, 24250879600774217943552⟩, ⟨.privateRow 10 6, 9666326371482070290⟩, ⟨.privateRow 10 7, 643250082174988677480⟩, ⟨.privateRow 10 8, 2586708937008602009604⟩, ⟨.privateRow 10 9, 6431329145826070766280⟩, ⟨.privateRow 10 10, 15441956378442607288275⟩, ⟨.privateRow 10 11, 23696308647804618025200⟩, ⟨.privateRow 11 5, 179517489756095591100⟩, ⟨.privateRow 11 6, 1159959164577848434800⟩, ⟨.privateRow 11 7, 3430164958108780371480⟩, ⟨.privateRow 11 8, 9187613065465815380400⟩, ⟨.privateRow 11 9, 4121997745553425687950⟩, ⟨.privateRow 12 3, 23369140678308301800⟩, ⟨.privateRow 12 4, 455698243227011885100⟩, ⟨.privateRow 12 5, 1905647198949322428600⟩, ⟨.privateRow 12 6, 3827865243106899834840⟩, ⟨.privateRow 13 2, 112171875255879848640⟩, ⟨.privateRow 13 3, 972156252217625354880⟩, ⟨.privateRow 13 4, 861683950829258837280⟩, ⟨.privateRow 14 1, 182279297290804754040⟩, ⟨.privateRow 14 2, 197469238731705150210⟩, ⟨.hall 5 21, 296783837679846649532400⟩, ⟨.hall 4 22, 941258590462360827296640⟩, ⟨.hall 3 23, 2098308130763098926131460⟩, ⟨.hall 2 24, 3961074953567019949092432⟩, ⟨.assumptionRow 16, 163455069702479856840⟩]
  caps := #[0, 98011265263666870167360, 10093633455173175174960, 40362246497222274209904, 1574420852845647686880, 0, 69725166911989463160, 0, 773650123761814392951, 163455069702479856840, 988334387912345125041, 0, 0, 0, 22742253751543454790090, 22808279774134775174760, 4393264474901604143160, 455671954460408400000] }

theorem case_44_27_16_checked :
    (Witness.linear .conditional case_44_27_16).check 44 27 16 = true := by
  change case_44_27_16.check 44 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_27_17 : Certificate := {
  objectiveScale := 2351453355108000000
  eta := 3244262348811629149804800
  rows := #[⟨.count 2, 549225515743700997801600⟩, ⟨.count 3, 94517879453567148458880⟩, ⟨.count 4, 18429161823958073348160⟩, ⟨.count 5, 3473889985856529439200⟩, ⟨.count 6, 596526563227888893600⟩, ⟨.count 7, 89319485403106358400⟩, ⟨.count 8, 8931948540310635840⟩, ⟨.path 3, 3299548447918609286400⟩, ⟨.path 8, 9404373189185694720⟩, ⟨.privateRow 7 12, 1240548408376477200⟩, ⟨.privateRow 7 13, 32099190066741347550⟩, ⟨.privateRow 8 15, 197396062740865052064⟩, ⟨.privateRow 8 17, 886123728103317663960⟩, ⟨.privateRow 9 10, 11137367932979928640⟩, ⟨.privateRow 9 11, 15879019627218908160⟩, ⟨.privateRow 9 14, 124451816328328192704⟩, ⟨.privateRow 9 15, 642107856175664598720⟩, ⟨.privateRow 10 7, 304498245692408040⟩, ⟨.privateRow 10 8, 3126181989108722544⟩, ⟨.privateRow 10 12, 254932697921366064600⟩, ⟨.privateRow 10 15, 580576655120191329600⟩, ⟨.privateRow 11 6, 869994987692594400⟩, ⟨.privateRow 12 5, 797495405384878200⟩, ⟨.privateRow 14 8, 3801394765667919420⟩, ⟨.hall 11 5, 199495569204184275⟩, ⟨.hall 12 5, 112175177900290560⟩, ⟨.hall 10 6, 39307708248608250⟩, ⟨.hall 13 6, 37975971684994200⟩, ⟨.hall 10 7, 77912447050147500⟩, ⟨.hall 14 7, 62027420418823860⟩, ⟨.hall 8 10, 34217209124935200⟩, ⟨.hall 7 12, 93329183664236520⟩, ⟨.hall 6 15, 824101120325693925⟩, ⟨.hall 5 17, 3743231566929323040⟩, ⟨.hall 4 18, 4183036769810074176⟩]
  caps := #[0, 5725862565496062612480, 0, 0, 0, 0, 0, 2372793133642588800, 10818598374734878728, 84532610431264320, 2835863862221563056, 326978427532511250, 0, 0, 145856877534714291660, 79374954019019115600, 103463947624752000000, 21163080195972000000] }

theorem case_44_27_17_checked :
    (Witness.linear .negative case_44_27_17).check 44 27 17 = true := by
  change case_44_27_17.check 44 27 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_28_1_checked :
    (Witness.rising).check 44 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_28_2_checked :
    (Witness.rising).check 44 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_28_3_checked :
    (Witness.rising).check 44 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_28_4_checked :
    (Witness.rising).check 44 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_28_5_checked :
    (Witness.rising).check 44 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_28_6_checked :
    (Witness.rising).check 44 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_28_7_checked :
    (Witness.rising).check 44 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_28_8_checked :
    (Witness.rising).check 44 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_28_9_checked :
    (Witness.linear .positive case_44_28_9).check 44 28 9 = true := by
  change case_44_28_9.check 44 28 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_28_10_checked :
    (Witness.linear .positive case_44_28_10).check 44 28 10 = true := by
  change case_44_28_10.check 44 28 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_44_28_11_checked :
    (Witness.linear .positive case_44_28_11).check 44 28 11 = true := by
  change case_44_28_11.check 44 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_44_28_12_checked :
    (Witness.linear .positive case_44_28_12).check 44 28 12 = true := by
  change case_44_28_12.check 44 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_28_13 : Certificate := {
  objectiveScale := 45513282791950000
  eta := 216273573169085827845450
  rows := #[⟨.count 2, 25749755002666744573524⟩, ⟨.count 3, 3524780568751700614785⟩, ⟨.count 4, 581103425199710566692⟩, ⟨.count 5, 104884258772605209810⟩, ⟨.count 6, 20692832485117468860⟩, ⟨.count 7, 3834260136948236877⟩, ⟨.count 8, 757384718409528272⟩, ⟨.count 9, 426028904105359653⟩, ⟨.path 3, 412880376738285413100⟩, ⟨.path 7, 223313010824019480⟩, ⟨.path 8, 180261301484058704⟩]
  caps := #[0, 0, 0, 381465864213125731, 0, 582499539163545910, 0, 103223765978269643, 60062542161830432, 0, 91026565583900000, 45513282791950000, 45513282791950000, 0, 0, 0, 0] }

theorem case_44_28_13_checked :
    (Witness.linear .positive case_44_28_13).check 44 28 13 = true := by
  change case_44_28_13.check 44 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_28_14 : Certificate := {
  objectiveScale := 1419801350467500000
  eta := 2571990171818043783807000
  rows := #[⟨.count 2, 422330077474227222300000⟩, ⟨.count 3, 76019413945360900014000⟩, ⟨.count 4, 14479888370544933336000⟩, ⟨.count 5, 2738184018788945727000⟩, ⟨.count 6, 556918783482497436000⟩, ⟨.count 7, 106320858664840419600⟩, ⟨.count 8, 31502476641434198400⟩, ⟨.path 3, 1111936820263689420000⟩, ⟨.path 8, 6863891406487315200⟩, ⟨.privateRow 2 26, 38009706972680450007000⟩, ⟨.privateRow 3 23, 8285713900922934075600⟩, ⟨.privateRow 3 24, 12730235192437420557900⟩, ⟨.privateRow 4 20, 1436850461384843384880⟩, ⟨.privateRow 4 21, 3606049123049170898100⟩, ⟨.privateRow 4 22, 5151498747213101283000⟩, ⟨.privateRow 4 23, 7351327941968966155200⟩, ⟨.privateRow 5 17, 186965591597695567800⟩, ⟨.privateRow 5 18, 840019165086100299300⟩, ⟨.privateRow 5 19, 1421999293825310119920⟩, ⟨.privateRow 5 20, 2028112569848761496100⟩, ⟨.privateRow 5 21, 2967139518665083561800⟩, ⟨.privateRow 5 22, 2478288586497113590200⟩, ⟨.privateRow 6 14, 7031802821748705000⟩, ⟨.privateRow 6 15, 162962030394026238375⟩, ⟨.privateRow 6 16, 377909174505980403000⟩, ⟨.privateRow 6 17, 609657304645612723500⟩, ⟨.privateRow 6 18, 825252379160428018800⟩, ⟨.privateRow 6 19, 1202438282519028555000⟩, ⟨.privateRow 6 20, 1005547803510064815000⟩, ⟨.privateRow 7 12, 14682404291811296040⟩, ⟨.privateRow 7 13, 89725804005513475800⟩, ⟨.privateRow 7 14, 179100017869939516350⟩, ⟨.privateRow 7 15, 280267569609698385000⟩, ⟨.privateRow 7 16, 375076362512075924700⟩, ⟨.privateRow 7 17, 533629452536865725040⟩, ⟨.privateRow 7 18, 12657245079147669000⟩, ⟨.privateRow 8 10, 12171411429645031200⟩, ⟨.privateRow 8 11, 47647495920169225080⟩, ⟨.privateRow 8 12, 94288662725403746600⟩, ⟨.privateRow 8 13, 145206728269110758250⟩, ⟨.privateRow 8 14, 194359029993134206200⟩, ⟨.privateRow 8 15, 7547468362010276700⟩, ⟨.privateRow 9 8, 8203769958706822500⟩, ⟨.privateRow 9 9, 27743658405808527000⟩, ⟨.privateRow 9 10, 56113786517554665900⟩, ⟨.privateRow 9 11, 67599064459744217400⟩, ⟨.privateRow 10 6, 5257624879030570200⟩, ⟨.privateRow 10 7, 18774913534069042350⟩, ⟨.privateRow 10 8, 23243304599889355800⟩, ⟨.privateRow 11 4, 3616355736899334000⟩, ⟨.privateRow 11 5, 9087252877336788000⟩, ⟨.privateRow 12 2, 3093993241569430200⟩, ⟨.hall 4 23, 997812820406141239500⟩, ⟨.hall 3 24, 4691483832056558400864⟩, ⟨.hall 2 25, 12474980750007942566400⟩, ⟨.assumptionRow 14, 1673093911390902000⟩]
  caps := #[0, 9197462007364524894000, 849399362899160673600, 0, 33818155113704530140, 29398769785261485180, 2965279990121323875, 20783632474380641580, 0, 7958838450180618000, 10660930312431801150, 6188842316509677000, 0, 104358806782602372000, 16784323644686598000, 1419801350467500000, 0] }

theorem case_44_28_14_checked :
    (Witness.linear .conditional case_44_28_14).check 44 28 14 = true := by
  change case_44_28_14.check 44 28 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_28_15 : Certificate := {
  objectiveScale := 672150859614000000
  eta := 1455838955133565080078000
  rows := #[⟨.count 2, 230256827846412132205440⟩, ⟨.count 3, 37292426436918908455200⟩, ⟨.count 4, 6002094669137244437760⟩, ⟨.count 5, 919438521620288670000⟩, ⟨.count 6, 140423337847462269600⟩, ⟨.count 7, 28084667569492453920⟩, ⟨.count 8, 12482074475329979520⟩, ⟨.count 9, 7021166892373113480⟩, ⟨.path 6, 14111219917479484800⟩, ⟨.path 7, 6040201440224952000⟩, ⟨.privateRow 2 26, 21753915421536029932200⟩, ⟨.privateRow 3 23, 4382656953056709327000⟩, ⟨.privateRow 3 24, 7147715067076124120580⟩, ⟨.privateRow 4 20, 679648955181717384864⟩, ⟨.privateRow 4 21, 1850829744021641092710⟩, ⟨.privateRow 4 22, 2861292679282338341040⟩, ⟨.privateRow 4 23, 4402271641517942151960⟩, ⟨.privateRow 5 17, 70402721084067818160⟩, ⟨.privateRow 5 18, 375743875835491303140⟩, ⟨.privateRow 5 19, 709806538690862853240⟩, ⟨.privateRow 5 20, 1117117803768650734050⟩, ⟨.privateRow 5 21, 1810680928577555154120⟩, ⟨.privateRow 5 22, 1761644207424473091720⟩, ⟨.privateRow 6 15, 56002164498690309900⟩, ⟨.privateRow 6 16, 161677890684918293400⟩, ⟨.privateRow 6 17, 295892033321438353800⟩, ⟨.privateRow 6 18, 451695070076003633880⟩, ⟨.privateRow 6 19, 743073496109487843300⟩, ⟨.privateRow 6 20, 807434192622908050200⟩, ⟨.privateRow 6 21, 422941719945332788200⟩, ⟨.privateRow 7 12, 501511920883793820⟩, ⟨.privateRow 7 13, 29087691411260041560⟩, ⟨.privateRow 7 14, 72343094587487258535⟩, ⟨.privateRow 7 15, 131969279752564030920⟩, ⟨.privateRow 7 16, 201942133475874311520⟩, ⟨.privateRow 7 17, 330596658246596886144⟩, ⟨.privateRow 7 18, 343034153884514972880⟩, ⟨.privateRow 8 11, 13730281922862977472⟩, ⟨.privateRow 8 12, 35625920898337649880⟩, ⟨.privateRow 8 13, 65238342374966846085⟩, ⟨.privateRow 8 14, 101193960924996619680⟩, ⟨.privateRow 8 15, 167727875762246599800⟩, ⟨.privateRow 8 16, 30893134326441699312⟩, ⟨.privateRow 9 9, 6099195482263512720⟩, ⟨.privateRow 9 10, 19347215436761468256⟩, ⟨.privateRow 9 11, 37012818062263203160⟩, ⟨.privateRow 9 12, 58607240309947794465⟩, ⟨.privateRow 9 13, 27081643727724866280⟩, ⟨.privateRow 10 7, 2758315564860866010⟩, ⟨.privateRow 10 8, 11215630230673934520⟩, ⟨.privateRow 10 9, 24373479354952379652⟩, ⟨.privateRow 10 10, 11479050633562391880⟩, ⟨.privateRow 11 5, 1414520802492751800⟩, ⟨.privateRow 11 6, 7104752212520412450⟩, ⟨.privateRow 11 7, 7294718849218819200⟩, ⟨.privateRow 12 3, 788090161388818860⟩, ⟨.privateRow 12 4, 3677754086481154680⟩, ⟨.privateRow 13 1, 735550817296230936⟩, ⟨.privateRow 13 2, 788090161388818860⟩, ⟨.hall 4 23, 928632906836491556700⟩, ⟨.hall 3 24, 3126826524326277708936⟩, ⟨.hall 2 25, 7440096516951375917640⟩, ⟨.assumptionRow 15, 585119743472914650⟩]
  caps := #[0, 1443462516058329000, 47635163219425036320, 69063586746070666932, 3366382202210583738, 19737688405099445820, 4223150259659609850, 0, 0, 0, 12565267980232707558, 780096770270582850, 20718996183293276700, 0, 44149059525130109550, 7480690571895085350, 672150859614000000] }

theorem case_44_28_15_checked :
    (Witness.linear .conditional case_44_28_15).check 44 28 15 = true := by
  change case_44_28_15.check 44 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_28_16 : Certificate := {
  objectiveScale := 5971801868109000000
  eta := 15537315745304772147729000
  rows := #[⟨.count 2, 2349422865525891232677600⟩, ⟨.count 3, 354995213197593455487000⟩, ⟨.count 4, 51194336883817673145600⟩, ⟨.count 5, 6528013503504049557000⟩, ⟨.count 6, 752267881325690730000⟩, ⟨.count 7, 70211668923731134800⟩, ⟨.path 6, 274152891887915040000⟩, ⟨.path 7, 26935084329375222000⟩, ⟨.privateRow 2 26, 230926179090151702357200⟩, ⟨.privateRow 3 23, 43746884858693334918600⟩, ⟨.privateRow 3 24, 74584852873837816910400⟩, ⟨.privateRow 4 20, 6333092536920548358960⟩, ⟨.privateRow 4 21, 18011800638541455045300⟩, ⟨.privateRow 4 22, 29495587773578860533600⟩, ⟨.privateRow 4 23, 48077440295524894554300⟩, ⟨.privateRow 5 17, 640979997929572672800⟩, ⟨.privateRow 5 18, 3313043472905106840900⟩, ⟨.privateRow 5 19, 6704545699655144981640⟩, ⟨.privateRow 5 20, 11295302238105246310950⟩, ⟨.privateRow 5 21, 19804705755701017951800⟩, ⟨.privateRow 5 22, 21358556857239305804100⟩, ⟨.privateRow 6 14, 17645789808874227000⟩, ⟨.privateRow 6 15, 447181462788049489500⟩, ⟨.privateRow 6 16, 1361246642398868940000⟩, ⟨.privateRow 6 17, 2688661131404783535000⟩, ⟨.privateRow 6 18, 4465127802268710977400⟩, ⟨.privateRow 6 19, 8051355963188573285250⟩, ⟨.privateRow 6 20, 9916005146807901141000⟩, ⟨.privateRow 6 21, 7752538443661979467500⟩, ⟨.privateRow 7 12, 15045357626513814600⟩, ⟨.privateRow 7 13, 212306713174139383800⟩, ⟨.privateRow 7 14, 576111819115258150725⟩, ⟨.privateRow 7 15, 1147745853222625285200⟩, ⟨.privateRow 7 16, 1929149188999660227600⟩, ⟨.privateRow 7 17, 3109373909479521684000⟩, ⟨.privateRow 7 18, 5460211038622305215250⟩, ⟨.privateRow 7 19, 2067900820444176517800⟩, ⟨.privateRow 8 10, 5319065827555389000⟩, ⟨.privateRow 8 11, 94005623392328908260⟩, ⟨.privateRow 8 12, 264810677237035329400⟩, ⟨.privateRow 8 13, 537314299680220212150⟩, ⟨.privateRow 8 14, 922224698958531969000⟩, ⟨.privateRow 8 15, 1711734484038741462300⟩, ⟨.privateRow 8 16, 2197625237312784519240⟩, ⟨.privateRow 9 8, 325054022795051550⟩, ⟨.privateRow 9 9, 41843317843435726800⟩, ⟨.privateRow 9 10, 133792235782443217980⟩, ⟨.privateRow 9 11, 284313918604738422400⟩, ⟨.privateRow 9 12, 184305630924794228850⟩, ⟨.privateRow 9 13, 1588678318266329089800⟩, ⟨.privateRow 10 7, 17552917230932783700⟩, ⟨.privateRow 10 8, 73859028348340544400⟩, ⟨.privateRow 10 9, 173021612704908867900⟩, ⟨.privateRow 10 10, 320410393897979385000⟩, ⟨.privateRow 10 11, 243233281628640002700⟩, ⟨.privateRow 11 5, 7715568013596828000⟩, ⟨.privateRow 11 6, 43882293077331959250⟩, ⟨.privateRow 11 7, 121578647486980320000⟩, ⟨.privateRow 11 8, 116183595004745568300⟩, ⟨.privateRow 12 3, 3940450806944094300⟩, ⟨.privateRow 12 4, 28290416049855036000⟩, ⟨.privateRow 12 5, 62828298977386392450⟩, ⟨.privateRow 13 1, 3677754086481154680⟩, ⟨.privateRow 13 2, 23642704841664565800⟩, ⟨.privateRow 13 3, 4243562407478255400⟩, ⟨.hall 5 22, 1143301813840880694000⟩, ⟨.hall 4 23, 12954888769629867360300⟩, ⟨.hall 3 24, 36833442726926060351136⟩, ⟨.hall 2 25, 81609363179016822349200⟩, ⟨.assumptionRow 16, 2958472008591021000⟩]
  caps := #[0, 0, 689698336616978176800, 0, 0, 175222738622977318260, 0, 13783965451654091850, 42315118580294097850, 10806645907739106900, 4258618586733609000, 78655416741482017500, 176873522716406565450, 0, 1402499565332248383000, 352665457323992748000, 62731348540607979000] }

theorem case_44_28_16_checked :
    (Witness.linear .conditional case_44_28_16).check 44 28 16 = true := by
  change case_44_28_16.check 44 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_28_17 : Certificate := {
  objectiveScale := 90206416227989061000000
  eta := 438529151527761995556244389000
  rows := #[⟨.count 2, 53055258215707542224159730000⟩, ⟨.count 3, 7056610698640904630799570000⟩, ⟨.count 4, 1027732019699495853921578400⟩, ⟨.count 5, 150782279885489415188025000⟩, ⟨.count 6, 19738771185009523442796000⟩, ⟨.count 7, 1535237758834074045550800⟩, ⟨.path 3, 726801465965441675284476000⟩, ⟨.path 7, 1718499478886037315468000⟩, ⟨.path 8, 6184211976656073360000⟩, ⟨.privateRow 4 20, 115559539304239087800102360⟩, ⟨.privateRow 4 21, 302167688890520788036802100⟩, ⟨.privateRow 5 18, 80618258978775007320530700⟩, ⟨.privateRow 5 21, 960047529617565049770509400⟩, ⟨.privateRow 6 15, 5048921796165630417659625⟩, ⟨.privateRow 6 16, 27884930721680120419188000⟩, ⟨.privateRow 6 17, 44077163433192562379206500⟩, ⟨.privateRow 6 18, 2668389437973509650600200⟩, ⟨.privateRow 6 20, 733624329042853954623918000⟩, ⟨.privateRow 7 14, 17189179906945793331434850⟩, ⟨.privateRow 7 16, 51942210840552838541135400⟩, ⟨.privateRow 7 19, 484915812111733959244688400⟩, ⟨.privateRow 8 10, 46522356328305274107600⟩, ⟨.privateRow 8 11, 443513130329843613159120⟩, ⟨.privateRow 8 12, 4871063012597000366747600⟩, ⟨.privateRow 8 13, 10394838992105709683416875⟩, ⟨.privateRow 8 14, 5726680528984244455626000⟩, ⟨.privateRow 8 17, 173311284775046581142179200⟩, ⟨.privateRow 9 8, 35537911084122084387750⟩, ⟨.privateRow 9 9, 240365507696243916222600⟩, ⟨.privateRow 9 11, 8225841818938125132951200⟩, ⟨.privateRow 9 14, 23497666808821522197180300⟩, ⟨.privateRow 10 6, 16870744602572242258800⟩, ⟨.privateRow 10 7, 45691599965299822784250⟩, ⟨.privateRow 10 9, 1568135710809089917955460⟩, ⟨.privateRow 11 7, 249226908901635397005000⟩, ⟨.hall 11 4, 7771411624350154732380⟩, ⟨.hall 12 4, 11267247288146461794270⟩, ⟨.hall 10 5, 7252634915126955997500⟩, ⟨.hall 11 6, 2469177606398878593900⟩, ⟨.hall 13 6, 3133138283334844990920⟩, ⟨.hall 9 7, 5732396966353881077100⟩, ⟨.hall 8 9, 2338951442535836923410⟩, ⟨.hall 10 11, 2653282954244409015375⟩, ⟨.hall 7 15, 6804228973160747603475⟩, ⟨.hall 5 16, 3431358352360778697000⟩, ⟨.hall 4 18, 27471719730689582891400⟩, ⟨.hall 3 21, 1349030582836357393845873⟩]
  caps := #[0, 105848108177606817233211000, 0, 0, 4061487381768947797951284, 906331803087633525603000, 555993938514632704997625, 238919627841867930157200, 32903270648709286418880, 742841738111889575029780, 0, 668415628108052475378000, 3371194187272407187692000, 0, 104098860373762852678080, 18762934575421724688000000, 4871146476311409294000000] }

theorem case_44_28_17_checked :
    (Witness.linear .negative case_44_28_17).check 44 28 17 = true := by
  change case_44_28_17.check 44 28 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_28_18 : Certificate := {
  objectiveScale := 57173217601500000
  eta := 333669157200478438138800
  rows := #[⟨.count 2, 32652639236744067340800⟩, ⟨.count 3, 3308995136937903252840⟩, ⟨.count 4, 399187485174481043040⟩, ⟨.count 5, 61672223833136116200⟩, ⟨.count 6, 7135629203833930800⟩, ⟨.count 7, 713562920383393080⟩, ⟨.path 3, 852733783090250661600⟩, ⟨.path 7, 633139733522696400⟩, ⟨.privateRow 6 15, 955664625513472875⟩, ⟨.privateRow 7 13, 600298964766981480⟩, ⟨.hall 10 5, 79316495529700⟩, ⟨.hall 12 6, 1540265330497905⟩, ⟨.hall 11 8, 2337030034438176⟩, ⟨.hall 10 9, 2082640401502920⟩, ⟨.hall 13 9, 8737505147551752⟩, ⟨.hall 9 10, 1145415438057240⟩, ⟨.hall 12 10, 3500603023858875⟩, ⟨.hall 8 12, 3260261197627280⟩, ⟨.hall 9 12, 2091836093844420⟩, ⟨.hall 7 14, 7498915451569542⟩, ⟨.hall 6 15, 7130799626216175⟩]
  caps := #[0, 0, 20339961245315712000, 1891328655422966760, 245303245736508960, 0, 801843238054833975, 0, 15758463390109440, 0, 62204460750432000, 0, 0, 8777016251419746330, 1178024418605754720, 24527310351043500000, 8804675510631000000] }

theorem case_44_28_18_checked :
    (Witness.linear .negative case_44_28_18).check 44 28 18 = true := by
  change case_44_28_18.check 44 28 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_29_1_checked :
    (Witness.rising).check 44 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_29_2_checked :
    (Witness.rising).check 44 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_29_3_checked :
    (Witness.rising).check 44 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_29_4_checked :
    (Witness.rising).check 44 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_29_5_checked :
    (Witness.rising).check 44 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_29_6_checked :
    (Witness.rising).check 44 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_29_7_checked :
    (Witness.rising).check 44 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_29_8_checked :
    (Witness.rising).check 44 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_29_9_checked :
    (Witness.linear .positive case_44_29_9).check 44 29 9 = true := by
  change case_44_29_9.check 44 29 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_44_29_10_checked :
    (Witness.linear .positive case_44_29_10).check 44 29 10 = true := by
  change case_44_29_10.check 44 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_44_29_11_checked :
    (Witness.linear .positive case_44_29_11).check 44 29 11 = true := by
  change case_44_29_11.check 44 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_44_29_12_checked :
    (Witness.linear .positive case_44_29_12).check 44 29 12 = true := by
  change case_44_29_12.check 44 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_44_29_13_checked :
    (Witness.linear .positive case_44_29_13).check 44 29 13 = true := by
  change case_44_29_13.check 44 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_29_14 : Certificate := {
  objectiveScale := 641761350000
  eta := 6313233883131944769
  rows := #[⟨.count 2, 822095814151390779⟩, ⟨.count 3, 102247106858793666⟩, ⟨.count 4, 12518405658067155⟩, ⟨.count 5, 1578567282395565⟩, ⟨.count 6, 286344762853149⟩, ⟨.count 7, 85658689742395⟩, ⟨.count 8, 34263475896958⟩, ⟨.path 5, 381477601573530⟩, ⟨.path 6, 16570403109645⟩]
  caps := #[0, 3092870029776831, 231937771237326, 0, 3706529732070, 0, 5541259406496, 0, 0, 8984658900000, 3208806750000, 1283522700000, 641761350000, 641761350000, 0, 0] }

theorem case_44_29_14_checked :
    (Witness.linear .positive case_44_29_14).check 44 29 14 = true := by
  change case_44_29_14.check 44 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_29_15 : Certificate := {
  objectiveScale := 13873242814212600000
  eta := 60524865976755951939168000
  rows := #[⟨.count 2, 9121961943639647042260320⟩, ⟨.count 3, 1381762736996818573116720⟩, ⟨.count 4, 204520838328048958475760⟩, ⟨.count 5, 30988005807280145223600⟩, ⟨.count 6, 4534830118138557837600⟩, ⟨.count 7, 705418018377108996960⟩, ⟨.count 8, 352709009188554498480⟩, ⟨.path 6, 535747403047153096800⟩, ⟨.path 7, 183676497362521663500⟩, ⟨.privateRow 2 27, 788984860054140087778440⟩, ⟨.privateRow 3 23, 24110180128103332503240⟩, ⟨.privateRow 3 24, 175145216562773633816640⟩, ⟨.privateRow 3 25, 262717824844160450724960⟩, ⟨.privateRow 4 20, 4156927608293678017800⟩, ⟨.privateRow 4 21, 37994318339804217082692⟩, ⟨.privateRow 4 22, 74928620139493546270845⟩, ⟨.privateRow 4 23, 105863089757879000186640⟩, ⟨.privateRow 4 24, 150896472181060512046140⟩, ⟨.privateRow 5 18, 6931811752011795551760⟩, ⟨.privateRow 5 19, 18517222982399111170200⟩, ⟨.privateRow 5 20, 30020575382077252884912⟩, ⟨.privateRow 5 21, 42325081102626539817600⟩, ⟨.privateRow 5 22, 62631042631624748801520⟩, ⟨.privateRow 5 23, 50638936319213895853200⟩, ⟨.privateRow 6 15, 562654847991265509480⟩, ⟨.privateRow 6 16, 4043556855340214071860⟩, ⟨.privateRow 6 17, 8249071929185376637920⟩, ⟨.privateRow 6 18, 13088023590961004425740⟩, ⟨.privateRow 6 19, 17957927267828689036896⟩, ⟨.privateRow 6 20, 26793287948001979223820⟩, ⟨.privateRow 6 21, 16426162427924109500640⟩, ⟨.privateRow 7 13, 483715212601446169344⟩, ⟨.privateRow 7 14, 2071465609520081975200⟩, ⟨.privateRow 7 15, 4018363354683888750540⟩, ⟨.privateRow 7 16, 6298375164081330330000⟩, ⟨.privateRow 7 17, 8632972891567476772320⟩, ⟨.privateRow 7 18, 10893669683795068938768⟩, ⟨.privateRow 8 11, 312628439962582396380⟩, ⟨.privateRow 8 12, 1128668829403374395136⟩, ⟨.privateRow 8 13, 2228924988622115233450⟩, ⟨.privateRow 8 14, 3505045778811260328645⟩, ⟨.privateRow 8 15, 4402564239692849900670⟩, ⟨.privateRow 9 9, 193150171698494130120⟩, ⟨.privateRow 9 10, 700837381894140756720⟩, ⟨.privateRow 9 11, 1441068237541808379504⟩, ⟨.privateRow 9 12, 1645975376213254326240⟩, ⟨.privateRow 10 7, 133719349637419013160⟩, ⟨.privateRow 10 8, 510168388290587756730⟩, ⟨.privateRow 10 9, 652740698822974234200⟩, ⟨.privateRow 11 5, 107972145669965662800⟩, ⟨.privateRow 11 6, 290694238342215246000⟩, ⟨.privateRow 12 3, 110851402887831413808⟩, ⟨.hall 4 24, 9311517842577838759872⟩, ⟨.hall 3 25, 74632838751980342258040⟩, ⟨.hall 2 26, 221764389888378289512560⟩, ⟨.assumptionRow 15, 13169175741391310550⟩]
  caps := #[0, 49134569983304618882160, 11295421745818958715240, 0, 1673335984989173970582, 0, 258468213201305250000, 547302690168817134552, 0, 292642923829284009072, 720938945924959158810, 37151313281424335682, 0, 4734632561148847702800, 1064223392899655652300, 167182980843372489450] }

theorem case_44_29_15_checked :
    (Witness.linear .conditional case_44_29_15).check 44 29 15 = true := by
  change case_44_29_15.check 44 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_29_16 : Certificate := {
  objectiveScale := 236548026000000
  eta := 1244485229057353483200
  rows := #[⟨.count 2, 176845432097482948800⟩, ⟨.count 3, 24464640473799926400⟩, ⟨.count 4, 3175351565920934400⟩, ⟨.count 5, 377237014546392000⟩, ⟨.count 6, 34443379589018400⟩, ⟨.count 7, 3827042176557600⟩, ⟨.count 8, 3827042176557600⟩, ⟨.path 6, 23305352045976000⟩, ⟨.privateRow 2 27, 15948924910648329600⟩, ⟨.privateRow 3 23, 437512928827174200⟩, ⟨.privateRow 3 24, 3331713574848859200⟩, ⟨.privateRow 3 25, 5268196916187004800⟩, ⟨.privateRow 4 20, 75174042753810000⟩, ⟨.privateRow 4 21, 657622526010329880⟩, ⟨.privateRow 4 22, 1395981973938251700⟩, ⟨.privateRow 4 23, 2109383639671908600⟩, ⟨.privateRow 4 24, 3215945549007991800⟩, ⟨.privateRow 5 17, 3280321865620800⟩, ⟨.privateRow 5 18, 105907534518614400⟩, ⟨.privateRow 5 19, 309443695990228800⟩, ⟨.privateRow 5 20, 545845558439301120⟩, ⟨.privateRow 5 21, 835661995266898800⟩, ⟨.privateRow 5 22, 1353132769568580000⟩, ⟨.privateRow 5 23, 1263743998730413200⟩, ⟨.privateRow 6 15, 8474164819520400⟩, ⟨.privateRow 6 16, 58225713114769200⟩, ⟨.privateRow 6 17, 132853035557642400⟩, ⟨.privateRow 6 18, 231536051681734800⟩, ⟨.privateRow 6 19, 349682310875177280⟩, ⟨.privateRow 6 20, 508654909287825300⟩, ⟨.privateRow 6 21, 762948193912304400⟩, ⟨.privateRow 7 13, 5740563264836400⟩, ⟨.privateRow 7 14, 28429456168713600⟩, ⟨.privateRow 7 15, 61847735174725500⟩, ⟨.privateRow 7 16, 107547695451424800⟩, ⟨.privateRow 7 17, 128843753277439200⟩, ⟨.privateRow 7 18, 342684290895186240⟩, ⟨.privateRow 7 19, 150758125740822600⟩, ⟨.privateRow 8 11, 3131216326274400⟩, ⟨.privateRow 8 12, 14590598298125850⟩, ⟨.privateRow 8 13, 32476705137176300⟩, ⟨.privateRow 8 14, 57046847444311725⟩, ⟨.privateRow 8 15, 87748609905356400⟩, ⟨.privateRow 8 16, 122704539785878050⟩, ⟨.privateRow 9 9, 1685720958721800⟩, ⟨.privateRow 9 10, 8349910203398400⟩, ⟨.privateRow 9 11, 19791275255912160⟩, ⟨.privateRow 9 12, 35840553716968000⟩, ⟨.privateRow 9 13, 52211789694464400⟩, ⟨.privateRow 10 7, 1009329804806400⟩, ⟨.privateRow 10 8, 5535543148235100⟩, ⟨.privateRow 10 9, 14314131777254400⟩, ⟨.privateRow 10 10, 21404100173175720⟩, ⟨.privateRow 11 5, 702926114061600⟩, ⟨.privateRow 11 6, 4415817896028000⟩, ⟨.privateRow 11 7, 9157565208191400⟩, ⟨.privateRow 12 3, 601392342030480⟩, ⟨.privateRow 12 4, 3866093627338800⟩, ⟨.privateRow 13 1, 1127610641307150⟩, ⟨.hall 4 24, 381042187910512128⟩, ⟨.hall 3 25, 1767399571328806800⟩, ⟨.hall 2 26, 4699547046111517600⟩, ⟨.assumptionRow 16, 145954432915200⟩]
  caps := #[0, 0, 129460527299188800, 49555449198949200, 0, 0, 2274434769578400, 4628615651070840, 672002878895075, 728060017588080, 145954432915200, 7453739055934800, 977262555799530, 12818876581110600, 69655910137632000, 16316790374102400] }

theorem case_44_29_16_checked :
    (Witness.linear .conditional case_44_29_16).check 44 29 16 = true := by
  change case_44_29_16.check 44 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_29_17 : Certificate := {
  objectiveScale := 89528660294385312000
  eta := 695430710072925887781040320
  rows := #[⟨.count 2, 100730669804172405727329600⟩, ⟨.count 3, 14226669046624283648118720⟩, ⟨.count 4, 1895558989381917176116800⟩, ⟨.count 5, 223718285828168853321600⟩, ⟨.count 6, 21767184567065077620480⟩, ⟨.count 7, 1410836036754217993920⟩, ⟨.path 6, 10021244736632766436800⟩, ⟨.path 7, 1008886772105202790800⟩, ⟨.privateRow 2 27, 9424586273523426801956160⟩, ⟨.privateRow 3 23, 199532525198096544854400⟩, ⟨.privateRow 3 24, 1917729269959483458878400⟩, ⟨.privateRow 3 25, 3096079682657131387657440⟩, ⟨.privateRow 4 20, 34641063402447316815000⟩, ⟨.privateRow 4 21, 361818979025881734669312⟩, ⟨.privateRow 4 22, 799377179074874282822940⟩, ⟨.privateRow 4 23, 1235438885184881106890160⟩, ⟨.privateRow 4 24, 1935465494421536485087680⟩, ⟨.privateRow 5 17, 3023220078759038558400⟩, ⟨.privateRow 5 18, 57354803779885760079360⟩, ⟨.privateRow 5 19, 171215030460386883690720⟩, ⟨.privateRow 5 20, 308005661623970848329792⟩, ⟨.privateRow 5 21, 484319856617197977055680⟩, ⟨.privateRow 5 22, 812641557170429564497920⟩, ⟨.privateRow 5 23, 802362608902648833399360⟩, ⟨.privateRow 6 14, 30232200787590385584⟩, ⟨.privateRow 6 15, 6819040844312053637280⟩, ⟨.privateRow 6 16, 31781601077954392845180⟩, ⟨.privateRow 6 17, 72470904173680952871360⟩, ⟨.privateRow 6 18, 128234918340695885518800⟩, ⟨.privateRow 6 19, 199109274387070279456224⟩, ⟨.privateRow 6 20, 344042444962778587945920⟩, ⟨.privateRow 6 21, 394026350264928025444800⟩, ⟨.privateRow 6 22, 127428726319693475236560⟩, ⟨.privateRow 7 12, 439741102364951063040⟩, ⟨.privateRow 7 13, 4554984918663618094656⟩, ⟨.privateRow 7 14, 15608773295518887964480⟩, ⟨.privateRow 7 15, 33129453363067797535800⟩, ⟨.privateRow 7 16, 58304958661781457912000⟩, ⟨.privateRow 7 17, 91133289707480795654880⟩, ⟨.privateRow 7 18, 158981066541675307657728⟩, ⟨.privateRow 7 19, 167284844358000133564800⟩, ⟨.privateRow 8 9, 13565731122636711480⟩, ⟨.privateRow 8 10, 367405217904744269250⟩, ⟨.privateRow 8 11, 2725478707366102942800⟩, ⟨.privateRow 8 12, 8235755364552747539508⟩, ⟨.privateRow 8 13, 17204361670419491648080⟩, ⟨.privateRow 8 14, 30244797537918548244660⟩, ⟨.privateRow 8 15, 26176047181922008851480⟩, ⟨.privateRow 8 16, 127269167482203414868200⟩, ⟨.privateRow 9 7, 14396286089328755040⟩, ⟨.privateRow 9 8, 279066468808526636160⟩, ⟨.privateRow 9 9, 1746749378838555611520⟩, ⟨.privateRow 9 10, 5038700131265064264000⟩, ⟨.privateRow 9 11, 10581270275656634954400⟩, ⟨.privateRow 9 12, 18721570265500416554240⟩, ⟨.privateRow 9 13, 29728330774463879157600⟩, ⟨.privateRow 9 14, 16123840420048205644800⟩, ⟨.privateRow 10 6, 237538720473924458160⟩, ⟨.privateRow 10 7, 1325565726840501521760⟩, ⟨.privateRow 10 8, 3779025098448798198000⟩, ⟨.privateRow 10 9, 5414312322868459963680⟩, ⟨.privateRow 10 10, 19620698311146160244016⟩, ⟨.privateRow 11 4, 241857606300723084672⟩, ⟨.privateRow 11 5, 1252476889771601688480⟩, ⟨.privateRow 11 6, 3627864094510846270080⟩, ⟨.privateRow 11 7, 5794505150954823903600⟩, ⟨.privateRow 12 2, 311769570622025851335⟩, ⟨.privateRow 12 3, 1551919640429639793312⟩, ⟨.privateRow 12 4, 1900309763791395665280⟩, ⟨.privateRow 13 0, 782480490972927626880⟩, ⟨.privateRow 13 1, 415692760829367801780⟩, ⟨.hall 4 24, 275354884773373231899072⟩, ⟨.hall 3 25, 1107405514849435823941920⟩, ⟨.hall 2 26, 2824493745581944423827840⟩]
  caps := #[0, 425030362049814242641920, 17374822244051754081600, 3527840180552795387280, 10185724376348038674156, 2044814197509804791928, 0, 0, 659112524178151840846, 255302699648809679680, 1567343232187915176144, 64063473097512959928, 788593619808653623965, 0, 81471080867890633920000, 24441324260367190176000] }

theorem case_44_29_17_checked :
    (Witness.linear .negative case_44_29_17).check 44 29 17 = true := by
  change case_44_29_17.check 44 29 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_29_18 : Certificate := {
  objectiveScale := 8479721069820000
  eta := 78697436907049550029440
  rows := #[⟨.count 2, 10443199669483598297280⟩, ⟨.count 3, 1300234299163578979200⟩, ⟨.count 4, 145142433395004165120⟩, ⟨.count 5, 13286396996386113600⟩, ⟨.count 6, 824672917017069120⟩, ⟨.path 5, 2951925198851428800⟩, ⟨.path 6, 727003301147323200⟩, ⟨.hall 11 7, 23754090432765⟩, ⟨.hall 12 7, 259135531993800⟩, ⟨.hall 9 8, 235676946992256⟩, ⟨.hall 10 9, 285669026657280⟩, ⟨.hall 11 9, 248770110714048⟩, ⟨.hall 8 10, 262123059430320⟩, ⟨.hall 9 10, 104150165968800⟩, ⟨.hall 7 11, 78346824585260⟩, ⟨.hall 7 12, 181270884102840⟩, ⟨.hall 6 15, 738296375789700⟩, ⟨.hall 5 16, 769637860919200⟩]
  caps := #[0, 8465730897190126560, 0, 0, 195231179185922880, 0, 0, 18591659964958080, 0, 149681833799509440, 31871417082785280, 0, 583811836214967360, 0, 13889783112365160000, 5401582321475340000] }

theorem case_44_29_18_checked :
    (Witness.linear .negative case_44_29_18).check 44 29 18 = true := by
  change case_44_29_18.check 44 29 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_30_1_checked :
    (Witness.rising).check 44 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_30_2_checked :
    (Witness.rising).check 44 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_30_3_checked :
    (Witness.rising).check 44 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_30_4_checked :
    (Witness.rising).check 44 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_30_5_checked :
    (Witness.rising).check 44 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_30_6_checked :
    (Witness.rising).check 44 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_30_7_checked :
    (Witness.rising).check 44 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_30_8_checked :
    (Witness.rising).check 44 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_44_30_9_checked :
    (Witness.linear .positive case_44_30_9).check 44 30 9 = true := by
  change case_44_30_9.check 44 30 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_44_30_10_checked :
    (Witness.linear .positive case_44_30_10).check 44 30 10 = true := by
  change case_44_30_10.check 44 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_44_30_11_checked :
    (Witness.linear .positive case_44_30_11).check 44 30 11 = true := by
  change case_44_30_11.check 44 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_44_30_12_checked :
    (Witness.linear .positive case_44_30_12).check 44 30 12 = true := by
  change case_44_30_12.check 44 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_44_30_13_checked :
    (Witness.linear .positive case_44_30_13).check 44 30 13 = true := by
  change case_44_30_13.check 44 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_44_30_14_checked :
    (Witness.linear .positive case_44_30_14).check 44 30 14 = true := by
  change case_44_30_14.check 44 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_30_15 : Certificate := {
  objectiveScale := 12702690000
  eta := 86581768159766880
  rows := #[⟨.count 2, 11725825497946560⟩, ⟨.count 3, 1627664162604480⟩, ⟨.count 4, 214404741270720⟩, ⟨.count 5, 27178065794880⟩, ⟨.count 6, 3019785088320⟩, ⟨.count 7, 880770650760⟩, ⟨.path 6, 1491667572780⟩, ⟨.privateRow 2 27, 622830674466000⟩, ⟨.privateRow 2 28, 1345314256846560⟩, ⟨.privateRow 3 24, 191001406836240⟩, ⟨.privateRow 3 25, 370007556238320⟩, ⟨.privateRow 3 26, 424908926802360⟩, ⟨.privateRow 4 20, 3127634555760⟩, ⟨.privateRow 4 21, 36237421059840⟩, ⟨.privateRow 4 22, 100558843441056⟩, ⟨.privateRow 4 23, 136834011814500⟩, ⟨.privateRow 4 24, 171876101276880⟩, ⟨.privateRow 4 25, 214027268134680⟩, ⟨.privateRow 5 17, 503297514720⟩, ⟨.privateRow 5 18, 6643527194304⟩, ⟨.privateRow 5 19, 23166065606112⟩, ⟨.privateRow 5 20, 41522044964400⟩, ⟨.privateRow 5 21, 56168002642752⟩, ⟨.privateRow 5 22, 47561615141040⟩, ⟨.privateRow 5 23, 132065267862528⟩, ⟨.privateRow 6 15, 855605775024⟩, ⟨.privateRow 6 16, 4977053201120⟩, ⟨.privateRow 6 17, 11785550136360⟩, ⟨.privateRow 6 18, 18741840786240⟩, ⟨.privateRow 6 19, 25612251304640⟩, ⟨.privateRow 6 20, 30936020571456⟩, ⟨.privateRow 6 21, 22019266269000⟩, ⟨.privateRow 7 13, 754946272080⟩, ⟨.privateRow 7 14, 3170774342736⟩, ⟨.privateRow 7 15, 6403062826160⟩, ⟨.privateRow 7 16, 9924397868385⟩, ⟨.privateRow 7 17, 13463208518760⟩, ⟨.privateRow 7 18, 7234901774100⟩, ⟨.privateRow 8 11, 597665798730⟩, ⟨.privateRow 8 12, 2161891597320⟩, ⟨.privateRow 8 13, 4127039620704⟩, ⟨.privateRow 8 14, 6361121366600⟩, ⟨.privateRow 8 15, 817858461420⟩, ⟨.privateRow 9 9, 503297514720⟩, ⟨.privateRow 9 10, 1719599841960⟩, ⟨.privateRow 9 11, 2455481814240⟩, ⟨.privateRow 10 7, 496107550224⟩, ⟨.privateRow 10 8, 975622874688⟩, ⟨.privateRow 11 5, 452967763248⟩, ⟨.privateRow 12 3, 173008520685⟩, ⟨.hall 3 26, 57823292246720⟩, ⟨.hall 2 27, 281163561616080⟩, ⟨.assumptionRow 15, 12836337696⟩]
  caps := #[0, 0, 17288196618420, 4248713892540, 957024016596, 1011128472684, 659229461132, 0, 273171579408, 300387054240, 2728844016624, 12836337696, 0, 5382739174176, 1128534694560] }

theorem case_44_30_15_checked :
    (Witness.linear .conditional case_44_30_15).check 44 30 15 = true := by
  change case_44_30_15.check 44 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_30_16 : Certificate := {
  objectiveScale := 13231218000000
  eta := 132223342421563192800
  rows := #[⟨.count 2, 15344120104383470400⟩, ⟨.count 3, 1722418352661006000⟩, ⟨.count 4, 167730107685940800⟩, ⟨.count 5, 13800578480488800⟩, ⟨.count 7, 619256726688600⟩, ⟨.path 5, 9379270440540000⟩, ⟨.privateRow 2 27, 613064159421714000⟩, ⟨.privateRow 2 28, 1681547408699558400⟩, ⟨.privateRow 3 24, 211166543800812600⟩, ⟨.privateRow 3 25, 424279323028360800⟩, ⟨.privateRow 3 26, 530349153785451000⟩, ⟨.privateRow 4 20, 5383742154476400⟩, ⟨.privateRow 4 21, 35297633421250200⟩, ⟨.privateRow 4 22, 108281461923835200⟩, ⟨.privateRow 4 23, 158573954655616500⟩, ⟨.privateRow 4 24, 215147479900953600⟩, ⟨.privateRow 4 25, 292731501230368200⟩, ⟨.privateRow 5 17, 1155945889818720⟩, ⟨.privateRow 5 18, 5865245854207740⟩, ⟨.privateRow 5 19, 21838278035059200⟩, ⟨.privateRow 5 20, 43878762348220800⟩, ⟨.privateRow 5 21, 64671633925490592⟩, ⟨.privateRow 5 22, 86890565279077560⟩, ⟨.privateRow 5 23, 126823777625825280⟩, ⟨.privateRow 5 24, 77070922898729760⟩, ⟨.privateRow 6 12, 54440151796800⟩, ⟨.privateRow 6 14, 53615301012000⟩, ⟨.privateRow 6 15, 719517339581040⟩, ⟨.privateRow 6 16, 4062848365576000⟩, ⟨.privateRow 6 17, 10836992717050500⟩, ⟨.privateRow 6 18, 19327550081954400⟩, ⟨.privateRow 6 19, 29154213513625200⟩, ⟨.privateRow 6 20, 39066252929383680⟩, ⟨.privateRow 6 21, 57708829244266200⟩, ⟨.privateRow 6 22, 7313127058036800⟩, ⟨.privateRow 7 13, 562960660626000⟩, ⟨.privateRow 7 14, 2477026906754400⟩, ⟨.privateRow 7 15, 5720752617980400⟩, ⟨.privateRow 7 16, 9908107627017600⟩, ⟨.privateRow 7 17, 14937988794814800⟩, ⟨.privateRow 7 18, 20273285695162500⟩, ⟨.privateRow 7 19, 11341244623068360⟩, ⟨.privateRow 8 11, 383349402235800⟩, ⟨.privateRow 8 12, 1632585915815400⟩, ⟨.privateRow 8 13, 3547456391458980⟩, ⟨.privateRow 8 14, 5022860116474200⟩, ⟨.privateRow 8 15, 11312493417900675⟩, ⟨.privateRow 8 16, 2186355381982200⟩, ⟨.privateRow 9 9, 308494193515200⟩, ⟨.privateRow 9 10, 1258172397081600⟩, ⟨.privateRow 9 11, 2723657291409600⟩, ⟨.privateRow 9 12, 4328899403708880⟩, ⟨.privateRow 10 7, 303309417153600⟩, ⟨.privateRow 10 8, 1192239324349920⟩, ⟨.privateRow 10 9, 1503909193386600⟩, ⟨.privateRow 11 5, 353860986679200⟩, ⟨.privateRow 11 6, 644532511451400⟩, ⟨.privateRow 12 3, 243279428341950⟩, ⟨.hall 3 26, 97528019717528400⟩, ⟨.hall 2 27, 374511302830407600⟩, ⟨.assumptionRow 16, 9383877508005⟩]
  caps := #[0, 68886598551170400, 8964575151511980, 1449886624436250, 2077087043889000, 0, 518605618960340, 0, 602359165244655, 69135142352100, 1007621836491600, 0, 7786551086143830, 17388241235645280, 4845812659167480] }

theorem case_44_30_16_checked :
    (Witness.linear .conditional case_44_30_16).check 44 30 16 = true := by
  change case_44_30_16.check 44 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_30_17 : Certificate := {
  objectiveScale := 21831509700000
  eta := 302398275664470585600
  rows := #[⟨.count 2, 34728624954670046400⟩, ⟨.count 3, 3812675200975040400⟩, ⟨.count 4, 350322376812408000⟩, ⟨.count 5, 22293242160789600⟩, ⟨.path 5, 21706311590964000⟩, ⟨.privateRow 2 27, 1377934682128804800⟩, ⟨.privateRow 2 28, 3900255795178142400⟩, ⟨.privateRow 3 24, 466123384703176200⟩, ⟨.privateRow 3 25, 957547829953915200⟩, ⟨.privateRow 3 26, 1231967025123634800⟩, ⟨.privateRow 4 20, 15317125566256800⟩, ⟨.privateRow 4 21, 75018529175990400⟩, ⟨.privateRow 4 22, 235352942240335920⟩, ⟨.privateRow 4 23, 354303312912549000⟩, ⟨.privateRow 4 24, 497882408257634400⟩, ⟨.privateRow 4 25, 706748855645032200⟩, ⟨.privateRow 5 17, 4553011361939040⟩, ⟨.privateRow 5 18, 13004391260460600⟩, ⟨.privateRow 5 19, 45435750689609280⟩, ⟨.privateRow 5 20, 93631617075316320⟩, ⟨.privateRow 5 21, 142209653326636896⟩, ⟨.privateRow 5 22, 199206042451055640⟩, ⟨.privateRow 5 23, 307292880832217280⟩, ⟨.privateRow 5 24, 239917748968497600⟩, ⟨.privateRow 6 13, 39317887408800⟩, ⟨.privateRow 6 14, 772060334572800⟩, ⟨.privateRow 6 15, 2500617639199680⟩, ⟨.privateRow 6 16, 8636829267466400⟩, ⟨.privateRow 6 17, 22057334836336800⟩, ⟨.privateRow 6 18, 40289600911903200⟩, ⟨.privateRow 6 19, 62829984079262400⟩, ⟨.privateRow 6 20, 88134976415566080⟩, ⟨.privateRow 6 21, 138654529947133200⟩, ⟨.privateRow 6 22, 64599289012658400⟩, ⟨.privateRow 7 10, 6318946190700⟩, ⟨.privateRow 7 11, 115685322568200⟩, ⟨.privateRow 7 12, 434954129459850⟩, ⟨.privateRow 7 13, 1817558704306800⟩, ⟨.privateRow 7 14, 5130984306848400⟩, ⟨.privateRow 7 15, 11451334707813000⟩, ⟨.privateRow 7 16, 20147959929046950⟩, ⟨.privateRow 7 17, 31430438352541800⟩, ⟨.privateRow 7 18, 44689693776027300⟩, ⟨.privateRow 7 19, 54529978047264720⟩, ⟨.privateRow 8 8, 17693049333960⟩, ⟨.privateRow 8 9, 82146300479100⟩, ⟨.privateRow 8 10, 381081062577600⟩, ⟨.privateRow 8 11, 1349095011714450⟩, ⟨.privateRow 8 12, 3417975439515000⟩, ⟨.privateRow 8 13, 7015294060915140⟩, ⟨.privateRow 8 14, 12139397737467000⟩, ⟨.privateRow 8 15, 18820981228999950⟩, ⟨.privateRow 8 16, 21939381174110400⟩, ⟨.privateRow 9 5, 6938450719200⟩, ⟨.privateRow 9 6, 22116311667450⟩, ⟨.privateRow 9 7, 94362929781120⟩, ⟨.privateRow 9 8, 379136771442000⟩, ⟨.privateRow 9 9, 1197683339529600⟩, ⟨.privateRow 9 10, 2781740534172600⟩, ⟨.privateRow 9 11, 5415145402212000⟩, ⟨.privateRow 9 12, 9212181019881840⟩, ⟨.privateRow 9 13, 5242384987840000⟩, ⟨.privateRow 10 3, 11795366222640⟩, ⟨.privateRow 10 4, 37467633883680⟩, ⟨.privateRow 10 5, 132697870004700⟩, ⟨.privateRow 10 6, 467096502416544⟩, ⟨.privateRow 10 7, 1349726906333520⟩, ⟨.privateRow 10 8, 2956100242566240⟩, ⟨.privateRow 10 9, 3804005606801400⟩, ⟨.privateRow 11 1, 27936393685200⟩, ⟨.privateRow 11 2, 58976831113200⟩, ⟨.privateRow 11 3, 249784225891200⟩, ⟨.privateRow 11 4, 763012752527025⟩, ⟨.privateRow 11 5, 1910849328067680⟩, ⟨.privateRow 12 0, 204866887024800⟩, ⟨.privateRow 12 1, 756869332619400⟩, ⟨.privateRow 13 0, 648745142245200⟩, ⟨.hall 3 26, 256038082806105600⟩, ⟨.hall 2 27, 895824363563157600⟩, ⟨.assumptionRow 17, 5029185961800⟩]
  caps := #[0, 0, 27343350840405600, 0, 722493886514400, 0, 1477824923926000, 0, 970953974352600, 279722656100480, 5587278737040, 0, 14267512133074200, 0, 25294860398808000] }

theorem case_44_30_17_checked :
    (Witness.linear .conditional case_44_30_17).check 44 30 17 = true := by
  change case_44_30_17.check 44 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_30_18 : Certificate := {
  objectiveScale := 258314086800000
  eta := 2614940510772258068400
  rows := #[⟨.count 2, 338084448449094547200⟩, ⟨.count 3, 41162879275457940000⟩, ⟨.count 4, 4440601521837280800⟩, ⟨.count 5, 374207993413254000⟩, ⟨.count 6, 16631466373922400⟩, ⟨.path 5, 115583532499234800⟩, ⟨.path 6, 19237788641194200⟩, ⟨.privateRow 4 20, 3563885651554800⟩, ⟨.privateRow 6 15, 7761350974497120⟩, ⟨.privateRow 6 16, 16015486137851200⟩, ⟨.privateRow 7 12, 173244441395025⟩, ⟨.privateRow 7 13, 6236799890220900⟩, ⟨.privateRow 7 14, 13097279769463890⟩, ⟨.privateRow 7 19, 270261328576239000⟩, ⟨.privateRow 8 10, 159917945903100⟩, ⟨.privateRow 8 11, 4677599917665675⟩, ⟨.privateRow 8 12, 8693721059095800⟩, ⟨.privateRow 8 20, 103946664837015000⟩, ⟨.privateRow 9 9, 213223927870800⟩, ⟨.privateRow 9 10, 13397570134548600⟩, ⟨.hall 11 4, 11799930992850⟩, ⟨.hall 10 5, 8045407495125⟩, ⟨.hall 12 6, 14782331133900⟩, ⟨.hall 9 7, 20081337107832⟩, ⟨.hall 11 7, 9076869994500⟩, ⟨.hall 8 8, 13930203199640⟩, ⟨.hall 10 8, 8416733994900⟩, ⟨.hall 7 10, 7733767204800⟩, ⟨.hall 6 12, 5920466614425⟩, ⟨.hall 5 15, 10906138160190⟩, ⟨.hall 4 19, 148114177473708⟩, ⟨.hall 3 22, 3140541241388628⟩, ⟨.hall 2 25, 190931873887926600⟩]
  caps := #[0, 0, 0, 0, 134922632922000, 7390535822069400, 2606322267271800, 28689279495016140, 83581219197840, 100406685539160, 19523895308517600, 88499482446375, 74441986790371200, 0, 658184293166400000] }

theorem case_44_30_18_checked :
    (Witness.linear .negative case_44_30_18).check 44 30 18 = true := by
  change case_44_30_18.check 44 30 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934, 7072, 3640] }

theorem case_44_30_19_checked :
    (Witness.linear .negative case_44_30_19).check 44 30 19 = true := by
  change case_44_30_19.check 44 30 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_31_1_checked :
    (Witness.rising).check 44 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_31_2_checked :
    (Witness.rising).check 44 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_31_3_checked :
    (Witness.rising).check 44 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_31_4_checked :
    (Witness.rising).check 44 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_31_5_checked :
    (Witness.rising).check 44 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_31_6_checked :
    (Witness.rising).check 44 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_31_7_checked :
    (Witness.rising).check 44 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_31_8_checked :
    (Witness.rising).check 44 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_44_31_9_checked :
    (Witness.linear .positive case_44_31_9).check 44 31 9 = true := by
  change case_44_31_9.check 44 31 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_44_31_10_checked :
    (Witness.linear .positive case_44_31_10).check 44 31 10 = true := by
  change case_44_31_10.check 44 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_44_31_11_checked :
    (Witness.linear .positive case_44_31_11).check 44 31 11 = true := by
  change case_44_31_11.check 44 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_44_31_12_checked :
    (Witness.linear .positive case_44_31_12).check 44 31 12 = true := by
  change case_44_31_12.check 44 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_44_31_13_checked :
    (Witness.linear .positive case_44_31_13).check 44 31 13 = true := by
  change case_44_31_13.check 44 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_44_31_14_checked :
    (Witness.linear .positive case_44_31_14).check 44 31 14 = true := by
  change case_44_31_14.check 44 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_15 : Certificate := {
  objectiveScale := 583
  eta := 238262888
  rows := #[⟨.assumptionRow 15, 1158⟩]
  caps := #[0, 0, 69233758, 20378070, 6088992, 1852136, 575575, 183601, 60495, 20764, 3138933, 1923807, 770697, 230199] }

theorem case_44_31_15_checked :
    (Witness.linear .conditional case_44_31_15).check 44 31 15 = true := by
  change case_44_31_15.check 44 31 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_16 : Certificate := {
  objectiveScale := 127753727824800000
  eta := 2022752838611016774662400
  rows := #[⟨.count 2, 217421500768575474571200⟩, ⟨.count 3, 21320188022250506188800⟩, ⟨.count 4, 1821099393567230736960⟩, ⟨.count 5, 123380717721357096000⟩, ⟨.path 4, 313919572403400163200⟩, ⟨.path 5, 79119452153232691200⟩, ⟨.privateRow 2 28, 19645294779183083610600⟩, ⟨.privateRow 2 29, 27686633056672532342400⟩, ⟨.privateRow 3 24, 1621222630858632241440⟩, ⟨.privateRow 3 25, 4136338561608496643400⟩, ⟨.privateRow 3 26, 8426903020368689656800⟩, ⟨.privateRow 3 27, 8975947214228728734000⟩, ⟨.privateRow 3 28, 11326349886820581412800⟩, ⟨.privateRow 4 20, 2776066148730534660⟩, ⟨.privateRow 4 21, 520314112447780210560⟩, ⟨.privateRow 4 22, 904997564486154299160⟩, ⟨.privateRow 4 23, 2167552448928801462528⟩, ⟨.privateRow 4 24, 2945406183803097274260⟩, ⟨.privateRow 4 25, 3605184571818054345120⟩, ⟨.privateRow 4 26, 4325111059722173000280⟩, ⟨.privateRow 5 18, 103639802885939960640⟩, ⟨.privateRow 5 19, 230105038550330984040⟩, ⟨.privateRow 5 20, 540055027283197345920⟩, ⟨.privateRow 5 21, 908904620547330607200⟩, ⟨.privateRow 5 22, 1230846039988258389696⟩, ⟨.privateRow 5 23, 1502777141846129429280⟩, ⟨.privateRow 5 24, 1625335321449344144640⟩, ⟨.privateRow 6 15, 13740125382605676600⟩, ⟨.privateRow 6 16, 52745256825880158540⟩, ⟨.privateRow 6 17, 151826827640447759800⟩, ⟨.privateRow 6 18, 280305568073208152475⟩, ⟨.privateRow 6 19, 434035739126916927000⟩, ⟨.privateRow 6 20, 594283790357870012400⟩, ⟨.privateRow 6 21, 726095523790186509960⟩, ⟨.privateRow 6 22, 89451020347983894600⟩, ⟨.privateRow 7 12, 813499237723233600⟩, ⟨.privateRow 7 13, 8592585698451654900⟩, ⟨.privateRow 7 14, 41821256266589872800⟩, ⟨.privateRow 7 15, 98880832345259044080⟩, ⟨.privateRow 7 16, 167739023378321194800⟩, ⟨.privateRow 7 17, 250837405581723310350⟩, ⟨.privateRow 7 18, 297246810755228677200⟩, ⟨.privateRow 8 10, 220322710216709100⟩, ⟨.privateRow 8 11, 8541741996093952800⟩, ⟨.privateRow 8 12, 36243085830648646950⟩, ⟨.privateRow 8 13, 56082144418798680000⟩, ⟨.privateRow 8 14, 167489324306742257820⟩, ⟨.privateRow 8 15, 44211423850152959400⟩, ⟨.privateRow 9 9, 10222973754055302240⟩, ⟨.privateRow 9 10, 38342930738021743680⟩, ⟨.privateRow 9 11, 60867820742536167360⟩, ⟨.privateRow 10 7, 15545970432890994096⟩, ⟨.privateRow 10 8, 22208529189844277280⟩, ⟨.privateRow 11 5, 11566942286377227750⟩, ⟨.hall 3 27, 364854408118870269600⟩, ⟨.assumptionRow 16, 101487561384021120⟩]
  caps := #[0, 1297116506900793902400, 123296033563576695360, 0, 0, 43656308716751194464, 9565548918211855100, 1588781860294305600, 18774935847895904250, 32337970181301449280, 101487561384021120, 0, 695322557154500204160, 219393112041245197440] }

theorem case_44_31_16_checked :
    (Witness.linear .conditional case_44_31_16).check 44 31 16 = true := by
  change case_44_31_16.check 44 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_17 : Certificate := {
  objectiveScale := 498239538516720000
  eta := 9273393448511376421036800
  rows := #[⟨.count 2, 1008119168357664559996800⟩, ⟨.count 3, 98161699019111705577600⟩, ⟨.count 4, 8083904625103316929920⟩, ⟨.count 5, 444170583796885545600⟩, ⟨.path 4, 1175606050855631915520⟩, ⟨.path 5, 412774510246799500800⟩, ⟨.privateRow 2 28, 96292481145633145573200⟩, ⟨.privateRow 2 29, 140876103494245532212800⟩, ⟨.privateRow 3 24, 6766198559839223144640⟩, ⟨.privateRow 3 25, 19358434610480928362400⟩, ⟨.privateRow 3 26, 41357216580198898579200⟩, ⟨.privateRow 3 27, 46341797576141725257600⟩, ⟨.privateRow 3 28, 61295540563970205292800⟩, ⟨.privateRow 4 21, 2192299095740342228640⟩, ⟨.privateRow 4 22, 3942013931197359217200⟩, ⟨.privateRow 4 23, 10069347134675395318752⟩, ⟨.privateRow 4 24, 14457752502588624509280⟩, ⟨.privateRow 4 25, 18699581577848881469760⟩, ⟨.privateRow 4 26, 24051837112601352294240⟩, ⟨.privateRow 5 17, 24676143544271419200⟩, ⟨.privateRow 5 18, 425526386452324917760⟩, ⟨.privateRow 5 19, 951265333631663210160⟩, ⟨.privateRow 5 20, 2328017885233835034240⟩, ⟨.privateRow 5 21, 4181783792635863173760⟩, ⟨.privateRow 5 22, 5979523103647850300544⟩, ⟨.privateRow 5 23, 7800128974344195609120⟩, ⟨.privateRow 5 24, 10946337276238801557120⟩, ⟨.privateRow 5 25, 913017311138042510400⟩, ⟨.privateRow 6 14, 7197208533745830600⟩, ⟨.privateRow 6 15, 73467609188626270800⟩, ⟨.privateRow 6 16, 210981027303520634160⟩, ⟨.privateRow 6 17, 614847243311429528400⟩, ⟨.privateRow 6 18, 1189852796525337494550⟩, ⟨.privateRow 6 19, 1955584375883509971600⟩, ⟨.privateRow 6 20, 2838784680238891183800⟩, ⟨.privateRow 6 21, 3716227217767275731520⟩, ⟨.privateRow 6 22, 2967306261198638158800⟩, ⟨.privateRow 7 11, 1510784298628862400⟩, ⟨.privateRow 7 12, 13422737422433354400⟩, ⟨.privateRow 7 13, 44945832884208656400⟩, ⟨.privateRow 7 14, 164400800496249844800⟩, ⟨.privateRow 7 15, 393408231362955768960⟩, ⟨.privateRow 7 16, 698569873193778986400⟩, ⟨.privateRow 7 17, 1101172905663112081800⟩, ⟨.privateRow 7 18, 1590100474306877676000⟩, ⟨.privateRow 7 19, 1210012324510166377200⟩, ⟨.privateRow 8 8, 385564742879240925⟩, ⟨.privateRow 8 9, 2878883413498332240⟩, ⟨.privateRow 8 10, 11016135510835455000⟩, ⟨.privateRow 8 11, 45555957312501081600⟩, ⟨.privateRow 8 12, 140345566408043696700⟩, ⟨.privateRow 8 13, 302282758417324885200⟩, ⟨.privateRow 8 14, 513263785720845519360⟩, ⟨.privateRow 8 15, 784838454394188194000⟩, ⟨.privateRow 8 16, 150370249722903960750⟩, ⟨.privateRow 9 6, 1161230284436302080⟩, ⟨.privateRow 9 7, 3701421531640712880⟩, ⟨.privateRow 9 8, 15134701373819803776⟩, ⟨.privateRow 9 9, 54287515797397122240⟩, ⟨.privateRow 9 10, 86556318893752055040⟩, ⟨.privateRow 9 11, 429364897670322694080⟩, ⟨.privateRow 9 12, 129213260740912158720⟩, ⟨.privateRow 10 4, 2467614354427141920⟩, ⟨.privateRow 10 5, 6531920349954199200⟩, ⟨.privateRow 10 6, 26372628412940079270⟩, ⟨.privateRow 10 7, 84392410921408253664⟩, ⟨.privateRow 10 8, 134837498652625969200⟩, ⟨.privateRow 11 2, 7792466382401500800⟩, ⟨.privateRow 11 3, 24676143544271419200⟩, ⟨.privateRow 11 4, 56609976366269726400⟩, ⟨.privateRow 12 0, 20357818424023920840⟩, ⟨.hall 3 27, 3251963202798626316000⟩, ⟨.assumptionRow 17, 203946051099510720⟩]
  caps := #[0, 4176629438662427947200, 124391280084478767360, 107386169562838726560, 43863388771928661936, 30192447257870113216, 1713524858600034480, 0, 45200710481027729705, 0, 448432594207007576166, 0, 1481775597938341906200, 2286648439482791704320] }

theorem case_44_31_17_checked :
    (Witness.linear .conditional case_44_31_17).check 44 31 17 = true := by
  change case_44_31_17.check 44 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_18 : Certificate := {
  objectiveScale := 45869671799952000000
  eta := 1314887062625596218350592000
  rows := #[⟨.count 2, 137085477703692278152392000⟩, ⟨.count 3, 12462316154881116195672000⟩, ⟨.count 4, 927428178967897019212800⟩, ⟨.count 5, 42936489767032269408000⟩, ⟨.path 4, 268888037220083426745600⟩, ⟨.path 5, 39888956691661869792000⟩, ⟨.privateRow 4 24, 4927767259950084769619400⟩, ⟨.privateRow 5 17, 4293648976703226940800⟩, ⟨.privateRow 5 18, 19400932413251618028800⟩, ⟨.privateRow 5 19, 50808179557654852132800⟩, ⟨.privateRow 5 20, 117359738696554869715200⟩, ⟨.privateRow 5 22, 1450967110860577157527680⟩, ⟨.privateRow 6 13, 68808477190756842000⟩, ⟨.privateRow 6 14, 1416307822176411664500⟩, ⟨.privateRow 6 15, 4960465673842743246000⟩, ⟨.privateRow 6 16, 12254789787673793560200⟩, ⟨.privateRow 6 17, 39159668907895171636000⟩, ⟨.privateRow 6 18, 77039691274701129224250⟩, ⟨.privateRow 6 19, 84467320642881934758000⟩, ⟨.privateRow 6 23, 2655204453995988604710000⟩, ⟨.privateRow 7 11, 109531861650592524000⟩, ⟨.privateRow 7 12, 471829557879475488000⟩, ⟨.privateRow 7 13, 830616617516993307000⟩, ⟨.privateRow 7 14, 2300169094662443004000⟩, ⟨.privateRow 7 16, 2555743438513825560000⟩, ⟨.privateRow 8 9, 59634013565322596400⟩, ⟨.privateRow 8 10, 63893585962845639000⟩, ⟨.privateRow 8 11, 206425431572270526000⟩, ⟨.privateRow 8 12, 223627550869959736500⟩, ⟨.privateRow 10 19, 12880946930109680822400⟩, ⟨.hall 9 6, 86318382387182400⟩, ⟨.hall 8 7, 7023063749589014400⟩, ⟨.hall 10 7, 2954006863916908800⟩, ⟨.hall 7 8, 3705887234171122000⟩, ⟨.hall 11 8, 1405993651575836400⟩, ⟨.hall 7 9, 545256176786787375⟩, ⟨.hall 9 9, 401380478100398160⟩, ⟨.hall 6 10, 2169922161586479300⟩, ⟨.hall 9 11, 1045365409775540700⟩, ⟨.hall 5 13, 197124914560293720⟩, ⟨.hall 4 19, 7042941997359048144⟩, ⟨.hall 3 22, 52938364646139218400⟩, ⟨.hall 2 25, 495895576995454482000⟩]
  caps := #[0, 0, 2732413242461704401600, 21926911998384950356800, 0, 0, 10601705839458611228750, 992059092231905108400, 0, 345273529548729600, 2819733824647958400, 57670906286464150680000, 0, 458513239312320192000000] }

theorem case_44_31_18_checked :
    (Witness.linear .negative case_44_31_18).check 44 31 18 = true := by
  change case_44_31_18.check 44 31 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_19 : Certificate := {
  objectiveScale := 622
  eta := 1067605
  rows := #[⟨.assumptionRow 19, 245⟩]
  caps := #[0, 0, 623770, 306945, 137394, 78132, 35020, 18991, 10530, 4560, 14407092, 14247530, 9972948, 5798700] }

theorem case_44_31_19_checked :
    (Witness.linear .conditional case_44_31_19).check 44 31 19 = true := by
  change case_44_31_19.check 44 31 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934] }

theorem case_44_31_20_checked :
    (Witness.linear .negative case_44_31_20).check 44 31 20 = true := by
  change case_44_31_20.check 44 31 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_32_1_checked :
    (Witness.rising).check 44 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_32_2_checked :
    (Witness.rising).check 44 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_32_3_checked :
    (Witness.rising).check 44 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_32_4_checked :
    (Witness.rising).check 44 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_32_5_checked :
    (Witness.rising).check 44 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_32_6_checked :
    (Witness.rising).check 44 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_32_7_checked :
    (Witness.rising).check 44 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_32_8_checked :
    (Witness.rising).check 44 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_44_32_9_checked :
    (Witness.linear .positive case_44_32_9).check 44 32 9 = true := by
  change case_44_32_9.check 44 32 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_44_32_10_checked :
    (Witness.linear .positive case_44_32_10).check 44 32 10 = true := by
  change case_44_32_10.check 44 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_44_32_11_checked :
    (Witness.linear .positive case_44_32_11).check 44 32 11 = true := by
  change case_44_32_11.check 44 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_44_32_12_checked :
    (Witness.linear .positive case_44_32_12).check 44 32 12 = true := by
  change case_44_32_12.check 44 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_44_32_13_checked :
    (Witness.linear .positive case_44_32_13).check 44 32 13 = true := by
  change case_44_32_13.check 44 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_44_32_14_checked :
    (Witness.linear .positive case_44_32_14).check 44 32 14 = true := by
  change case_44_32_14.check 44 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_44_32_15_checked :
    (Witness.linear .positive case_44_32_15).check 44 32 15 = true := by
  change case_44_32_15.check 44 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_16 : Certificate := {
  objectiveScale := 975
  eta := 506992105
  rows := #[⟨.assumptionRow 16, 1432⟩]
  caps := #[0, 0, 149382332, 44480330, 13403208, 4160988, 1365624, 457457, 158631, 32519355, 24397197, 12497877, 5086965] }

theorem case_44_32_16_checked :
    (Witness.linear .conditional case_44_32_16).check 44 32 16 = true := by
  change case_44_32_16.check 44 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_17 : Certificate := {
  objectiveScale := 653753100000
  eta := 28168150684772498400
  rows := #[⟨.count 2, 2513533538442326400⟩, ⟨.count 3, 192606326234562240⟩, ⟨.count 4, 9791171268278400⟩, ⟨.path 4, 9617565751073280⟩, ⟨.privateRow 2 29, 221350407600722400⟩, ⟨.privateRow 2 30, 288489867726060000⟩, ⟨.privateRow 3 24, 594463969859760⟩, ⟨.privateRow 3 25, 26604011074665024⟩, ⟨.privateRow 3 26, 47627054526411360⟩, ⟨.privateRow 3 27, 96233226179650560⟩, ⟨.privateRow 3 28, 94414865801256000⟩, ⟨.privateRow 3 29, 103436730755598240⟩, ⟨.privateRow 4 21, 1809618261190740⟩, ⟨.privateRow 4 22, 7193513584857600⟩, ⟨.privateRow 4 23, 11469657771411840⟩, ⟨.privateRow 4 24, 25694830885467744⟩, ⟨.privateRow 4 25, 34041804391675080⟩, ⟨.privateRow 4 26, 40120489887397920⟩, ⟨.privateRow 4 27, 38290473352731600⟩, ⟨.privateRow 5 17, 34968468815280⟩, ⟨.privateRow 5 18, 643419826201152⟩, ⟨.privateRow 5 19, 1678486503133440⟩, ⟨.privateRow 5 20, 3107822665958010⟩, ⟨.privateRow 5 21, 6983702771965920⟩, ⟨.privateRow 5 22, 11224878489704880⟩, ⟨.privateRow 5 23, 14889574021546224⟩, ⟨.privateRow 5 24, 17781466392569880⟩, ⟨.privateRow 5 25, 7996123202427360⟩, ⟨.privateRow 6 14, 7685377761600⟩, ⟨.privateRow 6 15, 197738365324500⟩, ⟨.privateRow 6 16, 474572076778800⟩, ⟨.privateRow 6 17, 884202711472080⟩, ⟨.privateRow 6 18, 2189692213909200⟩, ⟨.privateRow 6 19, 3859020308543400⟩, ⟨.privateRow 6 20, 5773365565624800⟩, ⟨.privateRow 6 21, 7759669746628800⟩, ⟨.privateRow 6 22, 3676684721149440⟩, ⟨.privateRow 7 11, 3330330363360⟩, ⟨.privateRow 7 12, 66011905416600⟩, ⟨.privateRow 7 13, 178685032957200⟩, ⟨.privateRow 7 14, 328870123381800⟩, ⟨.privateRow 7 15, 785655208447200⟩, ⟨.privateRow 7 16, 1593563078867760⟩, ⟨.privateRow 7 17, 2583781306906800⟩, ⟨.privateRow 7 18, 3721644181054800⟩, ⟨.privateRow 8 8, 2056968753840⟩, ⟨.privateRow 8 9, 28411880912415⟩, ⟨.privateRow 8 10, 88586787665376⟩, ⟨.privateRow 8 11, 177340091848920⟩, ⟨.privateRow 8 12, 398102568050880⟩, ⟨.privateRow 8 13, 364254883492500⟩, ⟨.privateRow 8 14, 2352424265755200⟩, ⟨.privateRow 9 6, 15541541695680⟩, ⟨.privateRow 9 7, 57595125107520⟩, ⟨.privateRow 9 8, 131131758057300⟩, ⟨.privateRow 9 9, 219135737909088⟩, ⟨.privateRow 9 10, 774301809481200⟩, ⟨.privateRow 10 3, 10490540644584⟩, ⟨.privateRow 10 4, 44170697450880⟩, ⟨.privateRow 10 5, 128217718989360⟩, ⟨.privateRow 10 6, 209810812891680⟩, ⟨.privateRow 11 1, 99909910900800⟩, ⟨.privateRow 11 2, 52452703222920⟩, ⟨.assumptionRow 17, 356637881600⟩]
  caps := #[0, 0, 2594498688381600, 0, 116382999184452, 210310362446184, 62049767873500, 166426134576720, 0, 388538542392, 3935295543114936, 0, 11402278913625600] }

theorem case_44_32_17_checked :
    (Witness.linear .conditional case_44_32_17).check 44 32 17 = true := by
  change case_44_32_17.check 44 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_18 : Certificate := {
  objectiveScale := 983
  eta := 222780415
  rows := #[⟨.assumptionRow 18, 804⟩]
  caps := #[0, 0, 77166771, 25677531, 9155112, 3457392, 1231888, 422422, 178633, 58510804, 54652246, 35866566, 19403256] }

theorem case_44_32_18_checked :
    (Witness.linear .conditional case_44_32_18).check 44 32 18 = true := by
  change case_44_32_18.check 44 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_19 : Certificate := {
  objectiveScale := 18
  eta := 29183
  rows := #[⟨.assumptionRow 19, 7⟩]
  caps := #[0, 0, 16758, 7923, 3774, 2108, 900, 525, 286, 1456084, 1442518, 1017450, 600780] }

theorem case_44_32_19_checked :
    (Witness.linear .conditional case_44_32_19).check 44 32 19 = true := by
  change case_44_32_19.check 44 32 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990] }

theorem case_44_32_20_checked :
    (Witness.linear .negative case_44_32_20).check 44 32 20 = true := by
  change case_44_32_20.check 44 32 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_33_1_checked :
    (Witness.rising).check 44 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_33_2_checked :
    (Witness.rising).check 44 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_33_3_checked :
    (Witness.rising).check 44 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_33_4_checked :
    (Witness.rising).check 44 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_33_5_checked :
    (Witness.rising).check 44 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_33_6_checked :
    (Witness.rising).check 44 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_33_7_checked :
    (Witness.rising).check 44 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_33_8_checked :
    (Witness.rising).check 44 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_44_33_9_checked :
    (Witness.linear .positive case_44_33_9).check 44 33 9 = true := by
  change case_44_33_9.check 44 33 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_44_33_10_checked :
    (Witness.linear .positive case_44_33_10).check 44 33 10 = true := by
  change case_44_33_10.check 44 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_44_33_11_checked :
    (Witness.linear .positive case_44_33_11).check 44 33 11 = true := by
  change case_44_33_11.check 44 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_44_33_12_checked :
    (Witness.linear .positive case_44_33_12).check 44 33 12 = true := by
  change case_44_33_12.check 44 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_44_33_13_checked :
    (Witness.linear .positive case_44_33_13).check 44 33 13 = true := by
  change case_44_33_13.check 44 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_44_33_14_checked :
    (Witness.linear .positive case_44_33_14).check 44 33 14 = true := by
  change case_44_33_14.check 44 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_44_33_15_checked :
    (Witness.linear .positive case_44_33_15).check 44 33 15 = true := by
  change case_44_33_15.check 44 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_16 : Certificate := {
  objectiveScale := 5
  eta := 13037895
  rows := #[⟨.assumptionRow 16, 13⟩]
  caps := #[0, 0, 3714500, 1069776, 312018, 92378, 27846, 8580, 2717, 891, 306, 112] }

theorem case_44_33_16_checked :
    (Witness.linear .conditional case_44_33_16).check 44 33 16 = true := by
  change case_44_33_16.check 44 33 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_17 : Certificate := {
  objectiveScale := 9
  eta := 6874010
  rows := #[⟨.assumptionRow 17, 11⟩]
  caps := #[0, 0, 2042975, 653752, 209950, 67830, 22100, 7280, 456665, 865260, 620103, 332310] }

theorem case_44_33_17_checked :
    (Witness.linear .conditional case_44_33_17).check 44 33 17 = true := by
  change case_44_33_17.check 44 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_18 : Certificate := {
  objectiveScale := 999
  eta := 186848090
  rows := #[⟨.assumptionRow 18, 799⟩]
  caps := #[0, 0, 68076734, 23396505, 7736496, 3093048, 1140020, 482885, 208049145, 196043881, 130668681, 72427905] }

theorem case_44_33_18_checked :
    (Witness.linear .conditional case_44_33_18).check 44 33 18 = true := by
  change case_44_33_18.check 44 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_19 : Certificate := {
  objectiveScale := 91
  eta := 1137488
  rows := #[⟨.assumptionRow 19, 45⟩]
  caps := #[0, 0, 441826, 219051, 84303, 43656, 16660, 9100, 14115100, 19255968, 15036296, 9450980] }

theorem case_44_33_19_checked :
    (Witness.linear .conditional case_44_33_19).check 44 33 19 = true := by
  change case_44_33_19.check 44 33 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226] }

theorem case_44_33_20_checked :
    (Witness.linear .negative case_44_33_20).check 44 33 20 = true := by
  change case_44_33_20.check 44 33 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786] }

theorem case_44_33_21_checked :
    (Witness.linear .negative case_44_33_21).check 44 33 21 = true := by
  change case_44_33_21.check 44 33 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_34_1_checked :
    (Witness.rising).check 44 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_34_2_checked :
    (Witness.rising).check 44 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_34_3_checked :
    (Witness.rising).check 44 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_34_4_checked :
    (Witness.rising).check 44 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_34_5_checked :
    (Witness.rising).check 44 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_34_6_checked :
    (Witness.rising).check 44 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_34_7_checked :
    (Witness.rising).check 44 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_34_8_checked :
    (Witness.rising).check 44 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_44_34_9_checked :
    (Witness.linear .positive case_44_34_9).check 44 34 9 = true := by
  change case_44_34_9.check 44 34 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_44_34_10_checked :
    (Witness.linear .positive case_44_34_10).check 44 34 10 = true := by
  change case_44_34_10.check 44 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_44_34_11_checked :
    (Witness.linear .positive case_44_34_11).check 44 34 11 = true := by
  change case_44_34_11.check 44 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_44_34_12_checked :
    (Witness.linear .positive case_44_34_12).check 44 34 12 = true := by
  change case_44_34_12.check 44 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_44_34_13_checked :
    (Witness.linear .positive case_44_34_13).check 44 34 13 = true := by
  change case_44_34_13.check 44 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_44_34_14_checked :
    (Witness.linear .positive case_44_34_14).check 44 34 14 = true := by
  change case_44_34_14.check 44 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_44_34_15_checked :
    (Witness.linear .positive case_44_34_15).check 44 34 15 = true := by
  change case_44_34_15.check 44 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_44_34_16_checked :
    (Witness.linear .positive case_44_34_16).check 44 34 16 = true := by
  change case_44_34_16.check 44 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_17 : Certificate := {
  objectiveScale := 783
  eta := 1160117010
  rows := #[⟨.assumptionRow 17, 1096⟩]
  caps := #[0, 0, 342959785, 102312188, 30836810, 9403176, 2905708, 911638, 313313, 94217200, 73061593] }

theorem case_44_34_17_checked :
    (Witness.linear .conditional case_44_34_17).check 44 34 17 = true := by
  change case_44_34_17.check 44 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_18 : Certificate := {
  objectiveScale := 287
  eta := 170941290
  rows := #[⟨.assumptionRow 18, 271⟩]
  caps := #[0, 0, 56265935, 18223337, 5835318, 2005830, 724608, 255645, 100212840, 91260895, 58655014] }

theorem case_44_34_18_checked :
    (Witness.linear .conditional case_44_34_18).check 44 34 18 = true := by
  change case_44_34_18.check 44 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_19 : Certificate := {
  objectiveScale := 993
  eta := 65659825
  rows := #[⟨.assumptionRow 19, 611⟩]
  caps := #[0, 0, 27875793, 10672794, 4214181, 1775208, 638588, 334305, 442805545, 431364885, 299663573] }

theorem case_44_34_19_checked :
    (Witness.linear .conditional case_44_34_19).check 44 34 19 = true := by
  change case_44_34_19.check 44 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888] }

theorem case_44_34_20_checked :
    (Witness.linear .negative case_44_34_20).check 44 34 20 = true := by
  change case_44_34_20.check 44 34 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012] }

theorem case_44_34_21_checked :
    (Witness.linear .negative case_44_34_21).check 44 34 21 = true := by
  change case_44_34_21.check 44 34 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_34_22_checked :
    (Witness.linear .negative case_44_34_22).check 44 34 22 = true := by
  change case_44_34_22.check 44 34 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_35_1_checked :
    (Witness.rising).check 44 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_35_2_checked :
    (Witness.rising).check 44 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_35_3_checked :
    (Witness.rising).check 44 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_35_4_checked :
    (Witness.rising).check 44 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_35_5_checked :
    (Witness.rising).check 44 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_35_6_checked :
    (Witness.rising).check 44 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_35_7_checked :
    (Witness.rising).check 44 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_35_8_checked :
    (Witness.rising).check 44 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_44_35_9_checked :
    (Witness.linear .positive case_44_35_9).check 44 35 9 = true := by
  change case_44_35_9.check 44 35 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_44_35_10_checked :
    (Witness.linear .positive case_44_35_10).check 44 35 10 = true := by
  change case_44_35_10.check 44 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_44_35_11_checked :
    (Witness.linear .positive case_44_35_11).check 44 35 11 = true := by
  change case_44_35_11.check 44 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_44_35_12_checked :
    (Witness.linear .positive case_44_35_12).check 44 35 12 = true := by
  change case_44_35_12.check 44 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_44_35_13_checked :
    (Witness.linear .positive case_44_35_13).check 44 35 13 = true := by
  change case_44_35_13.check 44 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_44_35_14_checked :
    (Witness.linear .positive case_44_35_14).check 44 35 14 = true := by
  change case_44_35_14.check 44 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_44_35_15_checked :
    (Witness.linear .positive case_44_35_15).check 44 35 15 = true := by
  change case_44_35_15.check 44 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_44_35_16_checked :
    (Witness.linear .positive case_44_35_16).check 44 35 16 = true := by
  change case_44_35_16.check 44 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_44_35_17_checked :
    (Witness.linear .positive case_44_35_17).check 44 35 17 = true := by
  change case_44_35_17.check 44 35 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_18 : Certificate := {
  objectiveScale := 856
  eta := 1056410355
  rows := #[⟨.assumptionRow 18, 917⟩]
  caps := #[0, 0, 341797365, 109830336, 35167594, 11250090, 3602844, 1193010, 500723340, 439624185] }

theorem case_44_35_18_checked :
    (Witness.linear .conditional case_44_35_18).check 44 35 18 = true := by
  change case_44_35_18.check 44 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_19 : Certificate := {
  objectiveScale := 957
  eta := 58563175
  rows := #[⟨.assumptionRow 19, 581⟩]
  caps := #[0, 0, 23809071, 9532908, 3574641, 1589160, 585548, 1519986510, 1485553095, 1039850240] }

theorem case_44_35_19_checked :
    (Witness.linear .conditional case_44_35_19).check 44 35 19 = true := by
  change case_44_35_19.check 44 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540] }

theorem case_44_35_20_checked :
    (Witness.linear .negative case_44_35_20).check 44 35 20 = true := by
  change case_44_35_20.check 44 35 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 742900] }

theorem case_44_35_21_checked :
    (Witness.linear .negative case_44_35_21).check 44 35 21 = true := by
  change case_44_35_21.check 44 35 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_35_22_checked :
    (Witness.linear .negative case_44_35_22).check 44 35 22 = true := by
  change case_44_35_22.check 44 35 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_36_1_checked :
    (Witness.rising).check 44 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_36_2_checked :
    (Witness.rising).check 44 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_36_3_checked :
    (Witness.rising).check 44 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_36_4_checked :
    (Witness.rising).check 44 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_36_5_checked :
    (Witness.rising).check 44 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_36_6_checked :
    (Witness.rising).check 44 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_36_7_checked :
    (Witness.rising).check 44 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_36_8_checked :
    (Witness.rising).check 44 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_44_36_9_checked :
    (Witness.linear .positive case_44_36_9).check 44 36 9 = true := by
  change case_44_36_9.check 44 36 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_44_36_10_checked :
    (Witness.linear .positive case_44_36_10).check 44 36 10 = true := by
  change case_44_36_10.check 44 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_44_36_11_checked :
    (Witness.linear .positive case_44_36_11).check 44 36 11 = true := by
  change case_44_36_11.check 44 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_44_36_12_checked :
    (Witness.linear .positive case_44_36_12).check 44 36 12 = true := by
  change case_44_36_12.check 44 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_44_36_13_checked :
    (Witness.linear .positive case_44_36_13).check 44 36 13 = true := by
  change case_44_36_13.check 44 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_44_36_14_checked :
    (Witness.linear .positive case_44_36_14).check 44 36 14 = true := by
  change case_44_36_14.check 44 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_44_36_15_checked :
    (Witness.linear .positive case_44_36_15).check 44 36 15 = true := by
  change case_44_36_15.check 44 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_44_36_16_checked :
    (Witness.linear .positive case_44_36_16).check 44 36 16 = true := by
  change case_44_36_16.check 44 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_44_36_17_checked :
    (Witness.linear .positive case_44_36_17).check 44 36 17 = true := by
  change case_44_36_17.check 44 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_18 : Certificate := {
  objectiveScale := 8
  eta := 69194580
  rows := #[⟨.assumptionRow 18, 13⟩]
  caps := #[0, 0, 19684665, 5794620, 1723528, 518738, 158270, 49062, 15496] }

theorem case_44_36_18_checked :
    (Witness.linear .conditional case_44_36_18).check 44 36 18 = true := by
  change case_44_36_18.check 44 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_19 : Certificate := {
  objectiveScale := 761
  eta := 323736270
  rows := #[⟨.assumptionRow 19, 587⟩]
  caps := #[0, 0, 107075925, 39475084, 14592171, 5054304, 1900950, 1997328165, 1907026485] }

theorem case_44_36_19_checked :
    (Witness.linear .conditional case_44_36_19).check 44 36 19 = true := by
  change case_44_36_19.check 44 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405] }

theorem case_44_36_20_checked :
    (Witness.linear .negative case_44_36_20).check 44 36 20 = true := by
  change case_44_36_20.check 44 36 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 2674440] }

theorem case_44_36_21_checked :
    (Witness.linear .negative case_44_36_21).check 44 36 21 = true := by
  change case_44_36_21.check 44 36 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_36_22_checked :
    (Witness.linear .negative case_44_36_22).check 44 36 22 = true := by
  change case_44_36_22.check 44 36 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_36_23_checked :
    (Witness.linear .negative case_44_36_23).check 44 36 23 = true := by
  change case_44_36_23.check 44 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_37_1_checked :
    (Witness.rising).check 44 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_37_2_checked :
    (Witness.rising).check 44 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_37_3_checked :
    (Witness.rising).check 44 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_37_4_checked :
    (Witness.rising).check 44 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_37_5_checked :
    (Witness.rising).check 44 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_37_6_checked :
    (Witness.rising).check 44 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_37_7_checked :
    (Witness.rising).check 44 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_37_8_checked :
    (Witness.rising).check 44 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_44_37_9_checked :
    (Witness.linear .positive case_44_37_9).check 44 37 9 = true := by
  change case_44_37_9.check 44 37 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_44_37_10_checked :
    (Witness.linear .positive case_44_37_10).check 44 37 10 = true := by
  change case_44_37_10.check 44 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_44_37_11_checked :
    (Witness.linear .positive case_44_37_11).check 44 37 11 = true := by
  change case_44_37_11.check 44 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_44_37_12_checked :
    (Witness.linear .positive case_44_37_12).check 44 37 12 = true := by
  change case_44_37_12.check 44 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_44_37_13_checked :
    (Witness.linear .positive case_44_37_13).check 44 37 13 = true := by
  change case_44_37_13.check 44 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_44_37_14_checked :
    (Witness.linear .positive case_44_37_14).check 44 37 14 = true := by
  change case_44_37_14.check 44 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_44_37_15_checked :
    (Witness.linear .positive case_44_37_15).check 44 37 15 = true := by
  change case_44_37_15.check 44 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_44_37_16_checked :
    (Witness.linear .positive case_44_37_16).check 44 37 16 = true := by
  change case_44_37_16.check 44 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_44_37_17_checked :
    (Witness.linear .positive case_44_37_17).check 44 37 17 = true := by
  change case_44_37_17.check 44 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_44_37_18_checked :
    (Witness.linear .positive case_44_37_18).check 44 37 18 = true := by
  change case_44_37_18.check 44 37 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_19 : Certificate := {
  objectiveScale := 556
  eta := 744375450
  rows := #[⟨.assumptionRow 19, 503⟩]
  caps := #[0, 0, 231529155, 82031455, 28111336, 9385734, 3101550, 2467683225] }

theorem case_44_37_19_checked :
    (Witness.linear .conditional case_44_37_19).check 44 37 19 = true := by
  change case_44_37_19.check 44 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 35357670, 35357670, 25662825] }

theorem case_44_37_20_checked :
    (Witness.linear .negative case_44_37_20).check 44 37 20 = true := by
  change case_44_37_20.check 44 37 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 9694845] }

theorem case_44_37_21_checked :
    (Witness.linear .negative case_44_37_21).check 44 37 21 = true := by
  change case_44_37_21.check 44 37 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_37_22_checked :
    (Witness.linear .negative case_44_37_22).check 44 37 22 = true := by
  change case_44_37_22.check 44 37 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_37_23_checked :
    (Witness.linear .negative case_44_37_23).check 44 37 23 = true := by
  change case_44_37_23.check 44 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_44_37_24_checked :
    (Witness.linear .negative case_44_37_24).check 44 37 24 = true := by
  change case_44_37_24.check 44 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_38_1_checked :
    (Witness.rising).check 44 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_38_2_checked :
    (Witness.rising).check 44 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_38_3_checked :
    (Witness.rising).check 44 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_38_4_checked :
    (Witness.rising).check 44 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_38_5_checked :
    (Witness.rising).check 44 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_38_6_checked :
    (Witness.rising).check 44 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_38_7_checked :
    (Witness.rising).check 44 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_38_8_checked :
    (Witness.rising).check 44 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_44_38_9_checked :
    (Witness.linear .positive case_44_38_9).check 44 38 9 = true := by
  change case_44_38_9.check 44 38 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_44_38_10_checked :
    (Witness.linear .positive case_44_38_10).check 44 38 10 = true := by
  change case_44_38_10.check 44 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_44_38_11_checked :
    (Witness.linear .positive case_44_38_11).check 44 38 11 = true := by
  change case_44_38_11.check 44 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_44_38_12_checked :
    (Witness.linear .positive case_44_38_12).check 44 38 12 = true := by
  change case_44_38_12.check 44 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_44_38_13_checked :
    (Witness.linear .positive case_44_38_13).check 44 38 13 = true := by
  change case_44_38_13.check 44 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_44_38_14_checked :
    (Witness.linear .positive case_44_38_14).check 44 38 14 = true := by
  change case_44_38_14.check 44 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_44_38_15_checked :
    (Witness.linear .positive case_44_38_15).check 44 38 15 = true := by
  change case_44_38_15.check 44 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_44_38_16_checked :
    (Witness.linear .positive case_44_38_16).check 44 38 16 = true := by
  change case_44_38_16.check 44 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_44_38_17_checked :
    (Witness.linear .positive case_44_38_17).check 44 38 17 = true := by
  change case_44_38_17.check 44 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_44_38_18_checked :
    (Witness.linear .positive case_44_38_18).check 44 38 18 = true := by
  change case_44_38_18.check 44 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_44_38_19_checked :
    (Witness.linear .positive case_44_38_19).check 44 38 19 = true := by
  change case_44_38_19.check 44 38 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 129644790, 129644790, 94287120] }

theorem case_44_38_20_checked :
    (Witness.linear .negative case_44_38_20).check 44 38 20 = true := by
  change case_44_38_20.check 44 38 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 35357670] }

theorem case_44_38_21_checked :
    (Witness.linear .negative case_44_38_21).check 44 38 21 = true := by
  change case_44_38_21.check 44 38 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_44_38_22_checked :
    (Witness.linear .negative case_44_38_22).check 44 38 22 = true := by
  change case_44_38_22.check 44 38 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_44_38_23_checked :
    (Witness.linear .negative case_44_38_23).check 44 38 23 = true := by
  change case_44_38_23.check 44 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_44_38_24_checked :
    (Witness.linear .negative case_44_38_24).check 44 38 24 = true := by
  change case_44_38_24.check 44 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_39_1_checked :
    (Witness.rising).check 44 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_39_2_checked :
    (Witness.rising).check 44 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_39_3_checked :
    (Witness.rising).check 44 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_39_4_checked :
    (Witness.rising).check 44 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_39_5_checked :
    (Witness.rising).check 44 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_39_6_checked :
    (Witness.rising).check 44 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_39_7_checked :
    (Witness.rising).check 44 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_39_8_checked :
    (Witness.rising).check 44 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_44_39_9_checked :
    (Witness.linear .positive case_44_39_9).check 44 39 9 = true := by
  change case_44_39_9.check 44 39 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_44_39_10_checked :
    (Witness.linear .positive case_44_39_10).check 44 39 10 = true := by
  change case_44_39_10.check 44 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_44_39_11_checked :
    (Witness.linear .positive case_44_39_11).check 44 39 11 = true := by
  change case_44_39_11.check 44 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_44_39_12_checked :
    (Witness.linear .positive case_44_39_12).check 44 39 12 = true := by
  change case_44_39_12.check 44 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_44_39_13_checked :
    (Witness.linear .positive case_44_39_13).check 44 39 13 = true := by
  change case_44_39_13.check 44 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_44_39_14_checked :
    (Witness.linear .positive case_44_39_14).check 44 39 14 = true := by
  change case_44_39_14.check 44 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_44_39_15_checked :
    (Witness.linear .positive case_44_39_15).check 44 39 15 = true := by
  change case_44_39_15.check 44 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_44_39_16_checked :
    (Witness.linear .positive case_44_39_16).check 44 39 16 = true := by
  change case_44_39_16.check 44 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_44_39_17_checked :
    (Witness.linear .positive case_44_39_17).check 44 39 17 = true := by
  change case_44_39_17.check 44 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_44_39_18_checked :
    (Witness.linear .positive case_44_39_18).check 44 39 18 = true := by
  change case_44_39_18.check 44 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_44_39_19_checked :
    (Witness.linear .positive case_44_39_19).check 44 39 19 = true := by
  change case_44_39_19.check 44 39 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_20 : Certificate := {
  objectiveScale := 4
  eta := 3641820
  rows := #[⟨.assumptionRow 20, 3⟩]
  caps := #[0, 0, 1381380, 480700, 158631, 63954] }

theorem case_44_39_20_checked :
    (Witness.linear .conditional case_44_39_20).check 44 39 20 = true := by
  change case_44_39_20.check 44 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 129644790] }

theorem case_44_39_21_checked :
    (Witness.linear .negative case_44_39_21).check 44 39 21 = true := by
  change case_44_39_21.check 44 39 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_44_39_22_checked :
    (Witness.linear .negative case_44_39_22).check 44 39 22 = true := by
  change case_44_39_22.check 44 39 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_44_39_23_checked :
    (Witness.linear .negative case_44_39_23).check 44 39 23 = true := by
  change case_44_39_23.check 44 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_44_39_24_checked :
    (Witness.linear .negative case_44_39_24).check 44 39 24 = true := by
  change case_44_39_24.check 44 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_44_39_25_checked :
    (Witness.linear .negative case_44_39_25).check 44 39 25 = true := by
  change case_44_39_25.check 44 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_40_1_checked :
    (Witness.rising).check 44 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_40_2_checked :
    (Witness.rising).check 44 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_40_3_checked :
    (Witness.rising).check 44 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_40_4_checked :
    (Witness.rising).check 44 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_40_5_checked :
    (Witness.rising).check 44 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_40_6_checked :
    (Witness.rising).check 44 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_40_7_checked :
    (Witness.rising).check 44 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_40_8_checked :
    (Witness.rising).check 44 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_44_40_9_checked :
    (Witness.linear .positive case_44_40_9).check 44 40 9 = true := by
  change case_44_40_9.check 44 40 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_44_40_10_checked :
    (Witness.linear .positive case_44_40_10).check 44 40 10 = true := by
  change case_44_40_10.check 44 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_44_40_11_checked :
    (Witness.linear .positive case_44_40_11).check 44 40 11 = true := by
  change case_44_40_11.check 44 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_44_40_12_checked :
    (Witness.linear .positive case_44_40_12).check 44 40 12 = true := by
  change case_44_40_12.check 44 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_44_40_13_checked :
    (Witness.linear .positive case_44_40_13).check 44 40 13 = true := by
  change case_44_40_13.check 44 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_44_40_14_checked :
    (Witness.linear .positive case_44_40_14).check 44 40 14 = true := by
  change case_44_40_14.check 44 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_44_40_15_checked :
    (Witness.linear .positive case_44_40_15).check 44 40 15 = true := by
  change case_44_40_15.check 44 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_44_40_16_checked :
    (Witness.linear .positive case_44_40_16).check 44 40 16 = true := by
  change case_44_40_16.check 44 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_44_40_17_checked :
    (Witness.linear .positive case_44_40_17).check 44 40 17 = true := by
  change case_44_40_17.check 44 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_44_40_18_checked :
    (Witness.linear .positive case_44_40_18).check 44 40 18 = true := by
  change case_44_40_18.check 44 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_44_40_19_checked :
    (Witness.linear .positive case_44_40_19).check 44 40 19 = true := by
  change case_44_40_19.check 44 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_44_40_20_checked :
    (Witness.linear .positive case_44_40_20).check 44 40 20 = true := by
  change case_44_40_20.check 44 40 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 477638700] }

theorem case_44_40_21_checked :
    (Witness.linear .negative case_44_40_21).check 44 40 21 = true := by
  change case_44_40_21.check 44 40 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_44_40_22_checked :
    (Witness.linear .negative case_44_40_22).check 44 40 22 = true := by
  change case_44_40_22.check 44 40 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_44_40_23_checked :
    (Witness.linear .negative case_44_40_23).check 44 40 23 = true := by
  change case_44_40_23.check 44 40 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_44_40_24_checked :
    (Witness.linear .negative case_44_40_24).check 44 40 24 = true := by
  change case_44_40_24.check 44 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_44_40_25_checked :
    (Witness.linear .negative case_44_40_25).check 44 40 25 = true := by
  change case_44_40_25.check 44 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_44_40_26_checked :
    (Witness.linear .negative case_44_40_26).check 44 40 26 = true := by
  change case_44_40_26.check 44 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_41_1_checked :
    (Witness.rising).check 44 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_41_2_checked :
    (Witness.rising).check 44 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_41_3_checked :
    (Witness.rising).check 44 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_41_4_checked :
    (Witness.rising).check 44 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_41_5_checked :
    (Witness.rising).check 44 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_41_6_checked :
    (Witness.rising).check 44 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_41_7_checked :
    (Witness.rising).check 44 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_41_8_checked :
    (Witness.rising).check 44 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_44_41_9_checked :
    (Witness.linear .positive case_44_41_9).check 44 41 9 = true := by
  change case_44_41_9.check 44 41 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_44_41_10_checked :
    (Witness.linear .positive case_44_41_10).check 44 41 10 = true := by
  change case_44_41_10.check 44 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_44_41_11_checked :
    (Witness.linear .positive case_44_41_11).check 44 41 11 = true := by
  change case_44_41_11.check 44 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_44_41_12_checked :
    (Witness.linear .positive case_44_41_12).check 44 41 12 = true := by
  change case_44_41_12.check 44 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_44_41_13_checked :
    (Witness.linear .positive case_44_41_13).check 44 41 13 = true := by
  change case_44_41_13.check 44 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_44_41_14_checked :
    (Witness.linear .positive case_44_41_14).check 44 41 14 = true := by
  change case_44_41_14.check 44 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_44_41_15_checked :
    (Witness.linear .positive case_44_41_15).check 44 41 15 = true := by
  change case_44_41_15.check 44 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_44_41_16_checked :
    (Witness.linear .positive case_44_41_16).check 44 41 16 = true := by
  change case_44_41_16.check 44 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_44_41_17_checked :
    (Witness.linear .positive case_44_41_17).check 44 41 17 = true := by
  change case_44_41_17.check 44 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_44_41_18_checked :
    (Witness.linear .positive case_44_41_18).check 44 41 18 = true := by
  change case_44_41_18.check 44 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_44_41_19_checked :
    (Witness.linear .positive case_44_41_19).check 44 41 19 = true := by
  change case_44_41_19.check 44 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_44_41_20_checked :
    (Witness.linear .positive case_44_41_20).check 44 41 20 = true := by
  change case_44_41_20.check 44 41 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 1767263190] }

theorem case_44_41_21_checked :
    (Witness.linear .negative case_44_41_21).check 44 41 21 = true := by
  change case_44_41_21.check 44 41 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_44_41_22_checked :
    (Witness.linear .negative case_44_41_22).check 44 41 22 = true := by
  change case_44_41_22.check 44 41 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_44_41_23_checked :
    (Witness.linear .negative case_44_41_23).check 44 41 23 = true := by
  change case_44_41_23.check 44 41 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_44_41_24_checked :
    (Witness.linear .negative case_44_41_24).check 44 41 24 = true := by
  change case_44_41_24.check 44 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_44_41_25_checked :
    (Witness.linear .negative case_44_41_25).check 44 41 25 = true := by
  change case_44_41_25.check 44 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_44_41_26_checked :
    (Witness.linear .negative case_44_41_26).check 44 41 26 = true := by
  change case_44_41_26.check 44 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_42_1_checked :
    (Witness.rising).check 44 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_42_2_checked :
    (Witness.rising).check 44 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_42_3_checked :
    (Witness.rising).check 44 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_42_4_checked :
    (Witness.rising).check 44 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_42_5_checked :
    (Witness.rising).check 44 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_42_6_checked :
    (Witness.rising).check 44 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_42_7_checked :
    (Witness.rising).check 44 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_42_8_checked :
    (Witness.rising).check 44 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_44_42_9_checked :
    (Witness.linear .positive case_44_42_9).check 44 42 9 = true := by
  change case_44_42_9.check 44 42 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_44_42_10_checked :
    (Witness.linear .positive case_44_42_10).check 44 42 10 = true := by
  change case_44_42_10.check 44 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_44_42_11_checked :
    (Witness.linear .positive case_44_42_11).check 44 42 11 = true := by
  change case_44_42_11.check 44 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_44_42_12_checked :
    (Witness.linear .positive case_44_42_12).check 44 42 12 = true := by
  change case_44_42_12.check 44 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_44_42_13_checked :
    (Witness.linear .positive case_44_42_13).check 44 42 13 = true := by
  change case_44_42_13.check 44 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_44_42_14_checked :
    (Witness.linear .positive case_44_42_14).check 44 42 14 = true := by
  change case_44_42_14.check 44 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_44_42_15_checked :
    (Witness.linear .positive case_44_42_15).check 44 42 15 = true := by
  change case_44_42_15.check 44 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_44_42_16_checked :
    (Witness.linear .positive case_44_42_16).check 44 42 16 = true := by
  change case_44_42_16.check 44 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_44_42_17_checked :
    (Witness.linear .positive case_44_42_17).check 44 42 17 = true := by
  change case_44_42_17.check 44 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_44_42_18_checked :
    (Witness.linear .positive case_44_42_18).check 44 42 18 = true := by
  change case_44_42_18.check 44 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_44_42_19_checked :
    (Witness.linear .positive case_44_42_19).check 44 42 19 = true := by
  change case_44_42_19.check 44 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_44_42_20_checked :
    (Witness.linear .positive case_44_42_20).check 44 42 20 = true := by
  change case_44_42_20.check 44 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_44_42_21_checked :
    (Witness.linear .positive case_44_42_21).check 44 42 21 = true := by
  change case_44_42_21.check 44 42 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_44_42_22_checked :
    (Witness.linear .negative case_44_42_22).check 44 42 22 = true := by
  change case_44_42_22.check 44 42 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_44_42_23_checked :
    (Witness.linear .negative case_44_42_23).check 44 42 23 = true := by
  change case_44_42_23.check 44 42 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_44_42_24_checked :
    (Witness.linear .negative case_44_42_24).check 44 42 24 = true := by
  change case_44_42_24.check 44 42 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_44_42_25_checked :
    (Witness.linear .negative case_44_42_25).check 44 42 25 = true := by
  change case_44_42_25.check 44 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_44_42_26_checked :
    (Witness.linear .negative case_44_42_26).check 44 42 26 = true := by
  change case_44_42_26.check 44 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_44_42_27_checked :
    (Witness.linear .negative case_44_42_27).check 44 42 27 = true := by
  change case_44_42_27.check 44 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_43_1_checked :
    (Witness.rising).check 44 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_43_2_checked :
    (Witness.rising).check 44 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_43_3_checked :
    (Witness.rising).check 44 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_43_4_checked :
    (Witness.rising).check 44 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_43_5_checked :
    (Witness.rising).check 44 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_43_6_checked :
    (Witness.rising).check 44 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_43_7_checked :
    (Witness.rising).check 44 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_44_43_8_checked :
    (Witness.rising).check 44 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_9_checked :
    (Witness.linear .positive case_44_43_9).check 44 43 9 = true := by
  change case_44_43_9.check 44 43 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_10_checked :
    (Witness.linear .positive case_44_43_10).check 44 43 10 = true := by
  change case_44_43_10.check 44 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_11_checked :
    (Witness.linear .positive case_44_43_11).check 44 43 11 = true := by
  change case_44_43_11.check 44 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_12_checked :
    (Witness.linear .positive case_44_43_12).check 44 43 12 = true := by
  change case_44_43_12.check 44 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_13_checked :
    (Witness.linear .positive case_44_43_13).check 44 43 13 = true := by
  change case_44_43_13.check 44 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_14_checked :
    (Witness.linear .positive case_44_43_14).check 44 43 14 = true := by
  change case_44_43_14.check 44 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_15_checked :
    (Witness.linear .positive case_44_43_15).check 44 43 15 = true := by
  change case_44_43_15.check 44 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_16_checked :
    (Witness.linear .positive case_44_43_16).check 44 43 16 = true := by
  change case_44_43_16.check 44 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_17_checked :
    (Witness.linear .positive case_44_43_17).check 44 43 17 = true := by
  change case_44_43_17.check 44 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_18_checked :
    (Witness.linear .positive case_44_43_18).check 44 43 18 = true := by
  change case_44_43_18.check 44 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_19_checked :
    (Witness.linear .positive case_44_43_19).check 44 43 19 = true := by
  change case_44_43_19.check 44 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_20_checked :
    (Witness.linear .positive case_44_43_20).check 44 43 20 = true := by
  change case_44_43_20.check 44 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_21_checked :
    (Witness.linear .positive case_44_43_21).check 44 43 21 = true := by
  change case_44_43_21.check 44 43 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_22_checked :
    (Witness.linear .negative case_44_43_22).check 44 43 22 = true := by
  change case_44_43_22.check 44 43 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_23_checked :
    (Witness.linear .negative case_44_43_23).check 44 43 23 = true := by
  change case_44_43_23.check 44 43 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_24_checked :
    (Witness.linear .negative case_44_43_24).check 44 43 24 = true := by
  change case_44_43_24.check 44 43 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_25_checked :
    (Witness.linear .negative case_44_43_25).check 44 43 25 = true := by
  change case_44_43_25.check 44 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_26_checked :
    (Witness.linear .negative case_44_43_26).check 44 43 26 = true := by
  change case_44_43_26.check 44 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_27_checked :
    (Witness.linear .negative case_44_43_27).check 44 43 27 = true := by
  change case_44_43_27.check 44 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_44_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_44_43_28_checked :
    (Witness.linear .negative case_44_43_28).check 44 43 28 = true := by
  change case_44_43_28.check 44 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_44 (a k : ℕ) (h : Domain 44 a k) :
    ∃ w : Witness, w.check 44 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 22 ≤ a := by omega
  have haHi : a ≤ 43 := by omega
  interval_cases a

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_22_1_checked⟩

    · exact ⟨Witness.rising, case_44_22_2_checked⟩

    · exact ⟨Witness.rising, case_44_22_3_checked⟩

    · exact ⟨Witness.rising, case_44_22_4_checked⟩

    · exact ⟨Witness.rising, case_44_22_5_checked⟩

    · exact ⟨Witness.rising, case_44_22_6_checked⟩

    · exact ⟨Witness.rising, case_44_22_7_checked⟩

    · exact ⟨Witness.rising, case_44_22_8_checked⟩

    · exact ⟨Witness.rising, case_44_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_22_10, case_44_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_22_11, case_44_22_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_22_12, case_44_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_44_22_13, case_44_22_13_checked⟩

    · exact ⟨Witness.linear .conditional case_44_22_14, case_44_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_23_1_checked⟩

    · exact ⟨Witness.rising, case_44_23_2_checked⟩

    · exact ⟨Witness.rising, case_44_23_3_checked⟩

    · exact ⟨Witness.rising, case_44_23_4_checked⟩

    · exact ⟨Witness.rising, case_44_23_5_checked⟩

    · exact ⟨Witness.rising, case_44_23_6_checked⟩

    · exact ⟨Witness.rising, case_44_23_7_checked⟩

    · exact ⟨Witness.rising, case_44_23_8_checked⟩

    · exact ⟨Witness.rising, case_44_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_23_10, case_44_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_23_11, case_44_23_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_23_12, case_44_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_44_23_13, case_44_23_13_checked⟩

    · exact ⟨Witness.linear .conditional case_44_23_14, case_44_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_24_1_checked⟩

    · exact ⟨Witness.rising, case_44_24_2_checked⟩

    · exact ⟨Witness.rising, case_44_24_3_checked⟩

    · exact ⟨Witness.rising, case_44_24_4_checked⟩

    · exact ⟨Witness.rising, case_44_24_5_checked⟩

    · exact ⟨Witness.rising, case_44_24_6_checked⟩

    · exact ⟨Witness.rising, case_44_24_7_checked⟩

    · exact ⟨Witness.rising, case_44_24_8_checked⟩

    · exact ⟨Witness.rising, case_44_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_24_10, case_44_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_24_11, case_44_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_24_12, case_44_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_44_24_13, case_44_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_44_24_14, case_44_24_14_checked⟩

    · exact ⟨Witness.linear .conditional case_44_24_15, case_44_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_25_1_checked⟩

    · exact ⟨Witness.rising, case_44_25_2_checked⟩

    · exact ⟨Witness.rising, case_44_25_3_checked⟩

    · exact ⟨Witness.rising, case_44_25_4_checked⟩

    · exact ⟨Witness.rising, case_44_25_5_checked⟩

    · exact ⟨Witness.rising, case_44_25_6_checked⟩

    · exact ⟨Witness.rising, case_44_25_7_checked⟩

    · exact ⟨Witness.rising, case_44_25_8_checked⟩

    · exact ⟨Witness.rising, case_44_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_25_10, case_44_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_25_11, case_44_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_25_12, case_44_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_44_25_13, case_44_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_44_25_14, case_44_25_14_checked⟩

    · exact ⟨Witness.linear .conditional case_44_25_15, case_44_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_44_25_16, case_44_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_26_1_checked⟩

    · exact ⟨Witness.rising, case_44_26_2_checked⟩

    · exact ⟨Witness.rising, case_44_26_3_checked⟩

    · exact ⟨Witness.rising, case_44_26_4_checked⟩

    · exact ⟨Witness.rising, case_44_26_5_checked⟩

    · exact ⟨Witness.rising, case_44_26_6_checked⟩

    · exact ⟨Witness.rising, case_44_26_7_checked⟩

    · exact ⟨Witness.rising, case_44_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_26_9, case_44_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_26_10, case_44_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_26_11, case_44_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_26_12, case_44_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_26_13, case_44_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_44_26_14, case_44_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_44_26_15, case_44_26_15_checked⟩

    · exact ⟨Witness.linear .conditional case_44_26_16, case_44_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_27_1_checked⟩

    · exact ⟨Witness.rising, case_44_27_2_checked⟩

    · exact ⟨Witness.rising, case_44_27_3_checked⟩

    · exact ⟨Witness.rising, case_44_27_4_checked⟩

    · exact ⟨Witness.rising, case_44_27_5_checked⟩

    · exact ⟨Witness.rising, case_44_27_6_checked⟩

    · exact ⟨Witness.rising, case_44_27_7_checked⟩

    · exact ⟨Witness.rising, case_44_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_27_9, case_44_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_27_10, case_44_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_27_11, case_44_27_11_checked⟩

    · exact ⟨Witness.linear .conditional case_44_27_12, case_44_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_27_13, case_44_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_44_27_14, case_44_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_44_27_15, case_44_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_44_27_16, case_44_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_44_27_17, case_44_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_28_1_checked⟩

    · exact ⟨Witness.rising, case_44_28_2_checked⟩

    · exact ⟨Witness.rising, case_44_28_3_checked⟩

    · exact ⟨Witness.rising, case_44_28_4_checked⟩

    · exact ⟨Witness.rising, case_44_28_5_checked⟩

    · exact ⟨Witness.rising, case_44_28_6_checked⟩

    · exact ⟨Witness.rising, case_44_28_7_checked⟩

    · exact ⟨Witness.rising, case_44_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_28_9, case_44_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_28_10, case_44_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_28_11, case_44_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_28_12, case_44_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_28_13, case_44_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_44_28_14, case_44_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_44_28_15, case_44_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_44_28_16, case_44_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_44_28_17, case_44_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_44_28_18, case_44_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_29_1_checked⟩

    · exact ⟨Witness.rising, case_44_29_2_checked⟩

    · exact ⟨Witness.rising, case_44_29_3_checked⟩

    · exact ⟨Witness.rising, case_44_29_4_checked⟩

    · exact ⟨Witness.rising, case_44_29_5_checked⟩

    · exact ⟨Witness.rising, case_44_29_6_checked⟩

    · exact ⟨Witness.rising, case_44_29_7_checked⟩

    · exact ⟨Witness.rising, case_44_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_29_9, case_44_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_29_10, case_44_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_29_11, case_44_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_29_12, case_44_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_29_13, case_44_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_29_14, case_44_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_44_29_15, case_44_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_44_29_16, case_44_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_44_29_17, case_44_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_44_29_18, case_44_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_30_1_checked⟩

    · exact ⟨Witness.rising, case_44_30_2_checked⟩

    · exact ⟨Witness.rising, case_44_30_3_checked⟩

    · exact ⟨Witness.rising, case_44_30_4_checked⟩

    · exact ⟨Witness.rising, case_44_30_5_checked⟩

    · exact ⟨Witness.rising, case_44_30_6_checked⟩

    · exact ⟨Witness.rising, case_44_30_7_checked⟩

    · exact ⟨Witness.rising, case_44_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_30_9, case_44_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_30_10, case_44_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_30_11, case_44_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_30_12, case_44_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_30_13, case_44_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_30_14, case_44_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_44_30_15, case_44_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_44_30_16, case_44_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_44_30_17, case_44_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_44_30_18, case_44_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_44_30_19, case_44_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_31_1_checked⟩

    · exact ⟨Witness.rising, case_44_31_2_checked⟩

    · exact ⟨Witness.rising, case_44_31_3_checked⟩

    · exact ⟨Witness.rising, case_44_31_4_checked⟩

    · exact ⟨Witness.rising, case_44_31_5_checked⟩

    · exact ⟨Witness.rising, case_44_31_6_checked⟩

    · exact ⟨Witness.rising, case_44_31_7_checked⟩

    · exact ⟨Witness.rising, case_44_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_31_9, case_44_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_31_10, case_44_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_31_11, case_44_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_31_12, case_44_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_31_13, case_44_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_31_14, case_44_31_14_checked⟩

    · exact ⟨Witness.linear .conditional case_44_31_15, case_44_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_44_31_16, case_44_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_44_31_17, case_44_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_44_31_18, case_44_31_18_checked⟩

    · exact ⟨Witness.linear .conditional case_44_31_19, case_44_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_44_31_20, case_44_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_32_1_checked⟩

    · exact ⟨Witness.rising, case_44_32_2_checked⟩

    · exact ⟨Witness.rising, case_44_32_3_checked⟩

    · exact ⟨Witness.rising, case_44_32_4_checked⟩

    · exact ⟨Witness.rising, case_44_32_5_checked⟩

    · exact ⟨Witness.rising, case_44_32_6_checked⟩

    · exact ⟨Witness.rising, case_44_32_7_checked⟩

    · exact ⟨Witness.rising, case_44_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_32_9, case_44_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_32_10, case_44_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_32_11, case_44_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_32_12, case_44_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_32_13, case_44_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_32_14, case_44_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_32_15, case_44_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_44_32_16, case_44_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_44_32_17, case_44_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_44_32_18, case_44_32_18_checked⟩

    · exact ⟨Witness.linear .conditional case_44_32_19, case_44_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_44_32_20, case_44_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_33_1_checked⟩

    · exact ⟨Witness.rising, case_44_33_2_checked⟩

    · exact ⟨Witness.rising, case_44_33_3_checked⟩

    · exact ⟨Witness.rising, case_44_33_4_checked⟩

    · exact ⟨Witness.rising, case_44_33_5_checked⟩

    · exact ⟨Witness.rising, case_44_33_6_checked⟩

    · exact ⟨Witness.rising, case_44_33_7_checked⟩

    · exact ⟨Witness.rising, case_44_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_33_9, case_44_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_33_10, case_44_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_33_11, case_44_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_33_12, case_44_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_33_13, case_44_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_33_14, case_44_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_33_15, case_44_33_15_checked⟩

    · exact ⟨Witness.linear .conditional case_44_33_16, case_44_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_44_33_17, case_44_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_44_33_18, case_44_33_18_checked⟩

    · exact ⟨Witness.linear .conditional case_44_33_19, case_44_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_44_33_20, case_44_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_44_33_21, case_44_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_34_1_checked⟩

    · exact ⟨Witness.rising, case_44_34_2_checked⟩

    · exact ⟨Witness.rising, case_44_34_3_checked⟩

    · exact ⟨Witness.rising, case_44_34_4_checked⟩

    · exact ⟨Witness.rising, case_44_34_5_checked⟩

    · exact ⟨Witness.rising, case_44_34_6_checked⟩

    · exact ⟨Witness.rising, case_44_34_7_checked⟩

    · exact ⟨Witness.rising, case_44_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_34_9, case_44_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_34_10, case_44_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_34_11, case_44_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_34_12, case_44_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_34_13, case_44_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_34_14, case_44_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_34_15, case_44_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_44_34_16, case_44_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_44_34_17, case_44_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_44_34_18, case_44_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_44_34_19, case_44_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_44_34_20, case_44_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_44_34_21, case_44_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_44_34_22, case_44_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_35_1_checked⟩

    · exact ⟨Witness.rising, case_44_35_2_checked⟩

    · exact ⟨Witness.rising, case_44_35_3_checked⟩

    · exact ⟨Witness.rising, case_44_35_4_checked⟩

    · exact ⟨Witness.rising, case_44_35_5_checked⟩

    · exact ⟨Witness.rising, case_44_35_6_checked⟩

    · exact ⟨Witness.rising, case_44_35_7_checked⟩

    · exact ⟨Witness.rising, case_44_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_35_9, case_44_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_35_10, case_44_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_35_11, case_44_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_35_12, case_44_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_35_13, case_44_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_35_14, case_44_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_35_15, case_44_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_44_35_16, case_44_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_44_35_17, case_44_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_44_35_18, case_44_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_44_35_19, case_44_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_44_35_20, case_44_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_44_35_21, case_44_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_44_35_22, case_44_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_36_1_checked⟩

    · exact ⟨Witness.rising, case_44_36_2_checked⟩

    · exact ⟨Witness.rising, case_44_36_3_checked⟩

    · exact ⟨Witness.rising, case_44_36_4_checked⟩

    · exact ⟨Witness.rising, case_44_36_5_checked⟩

    · exact ⟨Witness.rising, case_44_36_6_checked⟩

    · exact ⟨Witness.rising, case_44_36_7_checked⟩

    · exact ⟨Witness.rising, case_44_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_36_9, case_44_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_36_10, case_44_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_36_11, case_44_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_36_12, case_44_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_36_13, case_44_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_36_14, case_44_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_36_15, case_44_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_44_36_16, case_44_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_44_36_17, case_44_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_44_36_18, case_44_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_44_36_19, case_44_36_19_checked⟩

    · exact ⟨Witness.linear .negative case_44_36_20, case_44_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_44_36_21, case_44_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_44_36_22, case_44_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_44_36_23, case_44_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_37_1_checked⟩

    · exact ⟨Witness.rising, case_44_37_2_checked⟩

    · exact ⟨Witness.rising, case_44_37_3_checked⟩

    · exact ⟨Witness.rising, case_44_37_4_checked⟩

    · exact ⟨Witness.rising, case_44_37_5_checked⟩

    · exact ⟨Witness.rising, case_44_37_6_checked⟩

    · exact ⟨Witness.rising, case_44_37_7_checked⟩

    · exact ⟨Witness.rising, case_44_37_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_37_9, case_44_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_37_10, case_44_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_37_11, case_44_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_37_12, case_44_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_37_13, case_44_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_37_14, case_44_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_37_15, case_44_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_44_37_16, case_44_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_44_37_17, case_44_37_17_checked⟩

    · exact ⟨Witness.linear .positive case_44_37_18, case_44_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_44_37_19, case_44_37_19_checked⟩

    · exact ⟨Witness.linear .negative case_44_37_20, case_44_37_20_checked⟩

    · exact ⟨Witness.linear .negative case_44_37_21, case_44_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_44_37_22, case_44_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_44_37_23, case_44_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_44_37_24, case_44_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_38_1_checked⟩

    · exact ⟨Witness.rising, case_44_38_2_checked⟩

    · exact ⟨Witness.rising, case_44_38_3_checked⟩

    · exact ⟨Witness.rising, case_44_38_4_checked⟩

    · exact ⟨Witness.rising, case_44_38_5_checked⟩

    · exact ⟨Witness.rising, case_44_38_6_checked⟩

    · exact ⟨Witness.rising, case_44_38_7_checked⟩

    · exact ⟨Witness.rising, case_44_38_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_38_9, case_44_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_38_10, case_44_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_38_11, case_44_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_38_12, case_44_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_38_13, case_44_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_38_14, case_44_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_38_15, case_44_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_44_38_16, case_44_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_44_38_17, case_44_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_44_38_18, case_44_38_18_checked⟩

    · exact ⟨Witness.linear .positive case_44_38_19, case_44_38_19_checked⟩

    · exact ⟨Witness.linear .negative case_44_38_20, case_44_38_20_checked⟩

    · exact ⟨Witness.linear .negative case_44_38_21, case_44_38_21_checked⟩

    · exact ⟨Witness.linear .negative case_44_38_22, case_44_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_44_38_23, case_44_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_44_38_24, case_44_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_39_1_checked⟩

    · exact ⟨Witness.rising, case_44_39_2_checked⟩

    · exact ⟨Witness.rising, case_44_39_3_checked⟩

    · exact ⟨Witness.rising, case_44_39_4_checked⟩

    · exact ⟨Witness.rising, case_44_39_5_checked⟩

    · exact ⟨Witness.rising, case_44_39_6_checked⟩

    · exact ⟨Witness.rising, case_44_39_7_checked⟩

    · exact ⟨Witness.rising, case_44_39_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_39_9, case_44_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_39_10, case_44_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_39_11, case_44_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_39_12, case_44_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_39_13, case_44_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_39_14, case_44_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_39_15, case_44_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_44_39_16, case_44_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_44_39_17, case_44_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_44_39_18, case_44_39_18_checked⟩

    · exact ⟨Witness.linear .positive case_44_39_19, case_44_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_44_39_20, case_44_39_20_checked⟩

    · exact ⟨Witness.linear .negative case_44_39_21, case_44_39_21_checked⟩

    · exact ⟨Witness.linear .negative case_44_39_22, case_44_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_44_39_23, case_44_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_44_39_24, case_44_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_44_39_25, case_44_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_40_1_checked⟩

    · exact ⟨Witness.rising, case_44_40_2_checked⟩

    · exact ⟨Witness.rising, case_44_40_3_checked⟩

    · exact ⟨Witness.rising, case_44_40_4_checked⟩

    · exact ⟨Witness.rising, case_44_40_5_checked⟩

    · exact ⟨Witness.rising, case_44_40_6_checked⟩

    · exact ⟨Witness.rising, case_44_40_7_checked⟩

    · exact ⟨Witness.rising, case_44_40_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_9, case_44_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_10, case_44_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_11, case_44_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_12, case_44_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_13, case_44_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_14, case_44_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_15, case_44_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_16, case_44_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_17, case_44_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_18, case_44_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_19, case_44_40_19_checked⟩

    · exact ⟨Witness.linear .positive case_44_40_20, case_44_40_20_checked⟩

    · exact ⟨Witness.linear .negative case_44_40_21, case_44_40_21_checked⟩

    · exact ⟨Witness.linear .negative case_44_40_22, case_44_40_22_checked⟩

    · exact ⟨Witness.linear .negative case_44_40_23, case_44_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_44_40_24, case_44_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_44_40_25, case_44_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_44_40_26, case_44_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_41_1_checked⟩

    · exact ⟨Witness.rising, case_44_41_2_checked⟩

    · exact ⟨Witness.rising, case_44_41_3_checked⟩

    · exact ⟨Witness.rising, case_44_41_4_checked⟩

    · exact ⟨Witness.rising, case_44_41_5_checked⟩

    · exact ⟨Witness.rising, case_44_41_6_checked⟩

    · exact ⟨Witness.rising, case_44_41_7_checked⟩

    · exact ⟨Witness.rising, case_44_41_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_9, case_44_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_10, case_44_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_11, case_44_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_12, case_44_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_13, case_44_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_14, case_44_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_15, case_44_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_16, case_44_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_17, case_44_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_18, case_44_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_19, case_44_41_19_checked⟩

    · exact ⟨Witness.linear .positive case_44_41_20, case_44_41_20_checked⟩

    · exact ⟨Witness.linear .negative case_44_41_21, case_44_41_21_checked⟩

    · exact ⟨Witness.linear .negative case_44_41_22, case_44_41_22_checked⟩

    · exact ⟨Witness.linear .negative case_44_41_23, case_44_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_44_41_24, case_44_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_44_41_25, case_44_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_44_41_26, case_44_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_42_1_checked⟩

    · exact ⟨Witness.rising, case_44_42_2_checked⟩

    · exact ⟨Witness.rising, case_44_42_3_checked⟩

    · exact ⟨Witness.rising, case_44_42_4_checked⟩

    · exact ⟨Witness.rising, case_44_42_5_checked⟩

    · exact ⟨Witness.rising, case_44_42_6_checked⟩

    · exact ⟨Witness.rising, case_44_42_7_checked⟩

    · exact ⟨Witness.rising, case_44_42_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_9, case_44_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_10, case_44_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_11, case_44_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_12, case_44_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_13, case_44_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_14, case_44_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_15, case_44_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_16, case_44_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_17, case_44_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_18, case_44_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_19, case_44_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_20, case_44_42_20_checked⟩

    · exact ⟨Witness.linear .positive case_44_42_21, case_44_42_21_checked⟩

    · exact ⟨Witness.linear .negative case_44_42_22, case_44_42_22_checked⟩

    · exact ⟨Witness.linear .negative case_44_42_23, case_44_42_23_checked⟩

    · exact ⟨Witness.linear .negative case_44_42_24, case_44_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_44_42_25, case_44_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_44_42_26, case_44_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_44_42_27, case_44_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_44_43_1_checked⟩

    · exact ⟨Witness.rising, case_44_43_2_checked⟩

    · exact ⟨Witness.rising, case_44_43_3_checked⟩

    · exact ⟨Witness.rising, case_44_43_4_checked⟩

    · exact ⟨Witness.rising, case_44_43_5_checked⟩

    · exact ⟨Witness.rising, case_44_43_6_checked⟩

    · exact ⟨Witness.rising, case_44_43_7_checked⟩

    · exact ⟨Witness.rising, case_44_43_8_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_9, case_44_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_10, case_44_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_11, case_44_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_12, case_44_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_13, case_44_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_14, case_44_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_15, case_44_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_16, case_44_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_17, case_44_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_18, case_44_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_19, case_44_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_20, case_44_43_20_checked⟩

    · exact ⟨Witness.linear .positive case_44_43_21, case_44_43_21_checked⟩

    · exact ⟨Witness.linear .negative case_44_43_22, case_44_43_22_checked⟩

    · exact ⟨Witness.linear .negative case_44_43_23, case_44_43_23_checked⟩

    · exact ⟨Witness.linear .negative case_44_43_24, case_44_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_44_43_25, case_44_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_44_43_26, case_44_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_44_43_27, case_44_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_44_43_28, case_44_43_28_checked⟩


#print axioms coverage_44
end ForestUnimodality.FiniteRows.FiniteData
