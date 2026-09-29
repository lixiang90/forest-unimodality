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

theorem case_31_16_1_checked :
    (Witness.rising).check 31 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_16_2_checked :
    (Witness.rising).check 31 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_16_3_checked :
    (Witness.rising).check 31 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_16_4_checked :
    (Witness.rising).check 31 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_16_5_checked :
    (Witness.rising).check 31 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_16_6_checked :
    (Witness.rising).check 31 16 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_16_7_checked :
    (Witness.rising).check 31 16 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_16_8 : Certificate := {
  objectiveScale := 350702352000
  eta := 343154360629080
  rows := #[⟨.count 2, 84001980862800⟩, ⟨.count 3, 14350740243840⟩, ⟨.count 4, 3259778361840⟩, ⟨.count 5, 942512571000⟩, ⟨.count 6, 386649343080⟩, ⟨.count 7, 349825596120⟩, ⟨.path 8, 36035599600⟩, ⟨.path 9, 95213253135⟩, ⟨.privateRow 8 0, 16678656995⟩, ⟨.privateRow 9 0, 11909267370⟩, ⟨.hall 6 3, 3112483374⟩, ⟨.hall 9 4, 6337692504⟩, ⟨.hall 5 5, 1984719750⟩, ⟨.hall 4 8, 4062302244⟩, ⟨.hall 7 8, 3636913280⟩, ⟨.hall 3 12, 398384383320⟩]
  caps := #[0, 0, 0, 0, 945939995, 0, 88608520, 876755880, 750234485, 0, 0, 0, 0, 0, 0, 0] }

theorem case_31_16_8_checked :
    (Witness.linear .positive case_31_16_8).check 31 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_16_9 : Certificate := {
  objectiveScale := 221760000
  eta := 1600266507840
  rows := #[⟨.count 2, 480051411840⟩, ⟨.count 3, 97147512000⟩, ⟨.count 4, 23286130560⟩, ⟨.count 5, 7005398400⟩, ⟨.count 6, 2460870720⟩, ⟨.count 7, 1341204480⟩, ⟨.count 8, 1311710400⟩, ⟨.path 10, 383090400⟩, ⟨.privateRow 4 12, 1247732640⟩, ⟨.privateRow 7 3, 6716160⟩, ⟨.privateRow 8 1, 28548135⟩, ⟨.privateRow 9 0, 98433720⟩, ⟨.privateRow 10 0, 86391360⟩, ⟨.hall 7 3, 18369120⟩, ⟨.hall 6 5, 17981568⟩, ⟨.hall 7 5, 264880⟩, ⟨.hall 5 7, 29126160⟩, ⟨.hall 6 8, 5610528⟩, ⟨.hall 4 9, 59864112⟩, ⟨.assumptionRow 9, 1340821440⟩]
  caps := #[0, 0, 21621600, 0, 2620800, 3049200, 0, 0, 1283345, 50400, 110880, 0, 0, 0, 0, 0] }

theorem case_31_16_9_checked :
    (Witness.linear .conditional case_31_16_9).check 31 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_16_10 : Certificate := {
  objectiveScale := 487086600000
  eta := 279964810845720
  rows := #[⟨.count 2, 73971893595600⟩, ⟨.count 3, 22857025791600⟩, ⟨.count 4, 7657585855920⟩, ⟨.count 5, 2836305271800⟩, ⟨.count 6, 1186250705640⟩, ⟨.count 7, 556447731840⟩, ⟨.count 8, 429610381200⟩, ⟨.count 9, 299850510960⟩, ⟨.count 11, 491860048680⟩, ⟨.path 8, 128237909800⟩, ⟨.privateRow 10 0, 35007609780⟩, ⟨.hall 8 2, 11300409120⟩, ⟨.hall 7 3, 9656491845⟩, ⟨.hall 8 3, 12844473642⟩, ⟨.hall 7 4, 1292403112⟩, ⟨.hall 6 5, 23841497394⟩, ⟨.hall 7 5, 17332164850⟩, ⟨.hall 5 7, 20929225590⟩, ⟨.hall 5 9, 215562388860⟩, ⟨.hall 4 10, 544392338490⟩, ⟨.hall 3 11, 492972854220⟩, ⟨.hall 2 13, 3376199017620⟩, ⟨.assumptionRow 10, 300902618016⟩]
  caps := #[0, 389509280160, 0, 8668099440, 2694395088, 1143486344, 0, 930705776, 0, 2479270794, 0, 0, 0, 0, 0, 0] }

theorem case_31_16_10_checked :
    (Witness.linear .conditional case_31_16_10).check 31 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_17_1_checked :
    (Witness.rising).check 31 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_17_2_checked :
    (Witness.rising).check 31 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_17_3_checked :
    (Witness.rising).check 31 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_17_4_checked :
    (Witness.rising).check 31 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_17_5_checked :
    (Witness.rising).check 31 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_17_6_checked :
    (Witness.rising).check 31 17 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_17_7_checked :
    (Witness.rising).check 31 17 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_17_8 : Certificate := {
  objectiveScale := 75600000
  eta := 95771255580
  rows := #[⟨.count 2, 18515657160⟩, ⟨.count 3, 3326753430⟩, ⟨.count 4, 755674920⟩, ⟨.count 5, 212432220⟩, ⟨.count 6, 86486400⟩, ⟨.count 7, 75675600⟩, ⟨.path 8, 10798920⟩, ⟨.path 9, 18000360⟩, ⟨.privateRow 7 4, 1814670⟩, ⟨.privateRow 8 1, 1846845⟩, ⟨.privateRow 9 0, 2002000⟩, ⟨.hall 7 2, 306306⟩, ⟨.hall 6 4, 201240⟩, ⟨.hall 5 5, 262080⟩, ⟨.hall 4 8, 357336⟩]
  caps := #[0, 0, 15135120, 0, 294840, 0, 0, 913815, 0, 0, 0, 0, 0, 0, 0] }

theorem case_31_17_8_checked :
    (Witness.linear .positive case_31_17_8).check 31 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_17_9 : Certificate := {
  objectiveScale := 226800000
  eta := 324648324000
  rows := #[⟨.count 2, 72921008160⟩, ⟨.count 3, 18694035360⟩, ⟨.count 4, 4761076320⟩, ⟨.count 5, 1472430960⟩, ⟨.count 6, 510269760⟩, ⟨.count 7, 227026800⟩, ⟨.count 8, 224864640⟩, ⟨.path 10, 56700000⟩, ⟨.privateRow 9 0, 1521520⟩, ⟨.privateRow 10 0, 7135128⟩, ⟨.hall 8 2, 1781780⟩, ⟨.hall 10 3, 3150576⟩, ⟨.hall 7 4, 2303301⟩, ⟨.hall 5 7, 4782960⟩, ⟨.hall 6 9, 22014720⟩]
  caps := #[0, 0, 51891840, 16964640, 1723680, 4490640, 30240, 102060, 1935360, 186900, 0, 0, 0, 0, 0] }

theorem case_31_17_9_checked :
    (Witness.linear .positive case_31_17_9).check 31 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_17_10 : Certificate := {
  objectiveScale := 36400000
  eta := 38339421120
  rows := #[⟨.count 2, 10322151840⟩, ⟨.count 3, 2889726840⟩, ⟨.count 4, 867746880⟩, ⟨.count 5, 304864560⟩, ⟨.count 6, 119159040⟩, ⟨.count 7, 55915860⟩, ⟨.count 8, 41321280⟩, ⟨.count 9, 30990960⟩, ⟨.count 11, 35675640⟩, ⟨.path 8, 10400940⟩, ⟨.privateRow 5 8, 288288⟩, ⟨.privateRow 5 9, 65225160⟩, ⟨.privateRow 6 6, 1881880⟩, ⟨.privateRow 6 7, 30606576⟩, ⟨.privateRow 6 8, 69109040⟩, ⟨.privateRow 7 4, 935220⟩, ⟨.privateRow 7 5, 16486470⟩, ⟨.privateRow 7 6, 37201164⟩, ⟨.privateRow 7 7, 28603575⟩, ⟨.privateRow 8 3, 9721140⟩, ⟨.privateRow 8 4, 20610590⟩, ⟨.privateRow 9 1, 6066060⟩, ⟨.privateRow 9 2, 3592160⟩, ⟨.privateRow 10 0, 2630628⟩, ⟨.hall 5 10, 19017180⟩, ⟨.hall 4 11, 50191680⟩, ⟨.hall 3 12, 71656200⟩, ⟨.hall 2 14, 688143456⟩, ⟨.assumptionRow 10, 30990960⟩]
  caps := #[0, 39605280, 4704700, 314160, 1003860, 229656, 0, 0, 195290, 0, 634452, 724360, 0, 0, 0] }

theorem case_31_17_10_checked :
    (Witness.linear .conditional case_31_17_10).check 31 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_18_1_checked :
    (Witness.rising).check 31 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_18_2_checked :
    (Witness.rising).check 31 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_18_3_checked :
    (Witness.rising).check 31 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_18_4_checked :
    (Witness.rising).check 31 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_18_5_checked :
    (Witness.rising).check 31 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_18_6_checked :
    (Witness.rising).check 31 18 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_18_7_checked :
    (Witness.rising).check 31 18 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_18_8 : Certificate := {
  objectiveScale := 49500000
  eta := 131286355200
  rows := #[⟨.count 2, 24764840100⟩, ⟨.count 3, 4897292400⟩, ⟨.count 4, 1041080040⟩, ⟨.count 5, 246846600⟩, ⟨.count 6, 74324250⟩, ⟨.count 7, 49999950⟩, ⟨.path 8, 24750900⟩, ⟨.privateRow 3 15, 613512900⟩, ⟨.privateRow 8 8, 55180125⟩, ⟨.hall 7 2, 737100⟩, ⟨.hall 8 2, 1649648⟩, ⟨.hall 6 4, 492960⟩, ⟨.hall 7 4, 88725⟩, ⟨.hall 5 7, 124950⟩]
  caps := #[0, 5148000, 14414400, 3920400, 0, 671400, 579150, 683100, 0, 0, 0, 0, 0, 0] }

theorem case_31_18_8_checked :
    (Witness.linear .positive case_31_18_8).check 31 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_18_9 : Certificate := {
  objectiveScale := 8640000
  eta := 19407548160
  rows := #[⟨.count 2, 4764679920⟩, ⟨.count 3, 1139458320⟩, ⟨.count 4, 311351040⟩, ⟨.count 5, 86486400⟩, ⟨.count 6, 27027000⟩, ⟨.count 7, 11171160⟩, ⟨.count 8, 8648640⟩, ⟨.path 9, 2468448⟩, ⟨.hall 6 6, 146965⟩]
  caps := #[0, 6177600, 473616, 964656, 0, 0, 245520, 0, 0, 0, 0, 0, 0, 0] }

theorem case_31_18_9_checked :
    (Witness.linear .positive case_31_18_9).check 31 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_18_10 : Certificate := {
  objectiveScale := 52787817600000
  eta := 141467133421373760
  rows := #[⟨.count 2, 31275222047989920⟩, ⟨.count 3, 8111787797393280⟩, ⟨.count 4, 2156349620513088⟩, ⟨.count 5, 645410251886400⟩, ⟨.count 6, 219099796035120⟩, ⟨.count 7, 79827057470160⟩, ⟨.count 8, 61144129126080⟩, ⟨.count 11, 37365856688160⟩, ⟨.path 7, 31672690489440⟩, ⟨.privateRow 2 16, 523121993634240⟩, ⟨.privateRow 4 11, 174260768009328⟩, ⟨.privateRow 4 12, 463336622933184⟩, ⟨.privateRow 5 9, 139046278827456⟩, ⟨.privateRow 5 10, 232347690679104⟩, ⟨.privateRow 5 11, 355843734197952⟩, ⟨.privateRow 6 6, 5459297243400⟩, ⟨.privateRow 6 7, 76571698743540⟩, ⟨.privateRow 6 8, 132648791242968⟩, ⟨.privateRow 6 9, 181592402011020⟩, ⟨.privateRow 7 4, 5853579822090⟩, ⟨.privateRow 7 5, 42149240939520⟩, ⟨.privateRow 7 6, 78249927155400⟩, ⟨.privateRow 7 7, 31494079208592⟩, ⟨.privateRow 8 2, 2704935753520⟩, ⟨.privateRow 8 3, 27776702178225⟩, ⟨.privateRow 8 4, 23980468632120⟩, ⟨.privateRow 9 0, 3623355800064⟩, ⟨.privateRow 9 1, 12128177052992⟩, ⟨.privateRow 10 0, 3963045406320⟩, ⟨.hall 4 13, 279224856342432⟩, ⟨.hall 3 14, 1346529599198784⟩, ⟨.hall 2 15, 2375067265741170⟩, ⟨.assumptionRow 10, 48288975845040⟩]
  caps := #[0, 137178828346560, 9229641701280, 11470861412010, 0, 406841769600, 0, 1154085711372, 627982573855, 0, 219069443040, 15421960911840, 0, 0] }

theorem case_31_18_10_checked :
    (Witness.linear .conditional case_31_18_10).check 31 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_18_11 : Certificate := {
  objectiveScale := 738551520000
  eta := 3127408228264320
  rows := #[⟨.count 2, 637021611626400⟩, ⟨.count 3, 145640144089440⟩, ⟨.count 4, 32021821383552⟩, ⟨.count 5, 7299022610880⟩, ⟨.count 6, 1372967275680⟩, ⟨.count 7, 228827879280⟩, ⟨.count 10, 211225734720⟩, ⟨.path 6, 1171017207360⟩, ⟨.privateRow 2 16, 9293932327680⟩, ⟨.privateRow 4 11, 3052211866704⟩, ⟨.privateRow 4 12, 8459590675536⟩, ⟨.privateRow 5 9, 2154502494144⟩, ⟨.privateRow 5 10, 3994513338816⟩, ⟨.privateRow 5 11, 7089361511232⟩, ⟨.privateRow 6 6, 85496130720⟩, ⟨.privateRow 6 7, 972518486940⟩, ⟨.privateRow 6 8, 2100522584160⟩, ⟨.privateRow 6 9, 3646577614680⟩, ⟨.privateRow 6 10, 2533730919720⟩, ⟨.privateRow 7 4, 42433741350⟩, ⟨.privateRow 7 5, 433946747520⟩, ⟨.privateRow 7 6, 1083370087800⟩, ⟨.privateRow 7 7, 2173613393952⟩, ⟨.privateRow 7 8, 220026807000⟩, ⟨.privateRow 8 2, 18580041480⟩, ⟨.privateRow 8 3, 151451785485⟩, ⟨.privateRow 8 4, 607693086000⟩, ⟨.privateRow 8 5, 840991351200⟩, ⟨.privateRow 9 1, 22426436032⟩, ⟨.privateRow 9 2, 322119245448⟩, ⟨.privateRow 9 3, 257494228992⟩, ⟨.privateRow 10 1, 203304769668⟩, ⟨.privateRow 11 0, 52806433680⟩, ⟨.hall 4 13, 9251687180736⟩, ⟨.hall 3 14, 29015375092704⟩, ⟨.hall 2 15, 47389373691660⟩, ⟨.assumptionRow 11, 204059049600⟩]
  caps := #[0, 0, 261376795680, 9629928000, 0, 8824361280, 11784885420, 3937224852, 0, 31687116608, 0, 108348243360, 738551520000, 0] }

theorem case_31_18_11_checked :
    (Witness.linear .conditional case_31_18_11).check 31 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_19_1_checked :
    (Witness.rising).check 31 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_19_2_checked :
    (Witness.rising).check 31 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_19_3_checked :
    (Witness.rising).check 31 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_19_4_checked :
    (Witness.rising).check 31 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_19_5_checked :
    (Witness.rising).check 31 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_19_6_checked :
    (Witness.rising).check 31 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_19_7_checked :
    (Witness.rising).check 31 19 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_31_19_8_checked :
    (Witness.linear .positive case_31_19_8).check 31 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_19_9 : Certificate := {
  objectiveScale := 2151560000
  eta := 9856460954340
  rows := #[⟨.count 2, 2339224442100⟩, ⟨.count 3, 531281483460⟩, ⟨.count 4, 136741104864⟩, ⟨.count 5, 34802020890⟩, ⟨.count 6, 10761565230⟩, ⟨.count 7, 3964787190⟩, ⟨.count 8, 2466978696⟩, ⟨.path 7, 1352431080⟩, ⟨.path 8, 184442481⟩]
  caps := #[0, 7378742228, 0, 244426092, 102858462, 54518625, 57933976, 0, 0, 0, 0, 0, 0] }

theorem case_31_19_9_checked :
    (Witness.linear .positive case_31_19_9).check 31 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_19_10 : Certificate := {
  objectiveScale := 115216038000000
  eta := 385921442261955600
  rows := #[⟨.count 2, 88436005596338400⟩, ⟨.count 3, 21839126264635680⟩, ⟨.count 4, 5849601204807360⟩, ⟨.count 5, 1649236932743400⟩, ⟨.count 6, 543704483322000⟩, ⟨.count 7, 219129382672200⟩, ⟨.count 8, 73812002584320⟩, ⟨.count 9, 41519251453680⟩, ⟨.path 7, 76438447885800⟩, ⟨.privateRow 2 17, 9272632824655200⟩, ⟨.privateRow 3 14, 2366597332859760⟩, ⟨.privateRow 3 15, 3805931383254000⟩, ⟨.privateRow 4 11, 288789460111152⟩, ⟨.privateRow 4 12, 1530445741084260⟩, ⟨.privateRow 4 13, 1914498817030800⟩, ⟨.privateRow 4 14, 2163614325752880⟩, ⟨.privateRow 5 9, 332922886656360⟩, ⟨.privateRow 5 10, 762108926683104⟩, ⟨.privateRow 5 11, 1012608410453640⟩, ⟨.privateRow 5 12, 774257152108440⟩, ⟨.privateRow 6 7, 249256730665800⟩, ⟨.privateRow 6 8, 429746220403500⟩, ⟨.privateRow 6 9, 482084641878840⟩, ⟨.privateRow 7 4, 5491964478000⟩, ⟨.privateRow 7 5, 160845909649425⟩, ⟨.privateRow 7 6, 260789856069600⟩, ⟨.privateRow 8 0, 2691062594220⟩, ⟨.privateRow 8 3, 114306087335440⟩, ⟨.privateRow 8 4, 23354578942695⟩, ⟨.privateRow 9 1, 39673951389072⟩, ⟨.privateRow 10 0, 11071800387648⟩, ⟨.privateRow 11 0, 15377500538400⟩, ⟨.hall 3 15, 384053075946540⟩, ⟨.hall 2 16, 3101732314480800⟩, ⟨.assumptionRow 10, 118257741403200⟩]
  caps := #[0, 0, 169335391024800, 0, 7683732534240, 18954489730176, 1864097991000, 2498555499300, 0, 5612403643056, 72731737012032, 0, 0] }

theorem case_31_19_10_checked :
    (Witness.linear .conditional case_31_19_10).check 31 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_19_11 : Certificate := {
  objectiveScale := 21689647812000000
  eta := 132046183296830602800
  rows := #[⟨.count 2, 25076594766082860000⟩, ⟨.count 3, 4986659987769620160⟩, ⟨.count 4, 932719057273523520⟩, ⟨.count 5, 169348432186533600⟩, ⟨.count 6, 24192633169504800⟩, ⟨.count 7, 9770101856915400⟩, ⟨.path 5, 67983236607686400⟩, ⟨.path 6, 12530483469504000⟩, ⟨.privateRow 2 17, 2670494507556876000⟩, ⟨.privateRow 3 14, 689552077723629120⟩, ⟨.privateRow 3 15, 1035630796833032400⟩, ⟨.privateRow 4 11, 98830008117064224⟩, ⟨.privateRow 4 12, 371806653999280500⟩, ⟨.privateRow 4 13, 509637461306653680⟩, ⟨.privateRow 4 14, 634839507324902880⟩, ⟨.privateRow 5 9, 82466896784852580⟩, ⟨.privateRow 5 10, 171128761858238184⟩, ⟨.privateRow 5 11, 255053936809141470⟩, ⟨.privateRow 5 12, 343690471988823960⟩, ⟨.privateRow 6 6, 1512039573094050⟩, ⟨.privateRow 6 7, 44663322774470400⟩, ⟨.privateRow 6 8, 91394391973684800⟩, ⟨.privateRow 6 9, 135695859123825000⟩, ⟨.privateRow 6 10, 101888205079260600⟩, ⟨.privateRow 7 5, 22699978719142725⟩, ⟨.privateRow 7 6, 55651918060252800⟩, ⟨.privateRow 7 7, 71776647768926100⟩, ⟨.privateRow 8 3, 9625359607183320⟩, ⟨.privateRow 8 4, 37967701382846235⟩, ⟨.privateRow 8 5, 9615020875059600⟩, ⟨.privateRow 9 1, 2431669795498944⟩, ⟨.privateRow 9 2, 17417317384426960⟩, ⟨.privateRow 10 0, 5862061114149240⟩, ⟨.privateRow 11 0, 1447422497320800⟩, ⟨.hall 3 15, 194669279499039345⟩, ⟨.hall 2 16, 926435540785154400⟩, ⟨.assumptionRow 11, 9484882988187600⟩]
  caps := #[0, 18863300857892400, 0, 0, 101371390509312, 0, 88229912654850, 96712590333150, 0, 0, 2347470582692760, 13522049434261200, 21689647812000000] }

theorem case_31_19_11_checked :
    (Witness.linear .conditional case_31_19_11).check 31 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_19_12 : Certificate := {
  objectiveScale := 21654854342100000
  eta := 133936053680644815600
  rows := #[⟨.count 2, 25615440581852721600⟩, ⟨.count 3, 5194930261135895280⟩, ⟨.count 4, 1192414448749043520⟩, ⟨.count 5, 319986564328431000⟩, ⟨.count 6, 81397503921333600⟩, ⟨.count 7, 16515435578241600⟩, ⟨.path 3, 492639758248397760⟩, ⟨.path 7, 16239635879266800⟩, ⟨.privateRow 5 10, 111644344508913216⟩, ⟨.privateRow 6 7, 2317216726539000⟩, ⟨.privateRow 6 11, 744374274990746400⟩, ⟨.privateRow 7 5, 663566608054350⟩, ⟨.privateRow 8 4, 670939570366065⟩, ⟨.privateRow 8 8, 158651403023483370⟩, ⟨.privateRow 9 2, 183504839758240⟩, ⟨.privateRow 10 1, 275257259637360⟩, ⟨.privateRow 11 0, 2752572596373600⟩, ⟨.hall 7 4, 257740888569528⟩, ⟨.hall 8 4, 1378788636910776⟩, ⟨.hall 9 4, 931942436200776⟩, ⟨.hall 10 5, 688143149093400⟩, ⟨.hall 6 6, 1030496084406600⟩, ⟨.hall 9 6, 117967396987440⟩, ⟨.hall 11 7, 17031542940061650⟩, ⟨.hall 5 11, 6087420165057000⟩, ⟨.hall 4 12, 26189972053232064⟩, ⟨.hall 3 13, 36783708973146135⟩, ⟨.hall 2 15, 256930388416651950⟩]
  caps := #[0, 51152566660650000, 0, 1481688666168480, 0, 0, 0, 0, 83371189217085, 0, 22240016628322080, 0, 108274271710500000] }

theorem case_31_19_12_checked :
    (Witness.linear .negative case_31_19_12).check 31 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_20_1_checked :
    (Witness.rising).check 31 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_20_2_checked :
    (Witness.rising).check 31 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_20_3_checked :
    (Witness.rising).check 31 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_20_4_checked :
    (Witness.rising).check 31 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_20_5_checked :
    (Witness.rising).check 31 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_20_6_checked :
    (Witness.rising).check 31 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_20_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_31_20_7_checked :
    (Witness.linear .positive case_31_20_7).check 31 20 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_31_20_8_checked :
    (Witness.linear .positive case_31_20_8).check 31 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_31_20_9_checked :
    (Witness.linear .positive case_31_20_9).check 31 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_20_10 : Certificate := {
  objectiveScale := 4784835300000
  eta := 47786724321336000
  rows := #[⟨.count 2, 9113962886028000⟩, ⟨.count 3, 1845782753855040⟩, ⟨.count 4, 420391801589760⟩, ⟨.count 5, 95010423908400⟩, ⟨.count 6, 23459363928000⟩, ⟨.count 7, 4926466424880⟩, ⟨.count 8, 3284310949920⟩, ⟨.path 6, 11482395004080⟩, ⟨.privateRow 3 15, 324416937164320⟩, ⟨.privateRow 4 13, 305133014191005⟩, ⟨.privateRow 4 14, 81149849720940⟩, ⟨.privateRow 5 9, 13941564848640⟩, ⟨.privateRow 5 12, 236880927262980⟩, ⟨.privateRow 6 6, 586484098200⟩, ⟨.privateRow 6 10, 124764717157080⟩, ⟨.privateRow 7 4, 1079130740688⟩, ⟨.privateRow 7 9, 656862189984⟩, ⟨.privateRow 8 2, 858399452820⟩, ⟨.privateRow 8 6, 821077737480⟩, ⟨.privateRow 8 9, 9955567566945⟩, ⟨.privateRow 9 1, 1890966910560⟩, ⟨.hall 9 1, 447860584080⟩, ⟨.hall 6 7, 109572728370⟩, ⟨.hall 7 7, 21292517085⟩, ⟨.hall 3 13, 272542610340⟩, ⟨.hall 2 15, 3690824927790⟩, ⟨.assumptionRow 10, 5621224510440⟩]
  caps := #[0, 2466735311040, 1799692734840, 2498706850640, 0, 1228333151760, 101869307400, 1029395795484, 0, 0, 0, 4784835300000] }

theorem case_31_20_10_checked :
    (Witness.linear .conditional case_31_20_10).check 31 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_20_11 : Certificate := {
  objectiveScale := 39135600000
  eta := 502533508276800
  rows := #[⟨.count 2, 86027719377600⟩, ⟨.count 3, 14933409210720⟩, ⟨.count 4, 2577697602480⟩, ⟨.count 5, 369361792800⟩, ⟨.count 6, 55963908000⟩, ⟨.count 7, 23504841360⟩, ⟨.path 5, 279815936400⟩, ⟨.privateRow 2 18, 7545054076560⟩, ⟨.privateRow 3 14, 411334723800⟩, ⟨.privateRow 3 15, 2542005065600⟩, ⟨.privateRow 3 16, 3050406078720⟩, ⟨.privateRow 4 11, 37542454950⟩, ⟨.privateRow 4 12, 713763682632⟩, ⟨.privateRow 4 13, 1313333010990⟩, ⟨.privateRow 4 14, 1533690898740⟩, ⟨.privateRow 4 15, 1269261433440⟩, ⟨.privateRow 5 9, 104572559520⟩, ⟨.privateRow 5 10, 438757038720⟩, ⟨.privateRow 5 11, 664403515776⟩, ⟨.privateRow 5 12, 815114320020⟩, ⟨.privateRow 5 13, 129090081120⟩, ⟨.privateRow 6 7, 89192478375⟩, ⟨.privateRow 6 8, 255035523600⟩, ⟨.privateRow 6 9, 402629227000⟩, ⟨.privateRow 6 10, 146625438960⟩, ⟨.privateRow 7 5, 61435934560⟩, ⟨.privateRow 7 6, 176845949280⟩, ⟨.privateRow 7 7, 108729878400⟩, ⟨.privateRow 8 3, 44267451228⟩, ⟨.privateRow 8 4, 80308207980⟩, ⟨.privateRow 9 1, 36563086560⟩, ⟨.privateRow 9 2, 2611649040⟩, ⟨.privateRow 10 0, 12820822560⟩, ⟨.hall 2 17, 1697571876000⟩, ⟨.assumptionRow 11, 23324491470⟩]
  caps := #[0, 162064375200, 0, 12163971820, 8448856416, 2574873360, 0, 95034282, 3692182956, 19300373400, 0, 289760308530] }

theorem case_31_20_11_checked :
    (Witness.linear .conditional case_31_20_11).check 31 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_20_12 : Certificate := {
  objectiveScale := 10490610664800000
  eta := 167782095707401375200
  rows := #[⟨.count 2, 29593303520119859520⟩, ⟨.count 3, 5447371278781111680⟩, ⟨.count 4, 953800027277217120⟩, ⟨.count 5, 142086329502717600⟩, ⟨.count 6, 12751337263064400⟩, ⟨.path 5, 65042259458576400⟩, ⟨.path 6, 12588440877492480⟩, ⟨.privateRow 3 15, 926597174449346400⟩, ⟨.privateRow 3 16, 1238579892818988720⟩, ⟨.privateRow 4 13, 796161620362583475⟩, ⟨.privateRow 4 14, 483275682270140760⟩, ⟨.privateRow 4 15, 809391132773012790⟩, ⟨.privateRow 5 11, 200159562637930896⟩, ⟨.privateRow 5 13, 1214291631365532720⟩, ⟨.privateRow 6 7, 8387040283146525⟩, ⟨.privateRow 6 8, 24461749035266400⟩, ⟨.privateRow 6 11, 667395884250745650⟩, ⟨.privateRow 7 5, 1457295687207360⟩, ⟨.hall 7 4, 1079851008781188⟩, ⟨.hall 8 4, 391556214946624⟩, ⟨.hall 9 4, 463684991384160⟩, ⟨.hall 6 6, 624797934492000⟩, ⟨.hall 8 6, 207922238200040⟩, ⟨.hall 3 14, 1525159947150840⟩, ⟨.hall 2 16, 51855438203128560⟩]
  caps := #[0, 0, 589247694322560, 5412253883596560, 839294121299760, 584405433506160, 979123891014555, 707217024674160, 0, 9520229178306000, 0, 283246487949600000] }

theorem case_31_20_12_checked :
    (Witness.linear .negative case_31_20_12).check 31 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_21_1_checked :
    (Witness.rising).check 31 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_21_2_checked :
    (Witness.rising).check 31 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_21_3_checked :
    (Witness.rising).check 31 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_21_4_checked :
    (Witness.rising).check 31 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_21_5_checked :
    (Witness.rising).check 31 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_21_6_checked :
    (Witness.rising).check 31 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_21_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_31_21_7_checked :
    (Witness.linear .positive case_31_21_7).check 31 21 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_31_21_8_checked :
    (Witness.linear .positive case_31_21_8).check 31 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_31_21_9_checked :
    (Witness.linear .positive case_31_21_9).check 31 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_21_10 : Certificate := {
  objectiveScale := 3
  eta := 4004
  rows := #[⟨.assumptionRow 10, 7⟩]
  caps := #[0, 0, 1287, 429, 150, 56, 23, 11, 169, 85, 23] }

theorem case_31_21_10_checked :
    (Witness.linear .conditional case_31_21_10).check 31 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_21_11 : Certificate := {
  objectiveScale := 66074400000
  eta := 2121720278277600
  rows := #[⟨.count 2, 279897668930880⟩, ⟨.count 3, 36598831509240⟩, ⟨.count 4, 3919295540160⟩, ⟨.count 6, 64250746560⟩, ⟨.count 7, 56219403240⟩, ⟨.path 4, 3286565362080⟩, ⟨.privateRow 2 18, 5172185098080⟩, ⟨.privateRow 2 19, 19939148349120⟩, ⟨.privateRow 3 15, 5650050025620⟩, ⟨.privateRow 3 16, 8620308496800⟩, ⟨.privateRow 3 17, 7702058243880⟩, ⟨.privateRow 4 11, 203078252520⟩, ⟨.privateRow 4 12, 1246196771820⟩, ⟨.privateRow 4 13, 3744212255784⟩, ⟨.privateRow 4 14, 4108032108180⟩, ⟨.privateRow 4 15, 2869866679680⟩, ⟨.privateRow 5 7, 26771144400⟩, ⟨.privateRow 5 8, 8328800480⟩, ⟨.privateRow 5 9, 266372886780⟩, ⟨.privateRow 5 10, 1085378682960⟩, ⟨.privateRow 5 11, 2039068831800⟩, ⟨.privateRow 5 12, 1715494933152⟩, ⟨.privateRow 6 6, 9637611984⟩, ⟨.privateRow 6 7, 285558873600⟩, ⟨.privateRow 6 8, 836598262500⟩, ⟨.privateRow 6 9, 888801994080⟩, ⟨.privateRow 7 5, 305191046160⟩, ⟨.privateRow 7 6, 439046768160⟩, ⟨.privateRow 8 3, 252135505440⟩, ⟨.privateRow 9 1, 81205804680⟩, ⟨.hall 2 18, 1601759839680⟩, ⟨.assumptionRow 11, 46920670335⟩]
  caps := #[0, 0, 19792502730, 36252846630, 3789295020, 29831203688, 9815856855, 0, 112381542000, 0, 2438066896650] }

theorem case_31_21_11_checked :
    (Witness.linear .conditional case_31_21_11).check 31 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_21_12 : Certificate := {
  objectiveScale := 161053200000
  eta := 6317643217485600
  rows := #[⟨.count 2, 665712693565920⟩, ⟨.count 3, 53762859750600⟩, ⟨.path 3, 53782065136800⟩, ⟨.privateRow 2 17, 24976624152480⟩, ⟨.privateRow 2 18, 81016233938640⟩, ⟨.privateRow 2 19, 81016233938640⟩, ⟨.privateRow 3 13, 1916076762600⟩, ⟨.privateRow 3 14, 14634318050352⟩, ⟨.privateRow 3 15, 20152619126640⟩, ⟨.privateRow 3 16, 38918900360340⟩, ⟨.privateRow 3 17, 28200141529560⟩, ⟨.privateRow 4 9, 207709161660⟩, ⟨.privateRow 4 10, 1144815611940⟩, ⟨.privateRow 4 11, 3815361976140⟩, ⟨.privateRow 4 12, 5885897987970⟩, ⟨.privateRow 4 13, 12590073463968⟩, ⟨.privateRow 4 14, 15429650921685⟩, ⟨.privateRow 4 15, 10515880114740⟩, ⟨.privateRow 5 6, 103635015120⟩, ⟨.privateRow 5 7, 408655699452⟩, ⟨.privateRow 5 8, 987557771200⟩, ⟨.privateRow 5 9, 1809001884690⟩, ⟨.privateRow 5 10, 4231470363120⟩, ⟨.privateRow 5 11, 6612880053780⟩, ⟨.privateRow 5 12, 6034192668504⟩, ⟨.privateRow 6 3, 62424220320⟩, ⟨.privateRow 6 4, 184362007830⟩, ⟨.privateRow 6 5, 360966027240⟩, ⟨.privateRow 6 6, 625059663228⟩, ⟨.privateRow 6 7, 1264503320080⟩, ⟨.privateRow 6 8, 3677176728225⟩, ⟨.privateRow 6 9, 1686515585040⟩, ⟨.privateRow 7 1, 216334957410⟩, ⟨.privateRow 7 2, 181699069860⟩, ⟨.privateRow 7 3, 361075810095⟩, ⟨.privateRow 7 4, 781214796180⟩, ⟨.privateRow 7 5, 1304220317400⟩, ⟨.privateRow 8 0, 982995683670⟩, ⟨.privateRow 9 0, 426565505520⟩, ⟨.privateRow 10 0, 202878716040⟩, ⟨.hall 2 18, 4769429464800⟩]
  caps := #[0, 240940299600, 252191940000, 23690717820, 29086183269, 23256351664, 0, 52570864530, 0, 228534490800, 0] }

theorem case_31_21_12_checked :
    (Witness.linear .negative case_31_21_12).check 31 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_21_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 429, 429, 297, 165] }

theorem case_31_21_13_checked :
    (Witness.linear .negative case_31_21_13).check 31 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_22_1_checked :
    (Witness.rising).check 31 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_22_2_checked :
    (Witness.rising).check 31 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_22_3_checked :
    (Witness.rising).check 31 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_22_4_checked :
    (Witness.rising).check 31 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_22_5_checked :
    (Witness.rising).check 31 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_22_6_checked :
    (Witness.rising).check 31 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_22_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_31_22_7_checked :
    (Witness.linear .positive case_31_22_7).check 31 22 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_31_22_8_checked :
    (Witness.linear .positive case_31_22_8).check 31 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_31_22_9_checked :
    (Witness.linear .positive case_31_22_9).check 31 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_31_22_10_checked :
    (Witness.linear .positive case_31_22_10).check 31 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_22_11 : Certificate := {
  objectiveScale := 698
  eta := 874120
  rows := #[⟨.assumptionRow 11, 995⟩]
  caps := #[0, 0, 297297, 103565, 37200, 13900, 5465, 237874, 172991, 80509] }

theorem case_31_22_11_checked :
    (Witness.linear .conditional case_31_22_11).check 31 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_22_12 : Certificate := {
  objectiveScale := 203
  eta := 177996
  rows := #[⟨.assumptionRow 12, 191⟩]
  caps := #[0, 0, 61880, 22165, 9185, 3687, 1456, 93548, 81536, 47359] }

theorem case_31_22_12_checked :
    (Witness.linear .conditional case_31_22_12).check 31 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_22_13 : Certificate := {
  objectiveScale := 961
  eta := 35203
  rows := #[⟨.assumptionRow 13, 400⟩]
  caps := #[0, 0, 20735, 9706, 5351, 3112, 1439, 573430, 561561, 378092] }

theorem case_31_22_13_checked :
    (Witness.linear .conditional case_31_22_13).check 31 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_22_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 429, 429] }

theorem case_31_22_14_checked :
    (Witness.linear .negative case_31_22_14).check 31 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_23_1_checked :
    (Witness.rising).check 31 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_23_2_checked :
    (Witness.rising).check 31 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_23_3_checked :
    (Witness.rising).check 31 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_23_4_checked :
    (Witness.rising).check 31 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_23_5_checked :
    (Witness.rising).check 31 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_23_6_checked :
    (Witness.rising).check 31 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_23_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0] }

theorem case_31_23_7_checked :
    (Witness.linear .positive case_31_23_7).check 31 23 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_31_23_8_checked :
    (Witness.linear .positive case_31_23_8).check 31 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_31_23_9_checked :
    (Witness.linear .positive case_31_23_9).check 31 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_31_23_10_checked :
    (Witness.linear .positive case_31_23_10).check 31 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_23_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_31_23_11_checked :
    (Witness.linear .positive case_31_23_11).check 31 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_23_12 : Certificate := {
  objectiveScale := 887
  eta := 1668108
  rows := #[⟨.assumptionRow 12, 1012⟩]
  caps := #[0, 0, 573118, 198341, 69410, 24627, 10608, 650104, 531986] }

theorem case_31_23_12_checked :
    (Witness.linear .conditional case_31_23_12).check 31 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_23_13 : Certificate := {
  objectiveScale := 7
  eta := 280
  rows := #[⟨.assumptionRow 13, 3⟩]
  caps := #[0, 0, 169, 84, 42, 25, 12818, 13104, 9100] }

theorem case_31_23_13_checked :
    (Witness.linear .conditional case_31_23_13).check 31 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_23_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 1430, 1430] }

theorem case_31_23_14_checked :
    (Witness.linear .negative case_31_23_14).check 31 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_24_1_checked :
    (Witness.rising).check 31 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_24_2_checked :
    (Witness.rising).check 31 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_24_3_checked :
    (Witness.rising).check 31 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_24_4_checked :
    (Witness.rising).check 31 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_24_5_checked :
    (Witness.rising).check 31 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_24_6_checked :
    (Witness.rising).check 31 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_24_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_31_24_7_checked :
    (Witness.linear .positive case_31_24_7).check 31 24 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_31_24_8_checked :
    (Witness.linear .positive case_31_24_8).check 31 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_31_24_9_checked :
    (Witness.linear .positive case_31_24_9).check 31 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_31_24_10_checked :
    (Witness.linear .positive case_31_24_10).check 31 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_31_24_11_checked :
    (Witness.linear .positive case_31_24_11).check 31 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_24_12 : Certificate := {
  objectiveScale := 4
  eta := 54366
  rows := #[⟨.assumptionRow 12, 9⟩]
  caps := #[0, 0, 16328, 5005, 1573, 528, 186, 70] }

theorem case_31_24_12_checked :
    (Witness.linear .conditional case_31_24_12).check 31 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_24_13 : Certificate := {
  objectiveScale := 563
  eta := 246120
  rows := #[⟨.assumptionRow 13, 375⟩]
  caps := #[0, 0, 101920, 43771, 16478, 8420, 1746342, 1661036] }

theorem case_31_24_13_checked :
    (Witness.linear .conditional case_31_24_13).check 31 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_24_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 4862, 4862] }

theorem case_31_24_14_checked :
    (Witness.linear .negative case_31_24_14).check 31 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_24_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_31_24_15_checked :
    (Witness.linear .negative case_31_24_15).check 31 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_25_1_checked :
    (Witness.rising).check 31 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_25_2_checked :
    (Witness.rising).check 31 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_25_3_checked :
    (Witness.rising).check 31 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_25_4_checked :
    (Witness.rising).check 31 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_25_5_checked :
    (Witness.rising).check 31 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_25_6_checked :
    (Witness.rising).check 31 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_25_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_31_25_7_checked :
    (Witness.linear .positive case_31_25_7).check 31 25 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_31_25_8_checked :
    (Witness.linear .positive case_31_25_8).check 31 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_31_25_9_checked :
    (Witness.linear .positive case_31_25_9).check 31 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_31_25_10_checked :
    (Witness.linear .positive case_31_25_10).check 31 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_31_25_11_checked :
    (Witness.linear .positive case_31_25_11).check 31 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_25_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_31_25_12_checked :
    (Witness.linear .positive case_31_25_12).check 31 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_25_13 : Certificate := {
  objectiveScale := 985
  eta := 1527484
  rows := #[⟨.assumptionRow 13, 853⟩]
  caps := #[0, 0, 595140, 226408, 82885, 32395, 4978722] }

theorem case_31_25_13_checked :
    (Witness.linear .conditional case_31_25_13).check 31 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_25_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 16796, 16796] }

theorem case_31_25_14_checked :
    (Witness.linear .negative case_31_25_14).check 31 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_25_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_31_25_15_checked :
    (Witness.linear .negative case_31_25_15).check 31 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_31_25_16_checked :
    (Witness.linear .negative case_31_25_16).check 31 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_26_1_checked :
    (Witness.rising).check 31 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_26_2_checked :
    (Witness.rising).check 31 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_26_3_checked :
    (Witness.rising).check 31 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_26_4_checked :
    (Witness.rising).check 31 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_26_5_checked :
    (Witness.rising).check 31 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_26_6_checked :
    (Witness.rising).check 31 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_26_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_31_26_7_checked :
    (Witness.linear .positive case_31_26_7).check 31 26 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_31_26_8_checked :
    (Witness.linear .positive case_31_26_8).check 31 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_31_26_9_checked :
    (Witness.linear .positive case_31_26_9).check 31 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_31_26_10_checked :
    (Witness.linear .positive case_31_26_10).check 31 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_31_26_11_checked :
    (Witness.linear .positive case_31_26_11).check 31 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_31_26_12_checked :
    (Witness.linear .positive case_31_26_12).check 31 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_26_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_31_26_13_checked :
    (Witness.linear .positive case_31_26_13).check 31 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_26_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 58786, 58786] }

theorem case_31_26_14_checked :
    (Witness.linear .negative case_31_26_14).check 31 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_26_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_31_26_15_checked :
    (Witness.linear .negative case_31_26_15).check 31 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_26_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_31_26_16_checked :
    (Witness.linear .negative case_31_26_16).check 31 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_27_1_checked :
    (Witness.rising).check 31 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_27_2_checked :
    (Witness.rising).check 31 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_27_3_checked :
    (Witness.rising).check 31 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_27_4_checked :
    (Witness.rising).check 31 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_27_5_checked :
    (Witness.rising).check 31 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_27_6_checked :
    (Witness.rising).check 31 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_27_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_31_27_7_checked :
    (Witness.linear .positive case_31_27_7).check 31 27 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_31_27_8_checked :
    (Witness.linear .positive case_31_27_8).check 31 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_31_27_9_checked :
    (Witness.linear .positive case_31_27_9).check 31 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_31_27_10_checked :
    (Witness.linear .positive case_31_27_10).check 31 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_31_27_11_checked :
    (Witness.linear .positive case_31_27_11).check 31 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_31_27_12_checked :
    (Witness.linear .positive case_31_27_12).check 31 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_27_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_31_27_13_checked :
    (Witness.linear .positive case_31_27_13).check 31 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_27_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 208012, 208012] }

theorem case_31_27_14_checked :
    (Witness.linear .negative case_31_27_14).check 31 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_27_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_31_27_15_checked :
    (Witness.linear .negative case_31_27_15).check 31 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_27_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_31_27_16_checked :
    (Witness.linear .negative case_31_27_16).check 31 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_31_27_17_checked :
    (Witness.linear .negative case_31_27_17).check 31 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_28_1_checked :
    (Witness.rising).check 31 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_28_2_checked :
    (Witness.rising).check 31 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_28_3_checked :
    (Witness.rising).check 31 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_28_4_checked :
    (Witness.rising).check 31 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_28_5_checked :
    (Witness.rising).check 31 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_28_6_checked :
    (Witness.rising).check 31 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_31_28_7_checked :
    (Witness.linear .positive case_31_28_7).check 31 28 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_31_28_8_checked :
    (Witness.linear .positive case_31_28_8).check 31 28 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_31_28_9_checked :
    (Witness.linear .positive case_31_28_9).check 31 28 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_31_28_10_checked :
    (Witness.linear .positive case_31_28_10).check 31 28 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_31_28_11_checked :
    (Witness.linear .positive case_31_28_11).check 31 28 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_31_28_12_checked :
    (Witness.linear .positive case_31_28_12).check 31 28 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_31_28_13_checked :
    (Witness.linear .positive case_31_28_13).check 31 28 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_31_28_14_checked :
    (Witness.linear .positive case_31_28_14).check 31 28 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_31_28_15_checked :
    (Witness.linear .negative case_31_28_15).check 31 28 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_31_28_16_checked :
    (Witness.linear .negative case_31_28_16).check 31 28 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_31_28_17_checked :
    (Witness.linear .negative case_31_28_17).check 31 28 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_31_28_18_checked :
    (Witness.linear .negative case_31_28_18).check 31 28 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_29_1_checked :
    (Witness.rising).check 31 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_29_2_checked :
    (Witness.rising).check 31 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_29_3_checked :
    (Witness.rising).check 31 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_29_4_checked :
    (Witness.rising).check 31 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_29_5_checked :
    (Witness.rising).check 31 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_29_6_checked :
    (Witness.rising).check 31 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_31_29_7_checked :
    (Witness.linear .positive case_31_29_7).check 31 29 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_31_29_8_checked :
    (Witness.linear .positive case_31_29_8).check 31 29 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_31_29_9_checked :
    (Witness.linear .positive case_31_29_9).check 31 29 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_31_29_10_checked :
    (Witness.linear .positive case_31_29_10).check 31 29 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_31_29_11_checked :
    (Witness.linear .positive case_31_29_11).check 31 29 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_31_29_12_checked :
    (Witness.linear .positive case_31_29_12).check 31 29 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_31_29_13_checked :
    (Witness.linear .positive case_31_29_13).check 31 29 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_31_29_14_checked :
    (Witness.linear .positive case_31_29_14).check 31 29 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_31_29_15_checked :
    (Witness.linear .negative case_31_29_15).check 31 29 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_31_29_16_checked :
    (Witness.linear .negative case_31_29_16).check 31 29 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_31_29_17_checked :
    (Witness.linear .negative case_31_29_17).check 31 29 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_31_29_18_checked :
    (Witness.linear .negative case_31_29_18).check 31 29 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_30_1_checked :
    (Witness.rising).check 31 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_30_2_checked :
    (Witness.rising).check 31 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_30_3_checked :
    (Witness.rising).check 31 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_30_4_checked :
    (Witness.rising).check 31 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_30_5_checked :
    (Witness.rising).check 31 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_31_30_6_checked :
    (Witness.rising).check 31 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_7_checked :
    (Witness.linear .positive case_31_30_7).check 31 30 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_8_checked :
    (Witness.linear .positive case_31_30_8).check 31 30 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_9_checked :
    (Witness.linear .positive case_31_30_9).check 31 30 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_10_checked :
    (Witness.linear .positive case_31_30_10).check 31 30 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_11_checked :
    (Witness.linear .positive case_31_30_11).check 31 30 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_12_checked :
    (Witness.linear .positive case_31_30_12).check 31 30 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_13_checked :
    (Witness.linear .positive case_31_30_13).check 31 30 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_14_checked :
    (Witness.linear .positive case_31_30_14).check 31 30 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_15_checked :
    (Witness.linear .positive case_31_30_15).check 31 30 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_16_checked :
    (Witness.linear .negative case_31_30_16).check 31 30 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_17_checked :
    (Witness.linear .negative case_31_30_17).check 31 30 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_18_checked :
    (Witness.linear .negative case_31_30_18).check 31 30 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_31_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_31_30_19_checked :
    (Witness.linear .negative case_31_30_19).check 31 30 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_31 (a k : ℕ) (h : Domain 31 a k) :
    ∃ w : Witness, w.check 31 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 16 ≤ a := by omega
  have haHi : a ≤ 30 := by omega
  interval_cases a

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_16_1_checked⟩

    · exact ⟨Witness.rising, case_31_16_2_checked⟩

    · exact ⟨Witness.rising, case_31_16_3_checked⟩

    · exact ⟨Witness.rising, case_31_16_4_checked⟩

    · exact ⟨Witness.rising, case_31_16_5_checked⟩

    · exact ⟨Witness.rising, case_31_16_6_checked⟩

    · exact ⟨Witness.rising, case_31_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_16_8, case_31_16_8_checked⟩

    · exact ⟨Witness.linear .conditional case_31_16_9, case_31_16_9_checked⟩

    · exact ⟨Witness.linear .conditional case_31_16_10, case_31_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_17_1_checked⟩

    · exact ⟨Witness.rising, case_31_17_2_checked⟩

    · exact ⟨Witness.rising, case_31_17_3_checked⟩

    · exact ⟨Witness.rising, case_31_17_4_checked⟩

    · exact ⟨Witness.rising, case_31_17_5_checked⟩

    · exact ⟨Witness.rising, case_31_17_6_checked⟩

    · exact ⟨Witness.rising, case_31_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_17_8, case_31_17_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_17_9, case_31_17_9_checked⟩

    · exact ⟨Witness.linear .conditional case_31_17_10, case_31_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_18_1_checked⟩

    · exact ⟨Witness.rising, case_31_18_2_checked⟩

    · exact ⟨Witness.rising, case_31_18_3_checked⟩

    · exact ⟨Witness.rising, case_31_18_4_checked⟩

    · exact ⟨Witness.rising, case_31_18_5_checked⟩

    · exact ⟨Witness.rising, case_31_18_6_checked⟩

    · exact ⟨Witness.rising, case_31_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_18_8, case_31_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_18_9, case_31_18_9_checked⟩

    · exact ⟨Witness.linear .conditional case_31_18_10, case_31_18_10_checked⟩

    · exact ⟨Witness.linear .conditional case_31_18_11, case_31_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_19_1_checked⟩

    · exact ⟨Witness.rising, case_31_19_2_checked⟩

    · exact ⟨Witness.rising, case_31_19_3_checked⟩

    · exact ⟨Witness.rising, case_31_19_4_checked⟩

    · exact ⟨Witness.rising, case_31_19_5_checked⟩

    · exact ⟨Witness.rising, case_31_19_6_checked⟩

    · exact ⟨Witness.rising, case_31_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_19_8, case_31_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_19_9, case_31_19_9_checked⟩

    · exact ⟨Witness.linear .conditional case_31_19_10, case_31_19_10_checked⟩

    · exact ⟨Witness.linear .conditional case_31_19_11, case_31_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_31_19_12, case_31_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_20_1_checked⟩

    · exact ⟨Witness.rising, case_31_20_2_checked⟩

    · exact ⟨Witness.rising, case_31_20_3_checked⟩

    · exact ⟨Witness.rising, case_31_20_4_checked⟩

    · exact ⟨Witness.rising, case_31_20_5_checked⟩

    · exact ⟨Witness.rising, case_31_20_6_checked⟩

    · exact ⟨Witness.linear .positive case_31_20_7, case_31_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_20_8, case_31_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_20_9, case_31_20_9_checked⟩

    · exact ⟨Witness.linear .conditional case_31_20_10, case_31_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_31_20_11, case_31_20_11_checked⟩

    · exact ⟨Witness.linear .negative case_31_20_12, case_31_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_21_1_checked⟩

    · exact ⟨Witness.rising, case_31_21_2_checked⟩

    · exact ⟨Witness.rising, case_31_21_3_checked⟩

    · exact ⟨Witness.rising, case_31_21_4_checked⟩

    · exact ⟨Witness.rising, case_31_21_5_checked⟩

    · exact ⟨Witness.rising, case_31_21_6_checked⟩

    · exact ⟨Witness.linear .positive case_31_21_7, case_31_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_21_8, case_31_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_21_9, case_31_21_9_checked⟩

    · exact ⟨Witness.linear .conditional case_31_21_10, case_31_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_31_21_11, case_31_21_11_checked⟩

    · exact ⟨Witness.linear .negative case_31_21_12, case_31_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_31_21_13, case_31_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_22_1_checked⟩

    · exact ⟨Witness.rising, case_31_22_2_checked⟩

    · exact ⟨Witness.rising, case_31_22_3_checked⟩

    · exact ⟨Witness.rising, case_31_22_4_checked⟩

    · exact ⟨Witness.rising, case_31_22_5_checked⟩

    · exact ⟨Witness.rising, case_31_22_6_checked⟩

    · exact ⟨Witness.linear .positive case_31_22_7, case_31_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_22_8, case_31_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_22_9, case_31_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_31_22_10, case_31_22_10_checked⟩

    · exact ⟨Witness.linear .conditional case_31_22_11, case_31_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_31_22_12, case_31_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_31_22_13, case_31_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_31_22_14, case_31_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_23_1_checked⟩

    · exact ⟨Witness.rising, case_31_23_2_checked⟩

    · exact ⟨Witness.rising, case_31_23_3_checked⟩

    · exact ⟨Witness.rising, case_31_23_4_checked⟩

    · exact ⟨Witness.rising, case_31_23_5_checked⟩

    · exact ⟨Witness.rising, case_31_23_6_checked⟩

    · exact ⟨Witness.linear .positive case_31_23_7, case_31_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_23_8, case_31_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_23_9, case_31_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_31_23_10, case_31_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_31_23_11, case_31_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_31_23_12, case_31_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_31_23_13, case_31_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_31_23_14, case_31_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_24_1_checked⟩

    · exact ⟨Witness.rising, case_31_24_2_checked⟩

    · exact ⟨Witness.rising, case_31_24_3_checked⟩

    · exact ⟨Witness.rising, case_31_24_4_checked⟩

    · exact ⟨Witness.rising, case_31_24_5_checked⟩

    · exact ⟨Witness.rising, case_31_24_6_checked⟩

    · exact ⟨Witness.linear .positive case_31_24_7, case_31_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_24_8, case_31_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_24_9, case_31_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_31_24_10, case_31_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_31_24_11, case_31_24_11_checked⟩

    · exact ⟨Witness.linear .conditional case_31_24_12, case_31_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_31_24_13, case_31_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_31_24_14, case_31_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_31_24_15, case_31_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_25_1_checked⟩

    · exact ⟨Witness.rising, case_31_25_2_checked⟩

    · exact ⟨Witness.rising, case_31_25_3_checked⟩

    · exact ⟨Witness.rising, case_31_25_4_checked⟩

    · exact ⟨Witness.rising, case_31_25_5_checked⟩

    · exact ⟨Witness.rising, case_31_25_6_checked⟩

    · exact ⟨Witness.linear .positive case_31_25_7, case_31_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_25_8, case_31_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_25_9, case_31_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_31_25_10, case_31_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_31_25_11, case_31_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_31_25_12, case_31_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_31_25_13, case_31_25_13_checked⟩

    · exact ⟨Witness.linear .negative case_31_25_14, case_31_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_31_25_15, case_31_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_31_25_16, case_31_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_26_1_checked⟩

    · exact ⟨Witness.rising, case_31_26_2_checked⟩

    · exact ⟨Witness.rising, case_31_26_3_checked⟩

    · exact ⟨Witness.rising, case_31_26_4_checked⟩

    · exact ⟨Witness.rising, case_31_26_5_checked⟩

    · exact ⟨Witness.rising, case_31_26_6_checked⟩

    · exact ⟨Witness.linear .positive case_31_26_7, case_31_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_26_8, case_31_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_26_9, case_31_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_31_26_10, case_31_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_31_26_11, case_31_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_31_26_12, case_31_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_31_26_13, case_31_26_13_checked⟩

    · exact ⟨Witness.linear .negative case_31_26_14, case_31_26_14_checked⟩

    · exact ⟨Witness.linear .negative case_31_26_15, case_31_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_31_26_16, case_31_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_27_1_checked⟩

    · exact ⟨Witness.rising, case_31_27_2_checked⟩

    · exact ⟨Witness.rising, case_31_27_3_checked⟩

    · exact ⟨Witness.rising, case_31_27_4_checked⟩

    · exact ⟨Witness.rising, case_31_27_5_checked⟩

    · exact ⟨Witness.rising, case_31_27_6_checked⟩

    · exact ⟨Witness.linear .positive case_31_27_7, case_31_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_27_8, case_31_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_27_9, case_31_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_31_27_10, case_31_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_31_27_11, case_31_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_31_27_12, case_31_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_31_27_13, case_31_27_13_checked⟩

    · exact ⟨Witness.linear .negative case_31_27_14, case_31_27_14_checked⟩

    · exact ⟨Witness.linear .negative case_31_27_15, case_31_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_31_27_16, case_31_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_31_27_17, case_31_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_28_1_checked⟩

    · exact ⟨Witness.rising, case_31_28_2_checked⟩

    · exact ⟨Witness.rising, case_31_28_3_checked⟩

    · exact ⟨Witness.rising, case_31_28_4_checked⟩

    · exact ⟨Witness.rising, case_31_28_5_checked⟩

    · exact ⟨Witness.rising, case_31_28_6_checked⟩

    · exact ⟨Witness.linear .positive case_31_28_7, case_31_28_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_28_8, case_31_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_28_9, case_31_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_31_28_10, case_31_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_31_28_11, case_31_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_31_28_12, case_31_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_31_28_13, case_31_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_31_28_14, case_31_28_14_checked⟩

    · exact ⟨Witness.linear .negative case_31_28_15, case_31_28_15_checked⟩

    · exact ⟨Witness.linear .negative case_31_28_16, case_31_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_31_28_17, case_31_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_31_28_18, case_31_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_29_1_checked⟩

    · exact ⟨Witness.rising, case_31_29_2_checked⟩

    · exact ⟨Witness.rising, case_31_29_3_checked⟩

    · exact ⟨Witness.rising, case_31_29_4_checked⟩

    · exact ⟨Witness.rising, case_31_29_5_checked⟩

    · exact ⟨Witness.rising, case_31_29_6_checked⟩

    · exact ⟨Witness.linear .positive case_31_29_7, case_31_29_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_29_8, case_31_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_29_9, case_31_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_31_29_10, case_31_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_31_29_11, case_31_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_31_29_12, case_31_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_31_29_13, case_31_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_31_29_14, case_31_29_14_checked⟩

    · exact ⟨Witness.linear .negative case_31_29_15, case_31_29_15_checked⟩

    · exact ⟨Witness.linear .negative case_31_29_16, case_31_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_31_29_17, case_31_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_31_29_18, case_31_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_31_30_1_checked⟩

    · exact ⟨Witness.rising, case_31_30_2_checked⟩

    · exact ⟨Witness.rising, case_31_30_3_checked⟩

    · exact ⟨Witness.rising, case_31_30_4_checked⟩

    · exact ⟨Witness.rising, case_31_30_5_checked⟩

    · exact ⟨Witness.rising, case_31_30_6_checked⟩

    · exact ⟨Witness.linear .positive case_31_30_7, case_31_30_7_checked⟩

    · exact ⟨Witness.linear .positive case_31_30_8, case_31_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_31_30_9, case_31_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_31_30_10, case_31_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_31_30_11, case_31_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_31_30_12, case_31_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_31_30_13, case_31_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_31_30_14, case_31_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_31_30_15, case_31_30_15_checked⟩

    · exact ⟨Witness.linear .negative case_31_30_16, case_31_30_16_checked⟩

    · exact ⟨Witness.linear .negative case_31_30_17, case_31_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_31_30_18, case_31_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_31_30_19, case_31_30_19_checked⟩


#print axioms coverage_31
end ForestUnimodality.FiniteRows.FiniteData
