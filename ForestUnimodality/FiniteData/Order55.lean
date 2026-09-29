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

theorem case_55_28_1_checked :
    (Witness.rising).check 55 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_28_2_checked :
    (Witness.rising).check 55 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_28_3_checked :
    (Witness.rising).check 55 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_28_4_checked :
    (Witness.rising).check 55 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_28_5_checked :
    (Witness.rising).check 55 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_28_6_checked :
    (Witness.rising).check 55 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_28_7_checked :
    (Witness.rising).check 55 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_28_8_checked :
    (Witness.rising).check 55 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_28_9_checked :
    (Witness.rising).check 55 28 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_28_10_checked :
    (Witness.rising).check 55 28 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_28_11 : Certificate := {
  objectiveScale := 4388756040000000
  eta := 3843448160290698960000
  rows := #[⟨.count 2, 919330274238031656000⟩, ⟨.count 3, 164043435764495327040⟩, ⟨.count 4, 20315368847250837360⟩, ⟨.count 5, 2788167920070733200⟩, ⟨.count 6, 441554983449980400⟩, ⟨.count 7, 82356821109763200⟩, ⟨.count 8, 18474638248946880⟩, ⟨.count 9, 5957104343430240⟩, ⟨.count 10, 4393144796040000⟩, ⟨.count 12, 540098389630800⟩, ⟨.path 11, 1577221522390800⟩, ⟨.path 12, 536115808659600⟩, ⟨.privateRow 9 5, 35926161887616⟩, ⟨.privateRow 9 6, 73637474676480⟩, ⟨.privateRow 10 2, 36695680061040⟩, ⟨.privateRow 11 0, 32350390872800⟩, ⟨.hall 9 3, 2427790545180⟩, ⟨.hall 9 4, 522280991232⟩, ⟨.hall 8 5, 1740029899608⟩, ⟨.hall 7 7, 1016418927095⟩, ⟨.hall 7 8, 11779841920⟩, ⟨.hall 6 10, 68412961800⟩, ⟨.hall 6 11, 548379369900⟩, ⟨.hall 10 17, 19525087982400⟩, ⟨.hall 5 18, 54937048795200⟩, ⟨.hall 4 23, 349617689794453080⟩]
  caps := #[0, 0, 38496067642890000, 17340976680492960, 5061103853390640, 447749931070200, 0, 109582303347720, 6948895592544, 38382412598112, 0, 7948845586000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_28_11_checked :
    (Witness.linear .positive case_55_28_11).check 55 28 11 = true := by
  change case_55_28_11.check 55 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_28_12 : Certificate := {
  objectiveScale := 25697880000000
  eta := 36452974818628368000
  rows := #[⟨.count 2, 9657317955681396000⟩, ⟨.count 3, 1939833964228960800⟩, ⟨.count 4, 272874162821420160⟩, ⟨.count 5, 42670706309431200⟩, ⟨.count 6, 7369567614208800⟩, ⟨.count 7, 1414361461312800⟩, ⟨.count 8, 306031427301600⟩, ⟨.count 9, 82275874480800⟩, ⟨.count 10, 31778512365600⟩, ⟨.count 11, 25632788781600⟩, ⟨.count 13, 4394192362560⟩, ⟨.path 12, 5969466360000⟩, ⟨.path 13, 4420585219050⟩, ⟨.privateRow 8 11, 4569793610382⟩, ⟨.privateRow 9 8, 3801812894880⟩, ⟨.privateRow 9 9, 4369050766080⟩, ⟨.privateRow 10 5, 1305966261600⟩, ⟨.privateRow 10 6, 820414702800⟩, ⟨.privateRow 11 2, 536150364750⟩, ⟨.privateRow 12 0, 255789383850⟩, ⟨.hall 10 3, 15115350250⟩, ⟨.hall 10 4, 5182405800⟩, ⟨.hall 9 5, 15195840660⟩, ⟨.hall 8 7, 10026196488⟩, ⟨.hall 7 9, 10041204360⟩, ⟨.hall 6 13, 8524641840⟩, ⟨.hall 6 14, 18434260845⟩, ⟨.hall 11 16, 132554822400⟩, ⟨.hall 5 22, 6095815187061600⟩, ⟨.hall 4 23, 4525232953230990⟩]
  caps := #[0, 0, 0, 0, 127235600434800, 0, 12406679485200, 349403085900, 656394599952, 0, 61243146000, 65091218400, 42940912950, 26392856490, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_28_12_checked :
    (Witness.linear .positive case_55_28_12).check 55 28 12 = true := by
  change case_55_28_12.check 55 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_28_13 : Certificate := {
  objectiveScale := 50992656000000
  eta := 100678467087270072000
  rows := #[⟨.count 2, 29271575176611768000⟩, ⟨.count 3, 6494876859815023680⟩, ⟨.count 4, 1055351858385464640⟩, ⟨.count 5, 180533728748973600⟩, ⟨.count 6, 34398082812693600⟩, ⟨.count 7, 7090605305784000⟩, ⟨.count 8, 1597980317693760⟩, ⟨.count 9, 416152085469120⟩, ⟨.count 10, 132891960801600⟩, ⟨.count 11, 55362726619200⟩, ⟨.count 12, 51239970381600⟩, ⟨.path 13, 4488729950250⟩, ⟨.path 14, 12187712216680⟩, ⟨.privateRow 9 9, 959867213760⟩, ⟨.privateRow 9 10, 24976406879424⟩, ⟨.privateRow 10 7, 6629427724920⟩, ⟨.privateRow 10 8, 12577570387200⟩, ⟨.privateRow 11 4, 1514481883200⟩, ⟨.privateRow 11 5, 4703484139200⟩, ⟨.privateRow 11 6, 3631951923600⟩, ⟨.privateRow 12 2, 1928860954020⟩, ⟨.privateRow 13 0, 1538671524390⟩, ⟨.privateRow 14 0, 813052403592⟩, ⟨.privateRow 15 0, 538482447360⟩, ⟨.privateRow 15 6, 80982711810⟩, ⟨.privateRow 16 0, 741869597700⟩, ⟨.privateRow 17 0, 1052998346400⟩, ⟨.privateRow 18 0, 1075713256800⟩, ⟨.privateRow 19 0, 2767065485184⟩, ⟨.privateRow 20 0, 7301978363680⟩, ⟨.privateRow 21 0, 18838280646900⟩, ⟨.privateRow 22 0, 55588369122000⟩, ⟨.privateRow 23 0, 44388342158160⟩, ⟨.privateRow 23 1, 15218860168512⟩, ⟨.privateRow 24 0, 350033783875776⟩, ⟨.privateRow 25 0, 2625253379068320⟩, ⟨.privateRow 26 0, 36461852487060000⟩, ⟨.privateRow 27 0, 853207348197204000⟩, ⟨.hall 17 2, 161816695040⟩, ⟨.hall 11 3, 114328534320⟩, ⟨.hall 18 3, 74117825496⟩, ⟨.hall 22 3, 120482643000720⟩, ⟨.hall 23 4, 11026064192086944⟩, ⟨.hall 10 5, 44651261600⟩, ⟨.hall 22 5, 1204826430007200⟩, ⟨.hall 9 6, 49405070880⟩, ⟨.hall 21 6, 400236257678400⟩, ⟨.hall 9 7, 9283192380⟩, ⟨.hall 14 7, 1721002140⟩, ⟨.hall 20 7, 112412035335600⟩, ⟨.hall 8 8, 51876528704⟩, ⟨.hall 19 8, 38431465072000⟩, ⟨.hall 18 9, 14745546335520⟩, ⟨.hall 7 10, 18725537400⟩, ⟨.hall 17 10, 7281751276800⟩, ⟨.hall 7 11, 39107444640⟩, ⟨.hall 16 11, 4809882277200⟩, ⟨.hall 15 12, 3329918499600⟩, ⟨.hall 12 15, 386508397275⟩, ⟨.hall 6 16, 758168080800⟩, ⟨.hall 6 18, 2886694256160⟩, ⟨.hall 5 22, 26748800970091200⟩, ⟨.hall 4 23, 18850777735810020⟩]
  caps := #[0, 205475668475337000, 0, 0, 0, 0, 3168805582800, 0, 0, 2872092179736, 0, 118659331050, 0, 448534009755, 0, 595275517980, 254840701500, 0, 1903184992800, 1290199184560, 9992180918720, 0, 7494135689040, 289158343201728, 0, 19251858113167680, 0, 0] }

theorem case_55_28_13_checked :
    (Witness.linear .positive case_55_28_13).check 55 28 13 = true := by
  change case_55_28_13.check 55 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_28_14 : Certificate := {
  objectiveScale := 27886608750000
  eta := 75651051540152088000
  rows := #[⟨.count 2, 24546119094288792000⟩, ⟨.count 3, 6342612163829061120⟩, ⟨.count 4, 1152486233410992480⟩, ⟨.count 5, 220673472443424000⟩, ⟨.count 6, 45449050594147200⟩, ⟨.count 7, 10099789020921600⟩, ⟨.count 8, 2386593980971200⟩, ⟨.count 9, 602929005719040⟩, ⟨.count 10, 182043781920000⟩, ⟨.count 11, 62430308740800⟩, ⟨.count 12, 28270328486400⟩, ⟨.count 13, 27563570274240⟩, ⟨.path 15, 6854092868480⟩, ⟨.path 16, 739762228128⟩, ⟨.privateRow 5 23, 11908758081860640⟩, ⟨.privateRow 8 14, 65841334982280⟩, ⟨.privateRow 9 11, 12621702213120⟩, ⟨.privateRow 9 12, 33268501145880⟩, ⟨.privateRow 10 9, 14144801855184⟩, ⟨.privateRow 10 10, 25506356555680⟩, ⟨.privateRow 10 11, 39093902167320⟩, ⟨.privateRow 11 6, 1597344949200⟩, ⟨.privateRow 11 7, 6142760769600⟩, ⟨.privateRow 11 8, 535422888000⟩, ⟨.privateRow 12 4, 1891484317800⟩, ⟨.privateRow 12 5, 3558331276500⟩, ⟨.privateRow 12 6, 689356968300⟩, ⟨.privateRow 13 2, 866620188720⟩, ⟨.privateRow 14 0, 1097438446104⟩, ⟨.privateRow 15 0, 487999717920⟩, ⟨.privateRow 16 0, 237851321400⟩, ⟨.privateRow 17 0, 303406303200⟩, ⟨.privateRow 18 0, 446834737440⟩, ⟨.privateRow 19 0, 400496320224⟩, ⟨.privateRow 20 0, 1056865289480⟩, ⟨.privateRow 21 0, 617648545800⟩, ⟨.privateRow 22 0, 2470594183200⟩, ⟨.privateRow 22 6, 406412743136400⟩, ⟨.privateRow 23 0, 6341191736880⟩, ⟨.privateRow 25 3, 3500337838757760⟩, ⟨.hall 18 2, 9102189096⟩, ⟨.hall 12 3, 122687594865⟩, ⟨.hall 23 4, 525050675813664⟩, ⟨.hall 11 5, 47811383400⟩, ⟨.hall 18 5, 39009381840⟩, ⟨.hall 22 5, 95117876053200⟩, ⟨.hall 10 6, 69600072300⟩, ⟨.hall 20 7, 114573805245900⟩, ⟨.hall 19 8, 39968723674880⟩, ⟨.hall 9 9, 42452315136⟩, ⟨.hall 18 9, 14090188720608⟩, ⟨.hall 8 10, 52508885184⟩, ⟨.hall 17 10, 8109223012800⟩, ⟨.hall 8 11, 16588957000⟩, ⟨.hall 16 11, 4809882277200⟩, ⟨.hall 15 12, 3261960979200⟩, ⟨.hall 7 14, 321444955260⟩, ⟨.hall 13 14, 612523783872⟩, ⟨.hall 12 15, 276077426625⟩, ⟨.hall 6 21, 20507728516329600⟩, ⟨.hall 5 22, 22009449406744800⟩]
  caps := #[0, 109260545395510080, 20860599241081600, 573870461521280, 0, 23146722391936, 0, 2950804772916, 4652952378360, 0, 290790988488, 561454537504, 0, 1333840399320, 0, 333355989824, 411300879528, 606812606400, 2532063512160, 0, 0, 44779519570500, 25941238923600, 0, 0, 0, 0, 0] }

theorem case_55_28_14_checked :
    (Witness.linear .positive case_55_28_14).check 55 28 14 = true := by
  change case_55_28_14.check 55 28 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_28_15 : Certificate := {
  objectiveScale := 17847429600000
  eta := 57449294778611736000
  rows := #[⟨.count 2, 19951925680919232000⟩, ⟨.count 3, 5460527028462105600⟩, ⟨.count 4, 1118357939483104320⟩, ⟨.count 5, 254154964814150400⟩, ⟨.count 6, 57900845277475200⟩, ⟨.count 7, 14388740522956800⟩, ⟨.count 8, 3562596812174400⟩, ⟨.count 9, 1019081091188160⟩, ⟨.count 10, 305833553625600⟩, ⟨.count 11, 98946149702400⟩, ⟨.count 12, 37104806138400⟩, ⟨.count 13, 17610058786320⟩, ⟨.count 14, 17610058786320⟩, ⟨.path 16, 1187265932160⟩, ⟨.path 17, 2814471003960⟩, ⟨.privateRow 5 23, 12593606789443680⟩, ⟨.privateRow 10 10, 8414468142080⟩, ⟨.privateRow 10 11, 37136931511680⟩, ⟨.privateRow 10 12, 36356743874880⟩, ⟨.privateRow 11 8, 5707607986080⟩, ⟨.privateRow 11 9, 18228174764800⟩, ⟨.privateRow 11 10, 12502124434800⟩, ⟨.privateRow 12 6, 3366471408300⟩, ⟨.privateRow 12 7, 9313011858150⟩, ⟨.privateRow 12 8, 13488938563100⟩, ⟨.privateRow 13 4, 1815975961800⟩, ⟨.privateRow 13 5, 3351747278880⟩, ⟨.privateRow 14 2, 159861976560⟩, ⟨.privateRow 15 0, 1270482024240⟩, ⟨.privateRow 16 0, 339787602000⟩, ⟨.privateRow 17 0, 232016584800⟩, ⟨.privateRow 18 0, 380636998560⟩, ⟨.privateRow 19 0, 546131345760⟩, ⟨.privateRow 20 0, 1249022614840⟩, ⟨.privateRow 21 0, 2779418456100⟩, ⟨.privateRow 22 0, 11117673824400⟩, ⟨.privateRow 23 0, 44388342158160⟩, ⟨.privateRow 24 0, 175016891937888⟩, ⟨.privateRow 25 0, 437542229844720⟩, ⟨.privateRow 26 0, 7292370497412000⟩, ⟨.hall 20 2, 308824272900⟩, ⟨.hall 13 3, 213990680904⟩, ⟨.hall 24 3, 10501013516273280⟩, ⟨.hall 23 4, 1225118243565216⟩, ⟨.hall 12 5, 83825307225⟩, ⟨.hall 22 5, 190235752106400⟩, ⟨.hall 21 6, 44470695297600⟩, ⟨.hall 11 7, 63669291840⟩, ⟨.hall 20 7, 10808849551500⟩, ⟨.hall 10 8, 93409868720⟩, ⟨.hall 19 8, 3843146507200⟩, ⟨.hall 18 9, 1638394037280⟩, ⟨.hall 9 10, 122940347040⟩, ⟨.hall 8 12, 232188194700⟩, ⟨.hall 8 13, 12403963572⟩, ⟨.hall 14 13, 1421930212560⟩, ⟨.hall 13 14, 1174003919088⟩, ⟨.hall 7 16, 3490277327680⟩, ⟨.hall 7 20, 4047656803476000⟩, ⟨.hall 6 21, 30134286451432800⟩, ⟨.hall 5 22, 31264832302704000⟩, ⟨.hall 4 23, 5797434545442540⟩]
  caps := #[0, 0, 530354217993600, 0, 177996808614240, 119473817042580, 27269630868480, 5381892395880, 5929426039680, 1947868466544, 723773593760, 229064894520, 603090017530, 237370813680, 237370813680, 0, 8099987280, 1065422903160, 0, 0, 16045136667560, 3705891274800, 54764837727600, 101459067790080, 1487643581472048, 6417286037722560, 0, 0] }

theorem case_55_28_15_checked :
    (Witness.linear .positive case_55_28_15).check 55 28 15 = true := by
  change case_55_28_15.check 55 28 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_28_16 : Certificate := {
  objectiveScale := 13006224000000
  eta := 32990684130291888000
  rows := #[⟨.count 2, 10282242401350920000⟩, ⟨.count 3, 2499241216873040640⟩, ⟨.count 4, 603808277185713600⟩, ⟨.count 5, 162841803803078400⟩, ⟨.count 6, 44722695904286400⟩, ⟨.count 7, 12624736276152000⟩, ⟨.count 8, 3707867750146560⟩, ⟨.count 9, 1159982978394240⟩, ⟨.count 10, 385932817670400⟩, ⟨.count 11, 136639921017600⟩, ⟨.count 12, 55657209207600⟩, ⟨.count 13, 28329225004080⟩, ⟨.count 14, 19141368246000⟩, ⟨.count 15, 19435850834400⟩, ⟨.path 15, 2167697806560⟩, ⟨.privateRow 4 24, 36972318421878840⟩, ⟨.privateRow 10 11, 2662390310580⟩, ⟨.privateRow 11 9, 13373673913600⟩, ⟨.privateRow 11 10, 27346724004600⟩, ⟨.privateRow 12 7, 6051617191620⟩, ⟨.privateRow 12 8, 18405161775000⟩, ⟨.privateRow 12 9, 6349780812375⟩, ⟨.privateRow 13 5, 2816324390880⟩, ⟨.privateRow 13 6, 8834477652000⟩, ⟨.privateRow 13 7, 8140807554880⟩, ⟨.privateRow 14 3, 1253303873250⟩, ⟨.privateRow 14 4, 2018544287760⟩, ⟨.privateRow 15 1, 480233144160⟩, ⟨.privateRow 16 0, 1370476661400⟩, ⟨.privateRow 17 0, 1079769490800⟩, ⟨.privateRow 18 0, 1737690645600⟩, ⟨.privateRow 19 0, 2184525383040⟩, ⟨.privateRow 20 0, 5380405110080⟩, ⟨.privateRow 21 0, 13279443734700⟩, ⟨.privateRow 21 6, 9882376732800⟩, ⟨.privateRow 21 7, 22235347648800⟩, ⟨.privateRow 22 0, 55588369122000⟩, ⟨.privateRow 23 0, 247306477738320⟩, ⟨.privateRow 24 0, 1400135135503104⟩, ⟨.privateRow 25 0, 11813640205807440⟩, ⟨.privateRow 26 0, 138555039450828000⟩, ⟨.privateRow 27 0, 3981634291586952000⟩, ⟨.hall 14 2, 384229662960⟩, ⟨.hall 20 2, 1647062788800⟩, ⟨.hall 25 2, 14584740994824000⟩, ⟨.hall 14 3, 70369865280⟩, ⟨.hall 23 3, 43754222984472⟩, ⟨.hall 13 4, 180870950832⟩, ⟨.hall 18 5, 93622516416⟩, ⟨.hall 19 5, 411765697200⟩, ⟨.hall 12 6, 106933806045⟩, ⟨.hall 11 7, 152922591360⟩, ⟨.hall 10 8, 117576702880⟩, ⟨.hall 10 9, 71468762960⟩, ⟨.hall 9 10, 242747376480⟩, ⟨.hall 8 12, 103439583324⟩, ⟨.hall 15 12, 271830081600⟩, ⟨.hall 8 13, 568313151120⟩, ⟨.hall 7 16, 7376087690400⟩, ⟨.hall 6 21, 54398778022789200⟩, ⟨.hall 5 22, 69386422800895200⟩, ⟨.hall 4 23, 63735318147380880⟩, ⟨.assumptionRow 16, 17279505603360⟩]
  caps := #[0, 178055462720678400, 0, 23189577143040, 283540192024320, 14169074359440, 20507627780640, 0, 5929426039680, 393178151520, 909021253140, 798225828400, 392400874800, 484779632337, 321095800080, 11352575520, 0, 1155530745600, 49648304160, 1440168585856, 0, 0, 25941238923600, 190235752106400, 1750168919378880, 0, 240648226414596000, 0] }

theorem case_55_28_16_checked :
    (Witness.linear .conditional case_55_28_16).check 55 28 16 = true := by
  change case_55_28_16.check 55 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_28_17 : Certificate := {
  objectiveScale := 457626400000000
  eta := 597245143738042800000
  rows := #[⟨.count 2, 166703589570838320000⟩, ⟨.count 3, 47097045620485660800⟩, ⟨.count 4, 13546307435992531200⟩, ⟨.count 5, 3983536649108016000⟩, ⟨.count 6, 1200041712605736000⟩, ⟨.count 7, 371478541385952000⟩, ⟨.count 8, 118292049491616000⟩, ⟨.count 9, 39911278748140800⟩, ⟨.count 10, 14963998873824000⟩, ⟨.count 11, 5689403607888000⟩, ⟨.count 12, 2438315831952000⟩, ⟨.count 13, 1056603527179200⟩, ⟨.count 14, 505332121694400⟩, ⟨.count 15, 450558360252000⟩, ⟨.count 16, 424054927296000⟩, ⟨.path 15, 45521144011200⟩, ⟨.privateRow 11 10, 469030449888000⟩, ⟨.privateRow 12 8, 244420548372000⟩, ⟨.privateRow 12 9, 816360950530125⟩, ⟨.privateRow 13 6, 18375713516160⟩, ⟨.privateRow 14 4, 19688264481600⟩, ⟨.privateRow 14 5, 117473311406880⟩, ⟨.privateRow 15 3, 78385910803200⟩, ⟨.privateRow 15 4, 38164943456640⟩, ⟨.privateRow 16 1, 29080155604500⟩, ⟨.privateRow 17 0, 45778656924000⟩, ⟨.privateRow 18 0, 41704575494400⟩, ⟨.privateRow 19 0, 63351236108160⟩, ⟨.privateRow 19 6, 35498537474400⟩, ⟨.privateRow 20 0, 158529793422000⟩, ⟨.privateRow 21 0, 472501137537000⟩, ⟨.privateRow 22 0, 1667651073660000⟩, ⟨.privateRow 23 0, 7228958580043200⟩, ⟨.privateRow 24 0, 35440920617422320⟩, ⟨.privateRow 25 0, 315030405488198400⟩, ⟨.privateRow 25 3, 157515202744099200⟩, ⟨.privateRow 26 0, 4156651183524840000⟩, ⟨.privateRow 27 0, 119449028747608560000⟩, ⟨.hall 15 2, 9792060894000⟩, ⟨.hall 23 2, 5250506758136640⟩, ⟨.hall 24 2, 26252533790683200⟩, ⟨.hall 25 2, 437542229844720000⟩, ⟨.hall 15 3, 2956152137400⟩, ⟨.hall 14 4, 6702729667920⟩, ⟨.hall 23 4, 15751520274409920⟩, ⟨.hall 13 5, 8716684616640⟩, ⟨.hall 22 5, 4755893802660000⟩, ⟨.hall 12 6, 8752619729700⟩, ⟨.hall 19 6, 6588251155200⟩, ⟨.hall 20 6, 27794184561000⟩, ⟨.hall 21 6, 1111767382440000⟩, ⟨.hall 12 7, 1034807697000⟩, ⟨.hall 20 7, 194559291927000⟩, ⟨.hall 11 8, 8755577476800⟩, ⟨.hall 10 9, 6038047528800⟩, ⟨.hall 10 10, 5534419275000⟩, ⟨.hall 9 11, 7899167568600⟩, ⟨.hall 16 11, 8834477652000⟩, ⟨.hall 9 12, 13370305370400⟩, ⟨.hall 8 14, 66929645742960⟩, ⟨.hall 6 19, 9881927533857600⟩, ⟨.hall 7 19, 544766017395600⟩, ⟨.hall 8 19, 105570465923482560⟩, ⟨.hall 5 20, 11460334495896000⟩, ⟨.hall 7 20, 1415131642195128000⟩, ⟨.hall 4 23, 2758703759170959600⟩, ⟨.hall 3 24, 1883881824819426432⟩, ⟨.assumptionRow 17, 413558904528000⟩]
  caps := #[0, 7325925194839680000, 644566464061520000, 46485081984140800, 2397376574208000, 0, 68024572616000, 278030503296000, 56201421619200, 2589067120640, 6898501209600, 19964072128000, 0, 0, 722719395200, 30170426674960, 0, 1607253984000, 0, 119056633375680, 360294985050000, 83382553683000, 0, 0, 9188386826739120, 183767736534782400, 7219446792437880000, 0] }

theorem case_55_28_17_checked :
    (Witness.linear .conditional case_55_28_17).check 55 28 17 = true := by
  change case_55_28_17.check 55 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_28_18 : Certificate := {
  objectiveScale := 121136400000000
  eta := 79632685831739040000
  rows := #[⟨.count 2, 23846051526537240000⟩, ⟨.count 3, 7193194258647196800⟩, ⟨.count 4, 2209588260715836000⟩, ⟨.count 5, 689604601385700000⟩, ⟨.count 6, 217906406958240000⟩, ⟨.count 7, 69522520315248000⟩, ⟨.count 8, 22344053792860800⟩, ⟨.count 9, 7192549823659200⟩, ⟨.count 10, 2739758917896000⟩, ⟨.count 11, 1018909755864000⟩, ⟨.count 12, 357796344906000⟩, ⟨.count 13, 156959219617200⟩, ⟨.count 14, 65080652036400⟩, ⟨.count 15, 48589627086000⟩, ⟨.count 16, 53006865912000⟩, ⟨.count 17, 54613134576000⟩, ⟨.count 19, 138353274259200⟩, ⟨.path 14, 15157673230700⟩, ⟨.privateRow 3 25, 848831925898756800⟩, ⟨.privateRow 14 5, 12660647854140⟩, ⟨.privateRow 14 6, 34879826581600⟩, ⟨.privateRow 15 4, 7744892074920⟩, ⟨.privateRow 18 0, 5626807804800⟩, ⟨.hall 16 2, 5621940324000⟩, ⟨.hall 15 3, 5365555133400⟩, ⟨.hall 14 4, 2074763691000⟩, ⟨.hall 13 5, 266181664320⟩, ⟨.hall 14 5, 1770932449000⟩, ⟨.hall 13 6, 3089984978080⟩, ⟨.hall 12 7, 3707417377125⟩, ⟨.hall 11 8, 1807355088000⟩, ⟨.hall 11 9, 2487445121700⟩, ⟨.hall 10 10, 3914239808500⟩, ⟨.hall 17 10, 1654943472000⟩, ⟨.hall 10 11, 2094212813000⟩, ⟨.hall 16 11, 9325281966000⟩, ⟨.hall 9 12, 5834034676800⟩, ⟨.hall 15 12, 51647715504000⟩, ⟨.hall 9 13, 9188943706800⟩, ⟨.hall 8 14, 18887934745680⟩, ⟨.hall 12 15, 274697039491875⟩, ⟨.hall 6 19, 3605046112231200⟩, ⟨.hall 8 19, 100330335660915360⟩, ⟨.hall 7 20, 510836523946320000⟩, ⟨.hall 5 22, 1026445949408880000⟩, ⟨.hall 4 23, 1229858284388533800⟩, ⟨.hall 3 24, 1172963209767725376⟩, ⟨.assumptionRow 18, 50194751684000⟩]
  caps := #[0, 1185056084222010000, 45835308043910000, 22174285839120800, 1854922485385200, 588601363812000, 0, 36530443404000, 3690743456400, 1716730892800, 2881420542000, 2675364692000, 0, 1467601135000, 272513156300, 2328769608880, 748622952000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_28_18_checked :
    (Witness.linear .conditional case_55_28_18).check 55 28 18 = true := by
  change case_55_28_18.check 55 28 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_29_1_checked :
    (Witness.rising).check 55 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_29_2_checked :
    (Witness.rising).check 55 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_29_3_checked :
    (Witness.rising).check 55 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_29_4_checked :
    (Witness.rising).check 55 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_29_5_checked :
    (Witness.rising).check 55 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_29_6_checked :
    (Witness.rising).check 55 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_29_7_checked :
    (Witness.rising).check 55 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_29_8_checked :
    (Witness.rising).check 55 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_29_9_checked :
    (Witness.rising).check 55 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_29_10_checked :
    (Witness.rising).check 55 29 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_29_11 : Certificate := {
  objectiveScale := 7395303784050000000
  eta := 8270650750484416694400000
  rows := #[⟨.count 2, 1800244980022108033814400⟩, ⟨.count 3, 265866960583280311655400⟩, ⟨.count 4, 33532094890550950293600⟩, ⟨.count 5, 4719664830439476918000⟩, ⟨.count 6, 751099000020465096000⟩, ⟨.count 7, 139614904796550183000⟩, ⟨.count 8, 31256533243284148800⟩, ⟨.count 9, 10036501500137112000⟩, ⟨.count 10, 7421950689177024000⟩, ⟨.count 12, 881356644339771600⟩, ⟨.path 11, 2699121844592712000⟩, ⟨.path 12, 876266765182692000⟩, ⟨.privateRow 6 16, 1662082199958930750⟩, ⟨.privateRow 6 17, 27102943190967930000⟩, ⟨.privateRow 7 12, 176895666514476000⟩, ⟨.privateRow 7 13, 5555408406887118780⟩, ⟨.privateRow 7 14, 7178033045676292800⟩, ⟨.privateRow 7 15, 10641379938761446875⟩, ⟨.privateRow 7 16, 11716810825633828200⟩, ⟨.privateRow 8 10, 3447060336654234300⟩, ⟨.privateRow 8 11, 1935611003597871600⟩, ⟨.privateRow 8 12, 3423163904511050700⟩, ⟨.privateRow 8 13, 2282109269674033800⟩, ⟨.privateRow 8 14, 6882172457236876800⟩, ⟨.privateRow 9 5, 67706557739020200⟩, ⟨.privateRow 9 6, 406770378259525280⟩, ⟨.privateRow 9 8, 2056318622372414400⟩, ⟨.privateRow 9 9, 987719195251588800⟩, ⟨.privateRow 10 3, 336865275264117600⟩, ⟨.privateRow 10 4, 153921136451682600⟩, ⟨.privateRow 11 0, 55764506897599500⟩, ⟨.hall 6 12, 371956632606000⟩, ⟨.hall 5 15, 1600827600849750⟩, ⟨.hall 5 16, 475734015870750⟩, ⟨.hall 7 21, 11299210698612154500⟩, ⟨.hall 4 23, 55886824817584917156⟩]
  caps := #[0, 0, 137317065058664805600, 0, 6157774070796146400, 1091190820256871750, 2563549636060784250, 1162805237196519330, 116019028556431200, 57924128505600000, 62522266568077800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_29_11_checked :
    (Witness.linear .positive case_55_29_11).check 55 29 11 = true := by
  change case_55_29_11.check 55 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_29_12 : Certificate := {
  objectiveScale := 40575600000000
  eta := 77859488373947280000
  rows := #[⟨.count 2, 18763653098814624000⟩, ⟨.count 3, 3116797531491243600⟩, ⟨.count 4, 447013967818017600⟩, ⟨.count 5, 70532863304904000⟩, ⟨.count 6, 12178729010448000⟩, ⟨.count 7, 2322423547844400⟩, ⟨.count 8, 503015713200000⟩, ⟨.count 9, 132796148284800⟩, ⟨.count 10, 50893354512000⟩, ⟨.count 11, 40685094450000⟩, ⟨.path 12, 9978622056000⟩, ⟨.path 13, 6651295560000⟩, ⟨.privateRow 7 14, 32616177594000⟩, ⟨.privateRow 7 15, 124586213251500⟩, ⟨.privateRow 7 16, 157207808815200⟩, ⟨.privateRow 7 17, 7281751276800⟩, ⟨.privateRow 8 11, 17331177754800⟩, ⟨.privateRow 8 12, 37877083203960⟩, ⟨.privateRow 8 13, 58182150826800⟩, ⟨.privateRow 8 14, 77841681617700⟩, ⟨.privateRow 8 15, 81847842476400⟩, ⟨.privateRow 9 8, 6208159742400⟩, ⟨.privateRow 9 9, 12724434522800⟩, ⟨.privateRow 9 10, 19063787433600⟩, ⟨.privateRow 9 11, 24502454296320⟩, ⟨.privateRow 9 12, 28243400785600⟩, ⟨.privateRow 9 13, 29566145809200⟩, ⟨.privateRow 10 5, 2154090818880⟩, ⟨.privateRow 10 6, 4522914396000⟩, ⟨.privateRow 10 7, 6627971750400⟩, ⟨.privateRow 10 8, 8354006060400⟩, ⟨.privateRow 10 9, 3808931817600⟩, ⟨.privateRow 11 3, 3633918663375⟩, ⟨.privateRow 11 4, 611509298400⟩, ⟨.privateRow 12 0, 855893838800⟩, ⟨.privateRow 13 0, 391123933200⟩, ⟨.privateRow 14 0, 235392332175⟩, ⟨.privateRow 15 0, 292932680040⟩, ⟨.privateRow 15 11, 108493585200⟩, ⟨.privateRow 16 0, 211351140000⟩, ⟨.privateRow 16 2, 246576330000⟩, ⟨.privateRow 17 0, 609991905600⟩, ⟨.privateRow 17 2, 75317860800⟩, ⟨.privateRow 18 0, 1117812696000⟩, ⟨.privateRow 19 0, 137186103600⟩, ⟨.privateRow 19 7, 3521109992400⟩, ⟨.privateRow 20 0, 136532836440⟩, ⟨.privateRow 20 1, 151703151600⟩, ⟨.privateRow 21 0, 505677172000⟩, ⟨.privateRow 21 5, 2275547274000⟩, ⟨.privateRow 22 0, 2389324637700⟩, ⟨.privateRow 22 7, 382291942032000⟩, ⟨.privateRow 23 0, 15018612008400⟩, ⟨.privateRow 26 3, 241799653335240000⟩, ⟨.hall 19 3, 45510945480⟩, ⟨.hall 20 3, 162539091000⟩, ⟨.hall 21 3, 682664182200⟩, ⟨.hall 24 3, 967198613340960⟩, ⟨.hall 23 4, 80599884445080⟩, ⟨.hall 13 5, 289349775⟩, ⟨.hall 15 5, 45160500⟩, ⟨.hall 22 5, 40049632022400⟩, ⟨.hall 19 6, 546131345760⟩, ⟨.hall 21 6, 3413320911000⟩, ⟨.hall 16 7, 344862000⟩, ⟨.hall 17 7, 10161933600⟩, ⟨.hall 15 8, 180642000⟩, ⟨.hall 18 8, 325181875200⟩, ⟨.hall 20 8, 97090017024000⟩, ⟨.hall 7 12, 5243873040⟩, ⟨.hall 14 12, 10968582240⟩, ⟨.hall 15 12, 67063342500⟩, ⟨.hall 16 12, 1183566384000⟩, ⟨.hall 6 13, 13580892000⟩, ⟨.hall 13 13, 7555803255⟩, ⟨.hall 15 13, 58121563500⟩, ⟨.hall 5 18, 35503650000⟩, ⟨.hall 5 19, 1731394665000⟩, ⟨.hall 8 20, 86997765254400⟩, ⟨.hall 4 23, 745023279696696⟩]
  caps := #[0, 0, 1150422133536000, 1579944980156400, 195046909200000, 104233068276480, 45110520000, 17029856586600, 4135327871220, 287270156160, 0, 0, 104305723600, 464426071200, 0, 460322782920, 0, 0, 2906313009600, 7636693100400, 0, 2781224446000, 298665579712500, 0, 9671986133409600, 145079792001144000, 0] }

theorem case_55_29_12_checked :
    (Witness.linear .positive case_55_29_12).check 55 29 12 = true := by
  change case_55_29_12.check 55 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_29_13 : Certificate := {
  objectiveScale := 1079310960000000
  eta := 3073515393544235640000
  rows := #[⟨.count 2, 812620930956807772800⟩, ⟨.count 3, 149954473012382438400⟩, ⟨.count 4, 24736735317899404800⟩, ⟨.count 5, 4276413236555460000⟩, ⟨.count 6, 789132488055912000⟩, ⟨.count 7, 160705975131702000⟩, ⟨.count 8, 35782525774195200⟩, ⟨.count 9, 9289694191377600⟩, ⟨.count 10, 2900921207184000⟩, ⟨.count 11, 1205906199498000⟩, ⟨.count 12, 1076039378013600⟩, ⟨.path 13, 120101914296000⟩, ⟨.path 14, 242378322732000⟩, ⟨.privateRow 7 16, 9661258553403600⟩, ⟨.privateRow 7 17, 10726702294908600⟩, ⟨.privateRow 8 12, 74546928696240⟩, ⟨.privateRow 8 13, 2367024274414800⟩, ⟨.privateRow 8 14, 3842034017421600⟩, ⟨.privateRow 8 15, 6520808268374400⟩, ⟨.privateRow 8 16, 1543503715954200⟩, ⟨.privateRow 9 10, 613984028112000⟩, ⟨.privateRow 9 11, 1148150132569440⟩, ⟨.privateRow 9 12, 1922786878812800⟩, ⟨.privateRow 9 13, 2390917520791800⟩, ⟨.privateRow 9 14, 3509804115417600⟩, ⟨.privateRow 10 7, 142710792840000⟩, ⟨.privateRow 10 8, 349684688152800⟩, ⟨.privateRow 10 9, 589383780148800⟩, ⟨.privateRow 10 10, 780550194584160⟩, ⟨.privateRow 10 11, 985713536808000⟩, ⟨.privateRow 10 12, 957978631209600⟩, ⟨.privateRow 11 4, 29234089684800⟩, ⟨.privateRow 11 5, 117157220680500⟩, ⟨.privateRow 11 6, 191037856779000⟩, ⟨.privateRow 11 7, 269853135552000⟩, ⟨.privateRow 11 8, 188207229483000⟩, ⟨.privateRow 12 2, 34785755754750⟩, ⟨.privateRow 12 3, 102244354692480⟩, ⟨.privateRow 13 0, 28997873704800⟩, ⟨.privateRow 14 0, 15073827493725⟩, ⟨.privateRow 15 0, 206137811880⟩, ⟨.privateRow 15 5, 24427330707780⟩, ⟨.privateRow 16 0, 301175374500⟩, ⟨.privateRow 16 7, 4216455243000⟩, ⟨.privateRow 17 0, 518948337600⟩, ⟨.privateRow 17 8, 1349265677760⟩, ⟨.privateRow 18 0, 1061922061200⟩, ⟨.privateRow 18 11, 547951783579200⟩, ⟨.privateRow 19 1, 2867189565240⟩, ⟨.hall 19 4, 432353982060⟩, ⟨.hall 20 8, 345883185648000⟩, ⟨.hall 19 9, 108953203479120⟩, ⟨.hall 18 10, 62556863241600⟩, ⟨.hall 7 12, 656772928560⟩, ⟨.hall 8 12, 310588629120⟩, ⟨.hall 16 12, 290611069056000⟩, ⟨.hall 15 13, 215340392767500⟩, ⟨.hall 6 16, 6739798104000⟩, ⟨.hall 9 19, 1513876090446720⟩, ⟨.hall 4 23, 41227892196499008⟩, ⟨.hall 5 23, 1009406033065930500⟩]
  caps := #[0, 0, 157939695744667200, 3811003827321600, 0, 0, 94388917896000, 103167814056840, 51544082116800, 184444009597120, 0, 0, 3271581986400, 0, 30185212628025, 20201505564240, 2678144099400, 2032547655600, 158226387118800, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_29_13_checked :
    (Witness.linear .positive case_55_29_13).check 55 29 13 = true := by
  change case_55_29_13.check 55 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_29_14 : Certificate := {
  objectiveScale := 33404280000000
  eta := 129718402259846400000
  rows := #[⟨.count 2, 37553477454225532800⟩, ⟨.count 3, 7726352334602101200⟩, ⟨.count 4, 1411392615892459200⟩, ⟨.count 5, 271742107500864000⟩, ⟨.count 6, 56490862644216000⟩, ⟨.count 7, 12497573340252000⟩, ⟨.count 8, 2914413863961600⟩, ⟨.count 9, 742096122768000⟩, ⟨.count 10, 218263565520000⟩, ⟨.count 11, 76392247932000⟩, ⟨.count 12, 32739534828000⟩, ⟨.count 13, 32427729734400⟩, ⟨.path 15, 8582628468960⟩, ⟨.path 16, 527620602600⟩, ⟨.privateRow 7 17, 431845330316400⟩, ⟨.privateRow 8 14, 125228720717100⟩, ⟨.privateRow 8 15, 302139135698400⟩, ⟨.privateRow 8 16, 547295890541400⟩, ⟨.privateRow 9 11, 14991840864000⟩, ⟨.privateRow 9 12, 79040316555200⟩, ⟨.privateRow 9 13, 145889351407800⟩, ⟨.privateRow 9 14, 243724498617600⟩, ⟨.privateRow 9 15, 231249145327200⟩, ⟨.privateRow 10 9, 18074387822400⟩, ⟨.privateRow 10 10, 36747647576640⟩, ⟨.privateRow 10 11, 66096380750400⟩, ⟨.privateRow 10 12, 104121641824200⟩, ⟨.privateRow 10 13, 130107761784000⟩, ⟨.privateRow 10 14, 86048757194400⟩, ⟨.privateRow 11 6, 2194083045000⟩, ⟨.privateRow 11 7, 9817726668750⟩, ⟨.privateRow 11 8, 19503923985000⟩, ⟨.privateRow 11 9, 27778999248000⟩, ⟨.privateRow 11 10, 44341676379000⟩, ⟨.privateRow 11 11, 51093516474000⟩, ⟨.privateRow 12 4, 2572392022200⟩, ⟨.privateRow 12 5, 5442597883800⟩, ⟨.privateRow 12 6, 9382301878950⟩, ⟨.privateRow 12 7, 13542262133400⟩, ⟨.privateRow 12 8, 1855240306920⟩, ⟨.privateRow 13 2, 2047520114640⟩, ⟨.privateRow 13 3, 3919835462400⟩, ⟨.privateRow 14 0, 1198500828525⟩, ⟨.privateRow 15 0, 569910421080⟩, ⟨.privateRow 16 0, 549202153500⟩, ⟨.privateRow 17 0, 793685692800⟩, ⟨.privateRow 18 0, 1561650090000⟩, ⟨.privateRow 19 0, 3833141130000⟩, ⟨.privateRow 19 8, 562194032400⟩, ⟨.privateRow 20 0, 3662292553920⟩, ⟨.privateRow 21 0, 8477529060000⟩, ⟨.privateRow 21 5, 34333992693000⟩, ⟨.privateRow 22 0, 16022529923400⟩, ⟨.privateRow 23 0, 151069567849200⟩, ⟨.privateRow 24 0, 1351233356873400⟩, ⟨.hall 21 2, 13733597077200⟩, ⟨.hall 22 2, 33571015077600⟩, ⟨.hall 17 3, 10221709680⟩, ⟨.hall 24 3, 16214800282480800⟩, ⟨.hall 25 3, 405370007062020000⟩, ⟨.hall 16 4, 5550249600⟩, ⟨.hall 19 4, 406921394880⟩, ⟨.hall 23 5, 5404933427493600⟩, ⟨.hall 15 6, 794957625⟩, ⟨.hall 20 6, 1816613370000⟩, ⟨.hall 22 6, 1007130452328000⟩, ⟨.hall 21 7, 280394273659500⟩, ⟨.hall 17 8, 10221709680⟩, ⟨.hall 18 10, 2453210323200⟩, ⟨.hall 8 12, 47567076480⟩, ⟨.hall 7 14, 153926922240⟩, ⟨.hall 9 14, 83342799540⟩, ⟨.hall 6 18, 5455508760000⟩, ⟨.hall 6 22, 1484820785448000⟩, ⟨.hall 5 23, 62567979350877000⟩, ⟨.hall 4 24, 54312531033144384⟩]
  caps := #[0, 0, 8799767646415200, 0, 0, 0, 2391555566400, 3781715137200, 5116360982040, 1335447440600, 1421977251240, 0, 664745172000, 976550265600, 435511283025, 33972152760, 2813010209100, 0, 6309066363600, 0, 51272095754880, 108512371968000, 239574971235600, 1007130452328000, 31078367208088200, 0, 0] }

theorem case_55_29_14_checked :
    (Witness.linear .positive case_55_29_14).check 55 29 14 = true := by
  change case_55_29_14.check 55 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_29_15 : Certificate := {
  objectiveScale := 1431612000000
  eta := 6810216118641936000
  rows := #[⟨.count 2, 2062522595931557760⟩, ⟨.count 3, 454554901252211760⟩, ⟨.count 4, 94186839901714560⟩, ⟨.count 5, 21705187202899200⟩, ⟨.count 6, 4889160559483200⟩, ⟨.count 7, 1226257623470880⟩, ⟨.count 8, 304934043173760⟩, ⟨.count 9, 84553982472960⟩, ⟨.count 10, 25397942169600⟩, ⟨.count 11, 8184883707000⟩, ⟨.count 12, 3055689917280⟩, ⟨.count 13, 1486270946160⟩, ⟨.count 14, 1455090436800⟩, ⟨.path 16, 135059707692⟩, ⟨.path 17, 183032764992⟩, ⟨.privateRow 4 25, 2067974528780160⟩, ⟨.privateRow 7 17, 5900360225760⟩, ⟨.privateRow 8 15, 13781785137120⟩, ⟨.privateRow 8 16, 44788124581200⟩, ⟨.privateRow 9 13, 8145566869440⟩, ⟨.privateRow 9 14, 20388903575040⟩, ⟨.privateRow 9 15, 36122007681760⟩, ⟨.privateRow 10 10, 576744936768⟩, ⟨.privateRow 10 11, 3315842449920⟩, ⟨.privateRow 10 12, 9077780111400⟩, ⟨.privateRow 10 13, 15265221491520⟩, ⟨.privateRow 10 14, 21160542443040⟩, ⟨.privateRow 11 8, 496053558000⟩, ⟨.privateRow 11 9, 1562568707700⟩, ⟨.privateRow 11 10, 3654261210600⟩, ⟨.privateRow 11 11, 6595445431575⟩, ⟨.privateRow 11 12, 9025812595800⟩, ⟨.privateRow 11 13, 9314783478000⟩, ⟨.privateRow 12 6, 302133361530⟩, ⟨.privateRow 12 7, 793685692800⟩, ⟨.privateRow 12 8, 1635764166036⟩, ⟨.privateRow 12 9, 2743114934560⟩, ⟨.privateRow 12 10, 4043938838940⟩, ⟨.privateRow 12 11, 651326195520⟩, ⟨.privateRow 13 4, 174291052320⟩, ⟨.privateRow 13 5, 412275623760⟩, ⟨.privateRow 13 6, 805024059840⟩, ⟨.privateRow 13 7, 1273204132200⟩, ⟨.privateRow 13 8, 90077027040⟩, ⟨.privateRow 14 2, 112843748160⟩, ⟨.privateRow 14 3, 223060566960⟩, ⟨.privateRow 14 4, 225192567600⟩, ⟨.privateRow 15 0, 96197645544⟩, ⟨.privateRow 16 0, 21259438200⟩, ⟨.privateRow 17 0, 14245640640⟩, ⟨.privateRow 18 0, 24986401440⟩, ⟨.privateRow 19 0, 61330258080⟩, ⟨.privateRow 20 0, 152595523080⟩, ⟨.privateRow 21 0, 565168604000⟩, ⟨.privateRow 22 0, 2136337323120⟩, ⟨.privateRow 23 0, 13428406031040⟩, ⟨.privateRow 24 0, 90082223791560⟩, ⟨.privateRow 25 0, 1297184022598464⟩, ⟨.privateRow 26 3, 108098668549872000⟩, ⟨.hall 9 12, 85241772⟩, ⟨.hall 9 13, 12357825480⟩, ⟨.hall 8 14, 28161365232⟩, ⟨.hall 7 16, 15886121160⟩, ⟨.hall 7 17, 368873919960⟩, ⟨.hall 11 17, 9579345375600⟩, ⟨.hall 10 18, 62199894556800⟩, ⟨.hall 9 19, 18664841875680⟩, ⟨.hall 6 22, 4727276613259200⟩, ⟨.hall 5 23, 6428595061488600⟩, ⟨.hall 4 24, 5752729143697536⟩]
  caps := #[0, 0, 0, 170200714385520, 68412180548880, 0, 6864656847048, 0, 264547581480, 150134741120, 19159338744, 0, 0, 0, 26605432620, 91455794976, 0, 0, 424768824480, 0, 2899314938520, 0, 44863083785520, 0, 2071891147205880, 0, 0] }

theorem case_55_29_15_checked :
    (Witness.linear .positive case_55_29_15).check 55 29 15 = true := by
  change case_55_29_15.check 55 29 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_29_16 : Certificate := {
  objectiveScale := 5636030400000
  eta := 27893317152600900000
  rows := #[⟨.count 2, 7534477197926078400⟩, ⟨.count 3, 1772046030871116000⟩, ⟨.count 4, 445722367185295200⟩, ⟨.count 5, 112066152149952000⟩, ⟨.count 6, 28201832601228000⟩, ⟨.count 7, 7925048491159800⟩, ⟨.count 8, 2299212965649600⟩, ⟨.count 9, 693586809115200⟩, ⟨.count 10, 223271344296000⟩, ⟨.count 11, 77301679455000⟩, ⟨.count 12, 30920671782000⟩, ⟨.count 13, 14766198361200⟩, ⟨.count 14, 9717925417200⟩, ⟨.count 15, 9938787358500⟩, ⟨.path 15, 1127186866260⟩, ⟨.privateRow 8 15, 42227655841800⟩, ⟨.privateRow 9 13, 26358422590500⟩, ⟨.privateRow 9 14, 131591648073600⟩, ⟨.privateRow 9 15, 186797147336800⟩, ⟨.privateRow 10 11, 13082165896800⟩, ⟨.privateRow 10 12, 54954466667100⟩, ⟨.privateRow 10 13, 121089710570400⟩, ⟨.privateRow 10 14, 156022229563200⟩, ⟨.privateRow 11 9, 5913076519350⟩, ⟨.privateRow 11 10, 23391287419500⟩, ⟨.privateRow 11 11, 51300205456500⟩, ⟨.privateRow 11 12, 84902772240000⟩, ⟨.privateRow 11 13, 99471533411250⟩, ⟨.privateRow 12 7, 2630264937300⟩, ⟨.privateRow 12 8, 10174373429220⟩, ⟨.privateRow 12 9, 22274335783700⟩, ⟨.privateRow 12 10, 37196831947275⟩, ⟨.privateRow 12 11, 51124280793300⟩, ⟨.privateRow 12 12, 22245705532050⟩, ⟨.privateRow 13 5, 1209482059500⟩, ⟨.privateRow 13 6, 4652442451800⟩, ⟨.privateRow 13 7, 10147028617440⟩, ⟨.privateRow 13 8, 17213208441000⟩, ⟨.privateRow 13 9, 14695207022925⟩, ⟨.privateRow 14 3, 606763575000⟩, ⟨.privateRow 14 4, 2313791766000⟩, ⟨.privateRow 14 5, 4910592772800⟩, ⟨.privateRow 14 6, 3312929119500⟩, ⟨.privateRow 15 2, 2106683132400⟩, ⟨.privateRow 15 3, 128836132425⟩, ⟨.privateRow 16 0, 552154853250⟩, ⟨.privateRow 17 0, 432456948000⟩, ⟨.privateRow 18 0, 758515758000⟩, ⟨.privateRow 19 0, 434422661400⟩, ⟨.privateRow 19 3, 341332091100⟩, ⟨.privateRow 20 0, 1297061946180⟩, ⟨.privateRow 20 2, 926472818700⟩, ⟨.privateRow 20 6, 463236409350⟩, ⟨.privateRow 21 0, 5490209296000⟩, ⟨.privateRow 21 3, 2058828486000⟩, ⟨.privateRow 21 8, 49411883664000⟩, ⟨.privateRow 22 0, 25941238923600⟩, ⟨.privateRow 22 6, 12970619461800⟩, ⟨.privateRow 23 0, 122294412068400⟩, ⟨.privateRow 23 4, 95117876053200⟩, ⟨.privateRow 24 0, 911546312176500⟩, ⟨.privateRow 24 5, 1093855574611800⟩, ⟨.privateRow 25 0, 10501013516273280⟩, ⟨.privateRow 26 0, 328156672383540000⟩, ⟨.hall 18 6, 40191484320⟩, ⟨.hall 19 8, 1585297934220⟩, ⟨.hall 9 12, 102261436200⟩, ⟨.hall 10 12, 64042902000⟩, ⟨.hall 8 13, 75267844080⟩, ⟨.hall 10 13, 30646902000⟩, ⟨.hall 8 14, 185700492120⟩, ⟨.hall 7 16, 524152352100⟩, ⟨.hall 7 17, 2842266904620⟩, ⟨.hall 11 17, 191536383538500⟩, ⟨.hall 6 22, 46085174887752000⟩, ⟨.hall 5 23, 65328686689266000⟩, ⟨.hall 4 24, 73233155130879744⟩, ⟨.hall 3 25, 49475929067056800⟩, ⟨.assumptionRow 16, 8361865191680⟩]
  caps := #[0, 121678229329675200, 1749978600879600, 1324088092490800, 0, 59164229124000, 0, 2533356525700, 2751343522200, 1047375633460, 0, 1734633195685, 272729203695, 0, 111275002800, 0, 89538519070, 14090076000, 1972140970800, 9246996649800, 0, 0, 246441769774200, 0, 0, 252024324390558720, 0] }

theorem case_55_29_16_checked :
    (Witness.linear .conditional case_55_29_16).check 55 29 16 = true := by
  change case_55_29_16.check 55 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_29_17 : Certificate := {
  objectiveScale := 89258400000000
  eta := 165390962881304160000
  rows := #[⟨.count 2, 44104256768347776000⟩, ⟨.count 3, 12128670611295638400⟩, ⟨.count 4, 3395708175099240000⟩, ⟨.count 5, 991474151659992000⟩, ⟨.count 6, 295211298950568000⟩, ⟨.count 7, 90067981542739200⟩, ⟨.count 8, 28977729206025600⟩, ⟨.count 9, 9786673716019200⟩, ⟨.count 10, 3463115239584000⟩, ⟨.count 11, 1298668214844000⟩, ⟨.count 12, 519467285937600⟩, ⟨.count 13, 229696418952000⟩, ⟨.count 14, 111314418415200⟩, ⟨.count 15, 92762015346000⟩, ⟨.count 16, 89951045184000⟩, ⟨.path 14, 3625215048000⟩, ⟨.path 15, 4613966175000⟩, ⟨.privateRow 3 26, 1332316089877172400⟩, ⟨.privateRow 8 16, 4929973169121000⟩, ⟨.privateRow 9 14, 1601378468289600⟩, ⟨.privateRow 9 15, 5134747139922400⟩, ⟨.privateRow 10 12, 521434965051000⟩, ⟨.privateRow 10 13, 1835001321753600⟩, ⟨.privateRow 10 14, 3734092763200800⟩, ⟨.privateRow 11 10, 173655490008000⟩, ⟨.privateRow 11 11, 685701033892875⟩, ⟨.privateRow 11 12, 1505876872500000⟩, ⟨.privateRow 11 13, 2433363170238000⟩, ⟨.privateRow 12 8, 57203242796700⟩, ⟨.privateRow 12 9, 262367626120600⟩, ⟨.privateRow 12 10, 620990158288500⟩, ⟨.privateRow 12 11, 1084284890488800⟩, ⟨.privateRow 12 12, 1515628261847700⟩, ⟨.privateRow 13 6, 18231149336400⟩, ⟨.privateRow 13 7, 103186698975360⟩, ⟨.privateRow 13 8, 261696860224800⟩, ⟨.privateRow 13 9, 483135496593750⟩, ⟨.privateRow 13 10, 717864412636800⟩, ⟨.privateRow 13 11, 297721896872400⟩, ⟨.privateRow 14 4, 4785342061500⟩, ⟨.privateRow 14 5, 42887373328800⟩, ⟨.privateRow 14 6, 115643312464680⟩, ⟨.privateRow 14 7, 225671823577200⟩, ⟨.privateRow 14 8, 212137894618650⟩, ⟨.privateRow 15 3, 19325419863750⟩, ⟨.privateRow 15 4, 54907617164400⟩, ⟨.privateRow 15 5, 73281992123340⟩, ⟨.privateRow 16 1, 8108567775000⟩, ⟨.privateRow 16 2, 23307627593250⟩, ⟨.privateRow 17 0, 8303173401600⟩, ⟨.privateRow 18 0, 7433454428400⟩, ⟨.privateRow 19 0, 15639215810400⟩, ⟨.privateRow 20 0, 44100106170120⟩, ⟨.privateRow 21 0, 144117994020000⟩, ⟨.privateRow 22 0, 590163185511900⟩, ⟨.privateRow 23 0, 3424243537915200⟩, ⟨.privateRow 24 0, 25523296740942000⟩, ⟨.privateRow 25 0, 330781925762608320⟩, ⟨.privateRow 26 0, 8039838473396730000⟩, ⟨.hall 10 11, 971652066000⟩, ⟨.hall 9 12, 957133443420⟩, ⟨.hall 10 12, 1333584252000⟩, ⟨.hall 11 12, 2381011652250⟩, ⟨.hall 9 13, 3450166459740⟩, ⟨.hall 8 14, 460463683680⟩, ⟨.hall 8 15, 18357960020400⟩, ⟨.hall 12 16, 1541668317789600⟩, ⟨.hall 7 18, 430568711789580⟩, ⟨.hall 5 21, 5542760960919000⟩, ⟨.hall 6 22, 965059203156048000⟩, ⟨.hall 4 24, 1770562192004686080⟩, ⟨.hall 3 25, 1742259502147071600⟩, ⟨.assumptionRow 17, 91510196633856⟩]
  caps := #[0, 0, 264525910481982240, 0, 5494025175105600, 0, 922355161728, 85383049896144, 18505812812760, 0, 8107866467064, 24941417220174, 5875967260380, 0, 4484474912190, 3821226174948, 2731472837478, 0, 56946859200, 99917212122000, 0, 0, 4403525307281100, 0, 219500351972101200, 0, 0] }

theorem case_55_29_17_checked :
    (Witness.linear .conditional case_55_29_17).check 55 29 17 = true := by
  change case_55_29_17.check 55 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_29_18 : Certificate := {
  objectiveScale := 259097300000000
  eta := 266463217975434480000
  rows := #[⟨.count 2, 77917520290747737600⟩, ⟨.count 3, 22970967066847800000⟩, ⟨.count 4, 6839355759729292800⟩, ⟨.count 5, 2051951998856760000⟩, ⟨.count 6, 670321613785824000⟩, ⟨.count 7, 221901357752474400⟩, ⟨.count 8, 74317553531020800⟩, ⟨.count 9, 25154809785705600⟩, ⟨.count 10, 8545349292480000⟩, ⟨.count 11, 3122987849982000⟩, ⟨.count 12, 1311036483556800⟩, ⟨.count 13, 551271405484800⟩, ⟨.count 14, 272101911681600⟩, ⟨.count 15, 185524030692000⟩, ⟨.count 16, 179902090368000⟩, ⟨.count 17, 152916776812800⟩, ⟨.count 19, 363177344930400⟩, ⟨.path 14, 22458133152000⟩, ⟨.privateRow 2 27, 2205212838417388800⟩, ⟨.privateRow 8 16, 9139963180748400⟩, ⟨.privateRow 9 14, 2356860163257600⟩, ⟨.privateRow 9 15, 12057771030905600⟩, ⟨.privateRow 10 12, 530711166585600⟩, ⟨.privateRow 10 13, 3800431659024000⟩, ⟨.privateRow 10 14, 10043034194793600⟩, ⟨.privateRow 11 10, 78082504500000⟩, ⟨.privateRow 11 11, 1186580779634250⟩, ⟨.privateRow 11 12, 3623742105984000⟩, ⟨.privateRow 11 13, 7170316388235000⟩, ⟨.privateRow 12 9, 339211221549200⟩, ⟨.privateRow 12 10, 1336288365512100⟩, ⟨.privateRow 12 11, 2982225172726800⟩, ⟨.privateRow 12 12, 4933564964328000⟩, ⟨.privateRow 13 7, 76153197360240⟩, ⟨.privateRow 13 8, 475687541128800⟩, ⟨.privateRow 13 9, 1243231867577700⟩, ⟨.privateRow 13 10, 2309837285527200⟩, ⟨.privateRow 13 11, 3394500796486800⟩, ⟨.privateRow 14 5, 11886388113600⟩, ⟨.privateRow 14 6, 158137149970800⟩, ⟨.privateRow 14 7, 506706373773600⟩, ⟨.privateRow 14 8, 1059916456298700⟩, ⟨.privateRow 14 9, 1718684523784800⟩, ⟨.privateRow 14 10, 1097831089555200⟩, ⟨.privateRow 15 4, 47036900710800⟩, ⟨.privateRow 15 5, 205519398444360⟩, ⟨.privateRow 15 6, 491066076300800⟩, ⟨.privateRow 15 7, 585689058004050⟩, ⟨.privateRow 16 2, 7964415459000⟩, ⟨.privateRow 16 3, 86117904054000⟩, ⟨.privateRow 16 4, 231061747316400⟩, ⟨.privateRow 16 5, 17490481008000⟩, ⟨.privateRow 17 1, 35605622052000⟩, ⟨.privateRow 17 2, 38433628396800⟩, ⟨.privateRow 18 0, 12035116693600⟩, ⟨.hall 11 10, 3052548951375⟩, ⟨.hall 12 10, 1484526582000⟩, ⟨.hall 10 11, 3650891706000⟩, ⟨.hall 11 11, 3936011858625⟩, ⟨.hall 12 11, 3604080456900⟩, ⟨.hall 10 12, 8404060896000⟩, ⟨.hall 9 13, 13329775499040⟩, ⟨.hall 9 14, 18343306341360⟩, ⟨.hall 8 16, 194325819367680⟩, ⟨.hall 8 17, 131710273094400⟩, ⟨.hall 7 18, 1428083820858240⟩, ⟨.hall 6 22, 3015048690894240000⟩, ⟨.hall 5 23, 4298657848932447000⟩, ⟨.hall 4 24, 5525176746457944576⟩, ⟨.hall 3 25, 6089073270181347600⟩, ⟨.hall 2 26, 5036597223545888000⟩, ⟨.assumptionRow 18, 171792072144000⟩]
  caps := #[0, 3053908867878960000, 612040644599529600, 29369287084200000, 0, 837316039560000, 427642508832000, 283436322769600, 43104440579200, 81969693478400, 0, 13887697698000, 24056780733440, 0, 6635137902400, 24893853124140, 11315890313000, 18875295331200, 24192705829600, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_29_18_checked :
    (Witness.linear .conditional case_55_29_18).check 55 29 18 = true := by
  change case_55_29_18.check 55 29 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_30_1_checked :
    (Witness.rising).check 55 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_30_2_checked :
    (Witness.rising).check 55 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_30_3_checked :
    (Witness.rising).check 55 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_30_4_checked :
    (Witness.rising).check 55 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_30_5_checked :
    (Witness.rising).check 55 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_30_6_checked :
    (Witness.rising).check 55 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_30_7_checked :
    (Witness.rising).check 55 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_30_8_checked :
    (Witness.rising).check 55 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_30_9_checked :
    (Witness.rising).check 55 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_30_10_checked :
    (Witness.rising).check 55 30 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_30_11_checked :
    (Witness.linear .positive case_55_30_11).check 55 30 11 = true := by
  change case_55_30_11.check 55 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_30_12 : Certificate := {
  objectiveScale := 33802596000000
  eta := 85121215562911207680
  rows := #[⟨.count 2, 18523787842706065920⟩, ⟨.count 3, 2698988756584760640⟩, ⟨.count 4, 388309217199583680⟩, ⟨.count 5, 61636383682473600⟩, ⟨.count 6, 10521766507412160⟩, ⟨.count 7, 2007032695668000⟩, ⟨.count 8, 433264200969600⟩, ⟨.count 9, 113338316931840⟩, ⟨.count 10, 42164552430000⟩, ⟨.count 11, 33394325524560⟩, ⟨.path 12, 8635782853152⟩, ⟨.path 13, 5370111681480⟩, ⟨.privateRow 4 26, 13728103638369120⟩, ⟨.privateRow 6 18, 334271392986960⟩, ⟨.privateRow 6 19, 624319150094640⟩, ⟨.privateRow 6 20, 784463065049664⟩, ⟨.privateRow 6 21, 819743149985760⟩, ⟨.privateRow 7 14, 22118319503280⟩, ⟨.privateRow 7 15, 112503057226560⟩, ⟨.privateRow 7 16, 184933726957980⟩, ⟨.privateRow 7 17, 265419834039360⟩, ⟨.privateRow 7 18, 324128953708560⟩, ⟨.privateRow 7 19, 381745810686240⟩, ⟨.privateRow 7 20, 236338339877640⟩, ⟨.privateRow 8 11, 13698794589480⟩, ⟨.privateRow 8 12, 33884967589200⟩, ⟨.privateRow 8 13, 57152645333784⟩, ⟨.privateRow 8 14, 79360975373680⟩, ⟨.privateRow 8 15, 95254408889640⟩, ⟨.privateRow 8 16, 105494371622640⟩, ⟨.privateRow 8 17, 122864382480840⟩, ⟨.privateRow 8 18, 52119134763696⟩, ⟨.privateRow 9 8, 5118642809280⟩, ⟨.privateRow 9 9, 11878150838400⟩, ⟨.privateRow 9 10, 18439964262720⟩, ⟨.privateRow 9 11, 24886455834240⟩, ⟨.privateRow 9 12, 30223551181824⟩, ⟨.privateRow 9 13, 28118030420480⟩, ⟨.privateRow 10 5, 1813075754490⟩, ⟨.privateRow 10 6, 202389851664⟩, ⟨.privateRow 10 7, 14384135886120⟩, ⟨.privateRow 10 8, 5552747212320⟩, ⟨.privateRow 11 3, 3293795625120⟩, ⟨.privateRow 11 4, 182713060530⟩, ⟨.privateRow 12 0, 650961511200⟩, ⟨.privateRow 13 0, 299013089760⟩, ⟨.privateRow 14 0, 285821335800⟩, ⟨.privateRow 15 0, 372453546465⟩, ⟨.privateRow 15 15, 112438806480⟩, ⟨.privateRow 16 0, 562194032400⟩, ⟨.privateRow 17 0, 1006595029440⟩, ⟨.privateRow 18 0, 2156518647360⟩, ⟨.privateRow 19 0, 5597846294040⟩, ⟨.privateRow 20 0, 17451378912240⟩, ⟨.privateRow 21 0, 70560169872192⟩, ⟨.privateRow 22 0, 230012318455920⟩, ⟨.privateRow 22 1, 163429805218680⟩, ⟨.privateRow 23 0, 2696591786108220⟩, ⟨.privateRow 24 0, 31503040548819840⟩, ⟨.privateRow 25 0, 771824493446086080⟩, ⟨.hall 13 11, 28553580⟩, ⟨.hall 6 17, 19697425020⟩, ⟨.hall 5 19, 220791045384⟩, ⟨.hall 4 25, 27120966650648640⟩]
  caps := #[0, 0, 0, 0, 154906255286640, 44613229577400, 23915351693376, 9169755345828, 0, 4872969947272, 273826423152, 408270475440, 205612193232, 0, 732741969960, 42164552430, 337316419440, 813842789760, 2254542222240, 0, 20281332249360, 103764955694400, 0, 4194698333946120, 63006081097639680, 0] }

theorem case_55_30_12_checked :
    (Witness.linear .positive case_55_30_12).check 55 30 12 = true := by
  change case_55_30_12.check 55 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_30_13 : Certificate := {
  objectiveScale := 809483220000000
  eta := 3104939676491683430400
  rows := #[⟨.count 2, 728730959228679607200⟩, ⟨.count 3, 117199871450454592800⟩, ⟨.count 4, 19463400269509996800⟩, ⟨.count 5, 3384294029972856000⟩, ⟨.count 6, 624924445669524000⟩, ⟨.count 7, 125525559166207200⟩, ⟨.count 8, 28034742415680000⟩, ⟨.count 9, 7124122778572800⟩, ⟨.count 10, 2226288368304000⟩, ⟨.count 11, 884331212965200⟩, ⟨.count 12, 816305735044800⟩, ⟨.path 13, 99960834273300⟩, ⟨.path 14, 175607067636000⟩, ⟨.privateRow 4 26, 886879076320036800⟩, ⟨.privateRow 6 19, 25776944410417200⟩, ⟨.privateRow 6 20, 49480319122874640⟩, ⟨.privateRow 7 16, 7220197723038300⟩, ⟨.privateRow 7 17, 12911715295221600⟩, ⟨.privateRow 7 18, 20680628735566800⟩, ⟨.privateRow 7 19, 30601923828315840⟩, ⟨.privateRow 7 20, 4009969406242800⟩, ⟨.privateRow 8 13, 1836275628227040⟩, ⟨.privateRow 8 14, 3566642229550400⟩, ⟨.privateRow 8 15, 5878535050287900⟩, ⟨.privateRow 8 16, 7634461104270000⟩, ⟨.privateRow 8 17, 10834259829393000⟩, ⟨.privateRow 8 18, 11396122791973920⟩, ⟨.privateRow 9 10, 448006177819200⟩, ⟨.privateRow 9 11, 1020944362838400⟩, ⟨.privateRow 9 12, 1710119287356480⟩, ⟨.privateRow 9 13, 2321569845795200⟩, ⟨.privateRow 9 14, 2910665903745600⟩, ⟨.privateRow 9 15, 3663363399696000⟩, ⟨.privateRow 9 16, 2602833438004800⟩, ⟨.privateRow 10 7, 105351146000100⟩, ⟨.privateRow 10 8, 304687542713400⟩, ⟨.privateRow 10 9, 525651420294000⟩, ⟨.privateRow 10 10, 751372324302600⟩, ⟨.privateRow 10 11, 959159238677640⟩, ⟨.privateRow 10 12, 588523452917400⟩, ⟨.privateRow 11 4, 21257961850125⟩, ⟨.privateRow 11 5, 81218297880720⟩, ⟨.privateRow 11 6, 150627843966600⟩, ⟨.privateRow 11 7, 365339629670400⟩, ⟨.privateRow 12 2, 40014987012000⟩, ⟨.privateRow 12 3, 60737033857500⟩, ⟨.privateRow 13 0, 19685028409200⟩, ⟨.privateRow 14 0, 10289568088800⟩, ⟨.privateRow 15 0, 11981760315525⟩, ⟨.privateRow 15 13, 2061378118800⟩, ⟨.privateRow 16 0, 17933989633560⟩, ⟨.privateRow 17 0, 32982049900800⟩, ⟨.privateRow 18 0, 70086856039200⟩, ⟨.privateRow 19 0, 180223344100800⟩, ⟨.privateRow 20 0, 570707256319200⟩, ⟨.privateRow 21 0, 2282829025276800⟩, ⟨.privateRow 22 0, 11984852382703200⟩, ⟨.privateRow 23 0, 87888917473156800⟩, ⟨.privateRow 24 0, 1010722550941303200⟩, ⟨.privateRow 25 0, 24257341222591276800⟩, ⟨.hall 6 18, 8849193467400⟩, ⟨.hall 7 18, 6032439372960⟩, ⟨.hall 7 19, 7159069597680⟩, ⟨.hall 5 22, 2359750438085040⟩, ⟨.hall 4 24, 61362444199440384⟩, ⟨.hall 5 24, 249969778267809600⟩]
  caps := #[0, 0, 70142751754966800, 46659641743915200, 10743996454191000, 0, 835469995566960, 206708028941700, 313030768870820, 62254841348700, 0, 61194924003150, 0, 4793347358100, 37269541108800, 0, 120590619949800, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_30_13_checked :
    (Witness.linear .positive case_55_30_13).check 55 30 13 = true := by
  change case_55_30_13.check 55 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_30_14 : Certificate := {
  objectiveScale := 103386628800000
  eta := 550421124468980244480
  rows := #[⟨.count 2, 138083077232235495360⟩, ⟨.count 3, 24648047410267401120⟩, ⟨.count 4, 4560781097635963200⟩, ⟨.count 5, 894350153130033600⟩, ⟨.count 6, 185344963861337280⟩, ⟨.count 7, 40404435353362080⟩, ⟨.count 8, 9276951126643200⟩, ⟨.count 9, 2350420810657920⟩, ⟨.count 10, 679692585171600⟩, ⟨.count 11, 241181239899600⟩, ⟨.count 12, 110254281096960⟩, ⟨.count 13, 110254281096960⟩, ⟨.path 15, 27994058295840⟩, ⟨.path 16, 374928568560⟩, ⟨.privateRow 4 26, 283278329045712000⟩, ⟨.privateRow 6 20, 1241028870105024⟩, ⟨.privateRow 7 18, 8906583052326960⟩, ⟨.privateRow 7 19, 4758223963068576⟩, ⟨.privateRow 7 20, 8274709085282640⟩, ⟨.privateRow 8 15, 1706296367936160⟩, ⟨.privateRow 8 16, 1140686337510720⟩, ⟨.privateRow 8 17, 4904911808476680⟩, ⟨.privateRow 8 18, 3493766058230448⟩, ⟨.privateRow 8 19, 3946845724862040⟩, ⟨.privateRow 9 11, 34726555019520⟩, ⟨.privateRow 9 12, 232313566028544⟩, ⟨.privateRow 9 13, 448256041833600⟩, ⟨.privateRow 9 14, 1052914463480880⟩, ⟨.privateRow 9 15, 975026495963520⟩, ⟨.privateRow 9 16, 2188658847735360⟩, ⟨.privateRow 9 17, 1542780359632512⟩, ⟨.privateRow 10 9, 55544770401120⟩, ⟨.privateRow 10 10, 126570320112600⟩, ⟨.privateRow 10 11, 226052598487716⟩, ⟨.privateRow 10 12, 316702638252000⟩, ⟨.privateRow 10 14, 1738071039224520⟩, ⟨.privateRow 11 7, 48011370366960⟩, ⟨.privateRow 11 8, 63096910236360⟩, ⟨.privateRow 11 9, 105774251768640⟩, ⟨.privateRow 11 10, 146755130217696⟩, ⟨.privateRow 11 11, 144221509111680⟩, ⟨.privateRow 11 12, 105608148986340⟩, ⟨.privateRow 11 13, 437258455714080⟩, ⟨.privateRow 12 5, 33798187360080⟩, ⟨.privateRow 12 6, 35602944937560⟩, ⟨.privateRow 12 7, 27085036068090⟩, ⟨.privateRow 12 8, 31217831484840⟩, ⟨.privateRow 12 9, 200180429116668⟩, ⟨.privateRow 12 10, 81414619606320⟩, ⟨.privateRow 13 4, 57550311561600⟩, ⟨.privateRow 13 5, 2609568783360⟩, ⟨.privateRow 13 6, 49296385298160⟩, ⟨.privateRow 13 8, 146298949917120⟩, ⟨.privateRow 14 0, 7431354730800⟩, ⟨.privateRow 14 2, 6048672365736⟩, ⟨.privateRow 14 3, 45775214919720⟩, ⟨.privateRow 14 6, 91252122801840⟩, ⟨.privateRow 14 8, 42238619262840⟩, ⟨.privateRow 15 0, 22930489096515⟩, ⟨.privateRow 15 2, 24222531453120⟩, ⟨.privateRow 15 3, 22262883683040⟩, ⟨.privateRow 15 5, 105774251768640⟩, ⟨.privateRow 15 9, 38630761369200⟩, ⟨.privateRow 16 0, 65922872239224⟩, ⟨.privateRow 16 3, 59929883853840⟩, ⟨.privateRow 16 4, 87502945715640⟩, ⟨.privateRow 16 7, 76465415831805⟩, ⟨.privateRow 17 0, 164824581841920⟩, ⟨.privateRow 17 2, 25011387841440⟩, ⟨.privateRow 17 4, 125901479575872⟩, ⟨.privateRow 17 6, 202202453653200⟩, ⟨.privateRow 18 0, 413512450631280⟩, ⟨.privateRow 18 2, 123491881880640⟩, ⟨.privateRow 18 4, 94794242663120⟩, ⟨.privateRow 18 9, 896633892374220⟩, ⟨.privateRow 18 12, 298187714784960⟩, ⟨.privateRow 19 0, 1425266279597160⟩, ⟨.privateRow 19 5, 143008393825440⟩, ⟨.privateRow 19 8, 479230255904400⟩, ⟨.privateRow 19 9, 1668431261296800⟩, ⟨.privateRow 20 0, 4641595131766320⟩, ⟨.privateRow 21 0, 19694588590797120⟩, ⟨.privateRow 21 9, 8093666544163200⟩, ⟨.privateRow 22 0, 102294952155396000⟩, ⟨.privateRow 23 0, 768628532810698560⟩, ⟨.privateRow 24 0, 8736843245539368960⟩, ⟨.privateRow 24 5, 537520629364238520⟩, ⟨.privateRow 25 0, 213574863400724105280⟩, ⟨.hall 19 3, 30657827818800⟩, ⟨.hall 21 6, 1191567574557360⟩, ⟨.hall 15 7, 44294075280⟩, ⟨.hall 20 8, 1244026524380640⟩, ⟨.hall 19 9, 654851202209568⟩, ⟨.hall 9 10, 17260719840⟩, ⟨.hall 14 11, 283439491335⟩, ⟨.hall 15 12, 3019785088320⟩, ⟨.hall 16 12, 31033110588480⟩, ⟨.hall 8 13, 29781012352⟩, ⟨.hall 13 15, 19709979479190⟩, ⟨.hall 7 17, 1067590021680⟩, ⟨.hall 8 17, 1174603387776⟩, ⟨.hall 6 18, 226501114320⟩, ⟨.hall 6 20, 71598405340800⟩, ⟨.hall 7 20, 62999380735200⟩, ⟨.hall 5 22, 1321379037970992⟩, ⟨.hall 4 25, 425571212789442720⟩]
  caps := #[0, 0, 56176758267215040, 4350829838453280, 2629473484921920, 571700222402400, 153353681889408, 60825307626720, 34515191144616, 100354857902208, 5579837172000, 0, 0, 5651181341280, 10954751292186, 8234287404525, 14580421824969, 0, 12819376016720, 115623807773760, 0, 0, 0, 0, 1168894067030169480, 0] }

theorem case_55_30_14_checked :
    (Witness.linear .positive case_55_30_14).check 55 30 14 = true := by
  change case_55_30_14.check 55 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_30_15 : Certificate := {
  objectiveScale := 60815664000000
  eta := 432883280181333421440
  rows := #[⟨.count 2, 101770572492962493120⟩, ⟨.count 3, 23339301530076211680⟩, ⟨.count 4, 5166996721793786880⟩, ⟨.count 5, 1191117926416017600⟩, ⟨.count 6, 280850229082463040⟩, ⟨.count 7, 65899484967476160⟩, ⟨.count 8, 16963567774433280⟩, ⟨.count 9, 4350032545098240⟩, ⟨.count 10, 1227831766761600⟩, ⟨.count 11, 385889983839360⟩, ⟨.count 12, 137817851371200⟩, ⟨.count 13, 55127140548480⟩, ⟨.count 14, 64314997306560⟩, ⟨.path 16, 13176686656224⟩, ⟨.privateRow 8 15, 121138759131390⟩, ⟨.privateRow 8 16, 2052998750602800⟩, ⟨.privateRow 8 17, 3912333257873040⟩, ⟨.privateRow 8 18, 6487239394988352⟩, ⟨.privateRow 8 19, 8912499475239360⟩, ⟨.privateRow 9 13, 211784738605440⟩, ⟨.privateRow 9 14, 758624627320560⟩, ⟨.privateRow 9 15, 2098729219466880⟩, ⟨.privateRow 9 16, 3361270667314560⟩, ⟨.privateRow 10 11, 134403727325868⟩, ⟨.privateRow 10 12, 339359057757720⟩, ⟨.privateRow 10 13, 772328106860310⟩, ⟨.privateRow 10 14, 1489059239587920⟩, ⟨.privateRow 10 15, 2164053488917320⟩, ⟨.privateRow 10 16, 1405867372942032⟩, ⟨.privateRow 10 17, 1197135972592560⟩, ⟨.privateRow 11 8, 7552139835240⟩, ⟨.privateRow 11 9, 60992941660560⟩, ⟨.privateRow 11 10, 155525357123136⟩, ⟨.privateRow 11 11, 322387044579600⟩, ⟨.privateRow 11 12, 565314209279820⟩, ⟨.privateRow 11 13, 927764717639760⟩, ⟨.privateRow 11 14, 1258527560930640⟩, ⟨.privateRow 11 15, 1080199613853360⟩, ⟨.privateRow 12 7, 46322111155320⟩, ⟨.privateRow 12 8, 58363771906440⟩, ⟨.privateRow 12 9, 144593895730284⟩, ⟨.privateRow 12 11, 862079372379225⟩, ⟨.privateRow 12 13, 1341044259314760⟩, ⟨.privateRow 13 4, 5300686591200⟩, ⟨.privateRow 13 5, 3343510003680⟩, ⟨.privateRow 13 6, 60516171916200⟩, ⟨.privateRow 13 7, 49344573358080⟩, ⟨.privateRow 13 8, 118099297251936⟩, ⟨.privateRow 13 10, 567836051082300⟩, ⟨.privateRow 13 11, 191430510036480⟩, ⟨.privateRow 13 12, 644033420830800⟩, ⟨.privateRow 13 16, 4134535541136000⟩, ⟨.privateRow 14 3, 17309265856740⟩, ⟨.privateRow 14 5, 61156671545970⟩, ⟨.privateRow 14 7, 176751394383564⟩, ⟨.privateRow 14 9, 360192696969105⟩, ⟨.privateRow 14 11, 880694352998460⟩, ⟨.privateRow 15 1, 11401294977072⟩, ⟨.privateRow 15 2, 11484820947600⟩, ⟨.privateRow 15 5, 134343930324240⟩, ⟨.privateRow 15 6, 94572280130328⟩, ⟨.privateRow 15 8, 355011476609790⟩, ⟨.privateRow 15 9, 116936358739200⟩, ⟨.privateRow 15 10, 485529506181720⟩, ⟨.privateRow 16 0, 21925567263600⟩, ⟨.privateRow 16 1, 8926838100180⟩, ⟨.privateRow 16 5, 232411012994160⟩, ⟨.privateRow 16 7, 648448651820970⟩, ⟨.privateRow 16 9, 350443650096540⟩, ⟨.privateRow 17 1, 57268832100480⟩, ⟨.privateRow 17 3, 67681347027840⟩, ⟨.privateRow 17 4, 184759446807936⟩, ⟨.privateRow 17 6, 839018373953760⟩, ⟨.privateRow 17 7, 384219464428800⟩, ⟨.privateRow 17 9, 820113662624256⟩, ⟨.privateRow 18 1, 207765051273780⟩, ⟨.privateRow 18 3, 273338738552880⟩, ⟨.privateRow 18 4, 138970200409040⟩, ⟨.privateRow 18 5, 839688321842370⟩, ⟨.privateRow 18 7, 184986823061040⟩, ⟨.privateRow 18 10, 1830541249096560⟩, ⟨.privateRow 19 0, 356760301617720⟩, ⟨.privateRow 19 1, 149093857392480⟩, ⟨.privateRow 19 2, 389773941468912⟩, ⟨.privateRow 19 3, 452014710507360⟩, ⟨.privateRow 19 4, 1118203930443600⟩, ⟨.privateRow 19 5, 1071041587799040⟩, ⟨.privateRow 19 6, 113595319918080⟩, ⟨.privateRow 20 0, 2054074463859600⟩, ⟨.privateRow 20 3, 4223882227735170⟩, ⟨.privateRow 20 4, 1917428145581520⟩, ⟨.privateRow 21 0, 10278956511087264⟩, ⟨.privateRow 21 2, 5159712421904040⟩, ⟨.privateRow 21 3, 12410288701050240⟩, ⟨.privateRow 21 7, 13129725727198080⟩, ⟨.privateRow 22 0, 69403190616199440⟩, ⟨.privateRow 22 3, 79790062681208880⟩, ⟨.privateRow 22 7, 77193344664956520⟩, ⟨.privateRow 23 0, 589454989689285720⟩, ⟨.privateRow 23 4, 392104420454106360⟩, ⟨.privateRow 23 7, 1204877159541095040⟩, ⟨.privateRow 24 0, 7269326606640178080⟩, ⟨.privateRow 24 4, 3424205490764778720⟩, ⟨.privateRow 25 1, 243676018645121462400⟩, ⟨.hall 19 2, 111594493260432⟩, ⟨.hall 24 5, 2866776689942605440⟩, ⟨.hall 15 6, 361653823440⟩, ⟨.hall 18 6, 10461311422380⟩, ⟨.hall 19 6, 64644219800784⟩, ⟨.hall 23 6, 443667821062546080⟩, ⟨.hall 22 7, 54531078341299560⟩, ⟨.hall 20 8, 4061821543459680⟩, ⟨.hall 11 9, 111638158632⟩, ⟨.hall 13 9, 139816238562⟩, ⟨.hall 20 9, 52339043652255360⟩, ⟨.hall 10 10, 24422923980⟩, ⟨.hall 19 10, 31491720735471360⟩, ⟨.hall 18 11, 17717320053473040⟩, ⟨.hall 16 12, 213376729325760⟩, ⟨.hall 17 12, 10576743729552000⟩, ⟨.hall 15 13, 174047241087720⟩, ⟨.hall 15 14, 3218673274296480⟩, ⟨.hall 14 15, 5262775638975855⟩, ⟨.hall 13 16, 2267509001677920⟩, ⟨.hall 11 17, 84530968682160⟩, ⟨.hall 7 18, 38896708267872⟩, ⟨.hall 8 18, 8906905766304⟩, ⟨.hall 10 19, 43445511532823400⟩, ⟨.hall 6 20, 230857251901380⟩, ⟨.hall 9 20, 82259716814795520⟩, ⟨.hall 8 21, 164991178186773120⟩, ⟨.hall 5 22, 3250369564329888⟩, ⟨.hall 6 23, 199879840030230360⟩, ⟨.hall 4 25, 1084738093838118720⟩, ⟨.hall 3 26, 864418575188007840⟩]
  caps := #[0, 0, 0, 3465302685455520, 146583859793280, 578471819365440, 299607656283936, 55908524091420, 177063961074, 0, 6750066296610, 334029118878, 0, 26384815407312, 0, 20991787087635, 0, 100991659833792, 68900031716516, 0, 0, 2428099963248960, 0, 27698325506691840, 3094298649461859840, 0] }

theorem case_55_30_15_checked :
    (Witness.linear .positive case_55_30_15).check 55 30 15 = true := by
  change case_55_30_15.check 55 30 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_30_16 : Certificate := {
  objectiveScale := 731377920000
  eta := 6295666456344545280
  rows := #[⟨.count 2, 1508336755165880640⟩, ⟨.count 3, 354986627633557920⟩, ⟨.count 4, 81428633408041920⟩, ⟨.count 5, 20842513845753600⟩, ⟨.count 6, 5356102860108000⟩, ⟨.count 7, 1385695851059520⟩, ⟨.count 8, 379393519464960⟩, ⟨.count 9, 113497054070400⟩, ⟨.count 10, 35682785938800⟩, ⟨.count 11, 12295514190960⟩, ⟨.count 12, 4593928379040⟩, ⟨.count 13, 2161848648960⟩, ⟨.count 14, 1891617567840⟩, ⟨.count 15, 429913083600⟩, ⟨.path 15, 172776108960⟩, ⟨.privateRow 3 27, 5295268111573440⟩, ⟨.privateRow 6 20, 145209899762928⟩, ⟨.privateRow 7 18, 88398318808800⟩, ⟨.privateRow 7 19, 296016039551232⟩, ⟨.privateRow 7 20, 261958325068440⟩, ⟨.privateRow 8 16, 41182943802000⟩, ⟨.privateRow 8 17, 117423593567280⟩, ⟨.privateRow 8 18, 225134972894832⟩, ⟨.privateRow 8 19, 269359654123560⟩, ⟨.privateRow 9 13, 1019053235200⟩, ⟨.privateRow 9 14, 16422679793520⟩, ⟨.privateRow 9 15, 46992912046080⟩, ⟨.privateRow 9 16, 87090837113280⟩, ⟨.privateRow 9 17, 131213294564352⟩, ⟨.privateRow 9 18, 145081335278880⟩, ⟨.privateRow 10 11, 1109175755688⟩, ⟨.privateRow 10 12, 6525125246640⟩, ⟨.privateRow 10 13, 18534627816705⟩, ⟨.privateRow 10 14, 35025633082440⟩, ⟨.privateRow 10 15, 52177117912920⟩, ⟨.privateRow 10 16, 65329592183856⟩, ⟨.privateRow 10 17, 61499066608980⟩, ⟨.privateRow 11 9, 669622196880⟩, ⟨.privateRow 11 10, 2897614183464⟩, ⟨.privateRow 11 11, 7499594902800⟩, ⟨.privateRow 11 12, 14409253518660⟩, ⟨.privateRow 11 13, 21999266649360⟩, ⟨.privateRow 11 14, 27796269260760⟩, ⟨.privateRow 11 15, 22217908160448⟩, ⟨.privateRow 12 7, 347171875050⟩, ⟨.privateRow 12 8, 1340919379800⟩, ⟨.privateRow 12 9, 3330598074804⟩, ⟨.privateRow 12 10, 6192795609000⟩, ⟨.privateRow 12 11, 9776172340935⟩, ⟨.privateRow 12 12, 6594925194000⟩, ⟨.privateRow 13 5, 175890052800⟩, ⟨.privateRow 13 6, 649593945000⟩, ⟨.privateRow 13 7, 1583591929920⟩, ⟨.privateRow 13 8, 2941361382960⟩, ⟨.privateRow 13 9, 1741489189440⟩, ⟨.privateRow 14 3, 93294063720⟩, ⟨.privateRow 14 4, 341253352440⟩, ⟨.privateRow 14 5, 806940033900⟩, ⟨.privateRow 14 6, 337788851400⟩, ⟨.privateRow 15 0, 59113048995⟩, ⟨.privateRow 15 2, 208814926320⟩, ⟨.privateRow 15 3, 28660872240⟩, ⟨.privateRow 16 0, 65920006152⟩, ⟨.privateRow 17 0, 54592137600⟩, ⟨.privateRow 18 0, 24986401440⟩, ⟨.privateRow 18 1, 81205804680⟩, ⟨.privateRow 19 0, 278419901760⟩, ⟨.privateRow 20 0, 601133878800⟩, ⟨.privateRow 20 2, 293887674080⟩, ⟨.privateRow 21 0, 3173986880064⟩, ⟨.privateRow 22 0, 18514923467040⟩, ⟨.privateRow 23 0, 127290098835900⟩, ⟨.privateRow 24 0, 1672955584700400⟩, ⟨.privateRow 25 0, 37474205097288960⟩, ⟨.hall 8 18, 851201131872⟩, ⟨.hall 7 19, 381726891000⟩, ⟨.hall 7 20, 11707942034880⟩, ⟨.hall 9 20, 223784090449920⟩, ⟨.hall 6 21, 31592198956500⟩, ⟨.hall 5 24, 15619189436794944⟩, ⟨.hall 4 25, 20508838301952000⟩, ⟨.hall 3 26, 17922445916094720⟩, ⟨.assumptionRow 16, 1169168553280⟩]
  caps := #[0, 14038741395544320, 1231906821687360, 268687860648480, 52070146273600, 7799792320320, 504966294560, 4919955040, 383682579280, 0, 85942867920, 86724357720, 288004897479, 0, 296891916100, 0, 385352360120, 0, 1805267504040, 0, 0, 63479737601280, 0, 2800382174389800, 0, 0] }

theorem case_55_30_16_checked :
    (Witness.linear .conditional case_55_30_16).check 55 30 16 = true := by
  change case_55_30_16.check 55 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_30_17 : Certificate := {
  objectiveScale := 7459452000000
  eta := 34180798995469526400
  rows := #[⟨.count 2, 8407373946466294800⟩, ⟨.count 3, 2247159821756850000⟩, ⟨.count 4, 609048407448280800⟩, ⟨.count 5, 168099228224928000⟩, ⟨.count 6, 47316819796646400⟩, ⟨.count 7, 13705166121847200⟩, ⟨.count 8, 4090523779742400⟩, ⟨.count 9, 1275056065483200⟩, ⟨.count 10, 417429069057000⟩, ⟨.count 11, 145327157375400⟩, ⟨.count 12, 53006865912000⟩, ⟨.count 13, 21202746364800⟩, ⟨.count 14, 9276201534600⟩, ⟨.count 15, 8432910486000⟩, ⟨.count 16, 6746328388800⟩, ⟨.path 14, 1060264296000⟩, ⟨.privateRow 3 27, 265664227816587600⟩, ⟨.privateRow 6 20, 1955969414839440⟩, ⟨.privateRow 7 18, 767997204975000⟩, ⟨.privateRow 7 19, 3529100756301120⟩, ⟨.privateRow 7 20, 5882858590108500⟩, ⟨.privateRow 8 16, 285808737614400⟩, ⟨.privateRow 8 17, 1256253798399600⟩, ⟨.privateRow 8 18, 2876109710554080⟩, ⟨.privateRow 8 19, 4502284058972700⟩, ⟨.privateRow 9 14, 103162604945400⟩, ⟨.privateRow 9 15, 454681116489600⟩, ⟨.privateRow 9 16, 1061172469156800⟩, ⟨.privateRow 9 17, 1852691693973120⟩, ⟨.privateRow 9 18, 2459973687771600⟩, ⟨.privateRow 10 12, 36636311111400⟩, ⟨.privateRow 10 13, 167604095909250⟩, ⟨.privateRow 10 14, 404237587653900⟩, ⟨.privateRow 10 15, 724316736493350⟩, ⟨.privateRow 10 16, 1051077962975040⟩, ⟨.privateRow 10 17, 1181661581850750⟩, ⟨.privateRow 11 10, 12846133640340⟩, ⟨.privateRow 11 11, 63121896637800⟩, ⟨.privateRow 11 12, 159136048296225⟩, ⟨.privateRow 11 13, 295192023726600⟩, ⟨.privateRow 11 14, 444039586590600⟩, ⟨.privateRow 11 15, 552018320413560⟩, ⟨.privateRow 11 16, 529797601282950⟩, ⟨.privateRow 12 8, 4437317184300⟩, ⟨.privateRow 12 9, 24405244513650⟩, ⟨.privateRow 12 10, 65007031389300⟩, ⟨.privateRow 12 11, 126112168482300⟩, ⟨.privateRow 12 12, 197797644287100⟩, ⟨.privateRow 12 13, 258776574556500⟩, ⟨.privateRow 12 14, 39225080774880⟩, ⟨.privateRow 13 6, 1461086688600⟩, ⟨.privateRow 13 7, 9748815199200⟩, ⟨.privateRow 13 8, 27706281067080⟩, ⟨.privateRow 13 9, 56789834547600⟩, ⟨.privateRow 13 10, 94316543625150⟩, ⟨.privateRow 13 11, 23154098022000⟩, ⟨.privateRow 14 4, 373766362200⟩, ⟨.privateRow 14 5, 4085945914050⟩, ⟨.privateRow 14 6, 12428503787700⟩, ⟨.privateRow 14 7, 27055587809250⟩, ⟨.privateRow 14 8, 13987922949000⟩, ⟨.privateRow 15 3, 1816319181600⟩, ⟨.privateRow 15 4, 5996736345600⟩, ⟨.privateRow 15 5, 5877483066000⟩, ⟨.privateRow 16 1, 752938436250⟩, ⟨.privateRow 16 2, 1978490537100⟩, ⟨.privateRow 17 0, 642507465600⟩, ⟨.privateRow 18 0, 612647343000⟩, ⟨.privateRow 19 0, 1365328364400⟩, ⟨.privateRow 20 0, 4716588895200⟩, ⟨.privateRow 21 0, 15564743354160⟩, ⟨.privateRow 22 0, 90794336232600⟩, ⟨.privateRow 22 2, 38911858385400⟩, ⟨.privateRow 23 0, 749053273918950⟩, ⟨.privateRow 24 0, 6563133447670800⟩, ⟨.privateRow 25 0, 183767736534782400⟩, ⟨.hall 9 15, 219825906300⟩, ⟨.hall 9 16, 823855032000⟩, ⟨.hall 8 17, 3132004715840⟩, ⟨.hall 8 18, 2944928357280⟩, ⟨.hall 10 19, 735349794379200⟩, ⟨.hall 7 20, 176720980035600⟩, ⟨.hall 7 21, 578084346730800⟩, ⟨.hall 6 23, 112756837636292850⟩, ⟨.hall 5 24, 222575829964488000⟩, ⟨.hall 4 25, 308295660767648400⟩, ⟨.hall 3 26, 320039946960333600⟩, ⟨.assumptionRow 17, 8367957797472⟩]
  caps := #[0, 0, 0, 2012274972489600, 139216440854400, 0, 29100102752448, 15314299298298, 2864204415072, 93342762240, 512566626663, 3006954867462, 971892420408, 682732211616, 5668332480720, 162290434320, 1621629408672, 2224132511328, 0, 24575910559200, 0, 1400826901874400, 0, 0, 150952069296428400, 0] }

theorem case_55_30_17_checked :
    (Witness.linear .conditional case_55_30_17).check 55 30 17 = true := by
  change case_55_30_17.check 55 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_30_18 : Certificate := {
  objectiveScale := 3968811000000
  eta := 8715841218506822400
  rows := #[⟨.path 2, 142201224699534000⟩, ⟨.path 14, 306639197280⟩, ⟨.privateRow 2 28, 226975031731948500⟩, ⟨.privateRow 5 22, 5398186525437420⟩, ⟨.privateRow 6 20, 1504110091703076⟩, ⟨.privateRow 7 18, 407690300391660⟩, ⟨.privateRow 7 19, 1836144296641512⟩, ⟨.privateRow 8 16, 105047930919360⟩, ⟨.privateRow 8 17, 584449033468300⟩, ⟨.privateRow 8 18, 1476588972814956⟩, ⟨.privateRow 9 15, 233204713684800⟩, ⟨.privateRow 9 16, 491211235394880⟩, ⟨.privateRow 9 17, 1017263508957696⟩, ⟨.privateRow 18 0, 387426510240⟩, ⟨.privateRow 19 0, 404722336590⟩, ⟨.privateRow 20 0, 1398131708220⟩, ⟨.privateRow 21 0, 4101186344112⟩, ⟨.privateRow 22 2, 15379448790420⟩, ⟨.privateRow 24 3, 2269750317319485⟩, ⟨.hall 22 1, 98684796405195⟩, ⟨.hall 23 1, 1297000181325420⟩, ⟨.hall 12 17, 387813936750240⟩, ⟨.hall 11 18, 1480416668771040⟩, ⟨.hall 10 19, 3745633803551640⟩, ⟨.hall 9 20, 7996805484164640⟩, ⟨.hall 8 21, 15099560810093760⟩, ⟨.hall 7 22, 28990788868641600⟩, ⟨.hall 6 23, 51269955784330140⟩, ⟨.hall 5 24, 83930778532252080⟩, ⟨.hall 4 25, 124268312295638280⟩, ⟨.hall 3 26, 176492275882002080⟩, ⟨.hall 2 27, 207520029012067200⟩, ⟨.mean 9, 1811788680240⟩, ⟨.mean 13, 853532073680⟩, ⟨.tail 3 0, 1616851704302714880⟩, ⟨.tail 3 16, 789478371241560⟩, ⟨.tail 3 17, 1578956742483120⟩, ⟨.tail 3 18, 15000089053589640⟩, ⟨.tail 3 20, 83684707351605360⟩, ⟨.tail 3 23, 71842531782981960⟩, ⟨.tail 3 27, 57631921100633880⟩, ⟨.tail 4 2, 220479777859461120⟩, ⟨.tail 4 13, 753592990730580⟩, ⟨.tail 4 15, 3767964953652900⟩, ⟨.tail 4 25, 19055137051330380⟩, ⟨.tail 4 26, 64055404212099300⟩, ⟨.tail 5 0, 10499037040926720⟩, ⟨.tail 5 2, 820237268822400⟩, ⟨.tail 5 9, 9781329430707120⟩, ⟨.tail 5 16, 11196238719425760⟩, ⟨.tail 5 19, 4449787183361520⟩, ⟨.tail 5 24, 16199686059242400⟩, ⟨.tail 5 25, 47307184479331920⟩, ⟨.tail 6 0, 174300419624760⟩, ⟨.tail 6 1, 2491470704048040⟩, ⟨.tail 6 2, 164047453764480⟩, ⟨.tail 6 10, 2440205874746640⟩, ⟨.tail 6 16, 1901925167081940⟩, ⟨.tail 6 22, 5751913847617080⟩, ⟨.tail 6 23, 16445757239889120⟩, ⟨.tail 6 24, 34747301300488920⟩, ⟨.tail 7 0, 194266721563200⟩, ⟨.tail 7 2, 6475557385440⟩, ⟨.tail 7 3, 692884640242080⟩, ⟨.tail 7 14, 699360197627520⟩, ⟨.tail 7 21, 3373765397814240⟩, ⟨.tail 7 22, 10933978645315440⟩, ⟨.tail 7 23, 20242592386885440⟩, ⟨.tail 8 0, 114581390403480⟩, ⟨.tail 8 2, 2518272316560⟩, ⟨.tail 8 6, 108285709612080⟩, ⟨.tail 8 11, 112692686166060⟩, ⟨.tail 8 14, 53513286726900⟩, ⟨.tail 8 20, 2010210876694020⟩, ⟨.tail 8 21, 6103032959183160⟩, ⟨.tail 8 22, 10427536094795820⟩, ⟨.tail 9 1, 53920654307520⟩, ⟨.tail 9 2, 888801994080⟩, ⟨.tail 9 8, 50365446331200⟩, ⟨.tail 9 19, 1090856314067520⟩, ⟨.tail 9 20, 3034962542451840⟩, ⟨.tail 9 21, 4456749465648480⟩, ⟨.tail 10 1, 30330368047980⟩, ⟨.tail 10 14, 53161469270910⟩, ⟨.tail 10 15, 252142015695570⟩, ⟨.tail 10 16, 629271811808640⟩, ⟨.tail 10 17, 1262876533338420⟩, ⟨.tail 10 18, 1787658560718030⟩, ⟨.tail 10 19, 2536252040231910⟩, ⟨.tail 10 20, 2560582994819850⟩, ⟨.tail 11 1, 4666210468920⟩, ⟨.tail 11 3, 555501246300⟩, ⟨.tail 11 7, 3777408474840⟩, ⟨.tail 11 9, 1111002492600⟩, ⟨.tail 11 12, 14331932154540⟩, ⟨.tail 11 13, 51772716155160⟩, ⟨.tail 11 14, 156318050708820⟩, ⟨.tail 11 15, 383406960196260⟩, ⟨.tail 11 16, 733039444617480⟩, ⟨.tail 11 17, 1160442103520700⟩, ⟨.tail 11 18, 1328870081398860⟩, ⟨.tail 11 19, 870026051955060⟩, ⟨.tail 12 1, 3753601278570⟩, ⟨.tail 12 11, 20688453558630⟩, ⟨.tail 12 12, 50193505469250⟩, ⟨.tail 12 13, 111822400880190⟩, ⟨.tail 12 14, 227572989144930⟩, ⟨.tail 12 15, 413070726748680⟩, ⟨.tail 12 16, 619606090123020⟩, ⟨.tail 12 17, 713446122087270⟩, ⟨.tail 12 18, 198591695552250⟩, ⟨.tail 13 0, 322312811040⟩, ⟨.tail 13 1, 1369829446920⟩, ⟨.tail 13 8, 966938433120⟩, ⟨.tail 13 9, 5157004976640⟩, ⟨.tail 13 11, 57693993176160⟩, ⟨.tail 13 12, 80658780962760⟩, ⟨.tail 13 13, 123848697642120⟩, ⟨.tail 13 14, 237544541736480⟩, ⟨.tail 13 15, 317881009888200⟩, ⟨.tail 13 16, 279042316157880⟩, ⟨.tail 13 17, 113695844094360⟩, ⟨.tail 14 1, 611051370930⟩, ⟨.tail 14 8, 7594495610130⟩, ⟨.tail 14 9, 13181251001490⟩, ⟨.tail 14 10, 15014405114280⟩, ⟨.tail 14 11, 72540527034690⟩, ⟨.tail 14 12, 76468714419240⟩, ⟨.tail 14 13, 123956135245800⟩, ⟨.tail 14 15, 117409156271550⟩, ⟨.tail 14 16, 198591695552250⟩, ⟨.tail 15 1, 333300747780⟩, ⟨.tail 15 5, 555501246300⟩, ⟨.tail 15 6, 1777603988160⟩, ⟨.tail 15 7, 3888508724100⟩, ⟨.tail 15 8, 13998631406760⟩, ⟨.tail 15 9, 19331443371240⟩, ⟨.tail 15 10, 21997849353480⟩, ⟨.tail 15 11, 80214379965720⟩, ⟨.tail 15 12, 71548560523440⟩, ⟨.tail 16 1, 166650373890⟩, ⟨.tail 16 3, 166650373890⟩, ⟨.tail 16 4, 833251869450⟩, ⟨.tail 16 5, 2333105234460⟩, ⟨.tail 16 6, 4332909721140⟩, ⟨.tail 16 7, 7499266825050⟩, ⟨.tail 16 8, 19998044866800⟩, ⟨.tail 16 12, 999902243340⟩, ⟨.tail 16 13, 11165575050630⟩, ⟨.tail 16 14, 14831883276210⟩, ⟨.tail 17 2, 592534662720⟩, ⟨.tail 17 3, 888801994080⟩, ⟨.tail 17 4, 2370138650880⟩, ⟨.tail 17 5, 4444009970400⟩, ⟨.tail 17 11, 7406683284000⟩, ⟨.tail 18 1, 629568079140⟩, ⟨.tail 19 1, 1618889346360⟩, ⟨.tail 20 1, 5126482930140⟩, ⟨.tail 21 1, 20505931720560⟩, ⟨.tail 22 1, 107656141532940⟩, ⟨.tail 23 1, 789478371241560⟩, ⟨.tail 24 1, 9079001269277940⟩, ⟨.tailUpper 18 0, 629568079140⟩, ⟨.assumptionRow 18, 2943011697912⟩]
  caps := #[0, 4030850154436560, 0, 85990926991680, 602097423368760, 65387990657880, 22044780438228, 11023001702856, 0, 5259718620048, 0, 2060540382420, 2065044227688, 0, 1571219934282, 250708656924, 1473956306262, 1056338735760, 1971258278088, 11253813058620, 0, 0, 484452636898230, 20427752855875365, 0, 0] }

theorem case_55_30_18_checked :
    (Witness.linear .conditional case_55_30_18).check 55 30 18 = true := by
  change case_55_30_18.check 55 30 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_30_19 : Certificate := {
  objectiveScale := 762701940000000
  eta := 2135381098534171488000
  rows := #[⟨.count 2, 325391405490921369600⟩, ⟨.count 3, 84553133559971076000⟩, ⟨.count 4, 25501586806322827200⟩, ⟨.count 5, 7736888038167288000⟩, ⟨.count 6, 2359822622402044800⟩, ⟨.count 7, 720276247982491200⟩, ⟨.count 8, 218586037077408000⟩, ⟨.count 9, 65700243402393600⟩, ⟨.count 10, 23097741821154000⟩, ⟨.count 11, 7699247273718000⟩, ⟨.count 12, 2493089593394400⟩, ⟨.count 13, 1026566303162400⟩, ⟨.count 14, 513283151581200⟩, ⟨.count 15, 233310523446000⟩, ⟨.count 16, 373296837513600⟩, ⟨.path 2, 41347740720326040000⟩, ⟨.path 13, 46172473155900⟩, ⟨.path 14, 46231755897600⟩, ⟨.privateRow 2 28, 49571346930257552400⟩, ⟨.privateRow 6 20, 264403483604900640⟩, ⟨.privateRow 7 18, 64480362665518800⟩, ⟨.privateRow 7 19, 343049128051069440⟩, ⟨.privateRow 7 20, 645710204689149600⟩, ⟨.privateRow 8 16, 14114916334318800⟩, ⟨.privateRow 8 17, 101316390976000200⟩, ⟨.privateRow 8 18, 290031940970531760⟩, ⟨.privateRow 8 19, 555455324863639200⟩, ⟨.privateRow 9 14, 2343474591057600⟩, ⟨.privateRow 9 15, 28939392927244800⟩, ⟨.privateRow 9 16, 94810483824056000⟩, ⟨.privateRow 9 17, 212953402573591680⟩, ⟨.privateRow 9 18, 374634484514690400⟩, ⟨.privateRow 10 13, 7754658523036425⟩, ⟨.privateRow 10 14, 30643670750893200⟩, ⟨.privateRow 10 15, 75534281965642500⟩, ⟨.privateRow 10 16, 144946495796061960⟩, ⟨.privateRow 10 17, 225208815519337650⟩, ⟨.privateRow 11 11, 1538121228644000⟩, ⟨.privateRow 11 12, 9622114837785450⟩, ⟨.privateRow 11 13, 26977362525313200⟩, ⟨.privateRow 11 14, 55833800599777200⟩, ⟨.privateRow 11 15, 93607292813514480⟩, ⟨.privateRow 11 16, 125727152576325300⟩, ⟨.privateRow 12 9, 270084705951060⟩, ⟨.privateRow 12 10, 2650605057900800⟩, ⟨.privateRow 12 11, 9553788184490550⟩, ⟨.privateRow 12 12, 22015307964078000⟩, ⟨.privateRow 12 13, 39750928516899600⟩, ⟨.privateRow 12 14, 58744034595726480⟩, ⟨.privateRow 12 15, 68126117344985700⟩, ⟨.privateRow 13 8, 688137851570400⟩, ⟨.privateRow 13 9, 3163679303030400⟩, ⟨.privateRow 13 10, 8746965355104900⟩, ⟨.privateRow 13 11, 17511255023803200⟩, ⟨.privateRow 13 12, 28234333653094800⟩, ⟨.privateRow 13 13, 37148163036415200⟩, ⟨.privateRow 13 14, 1945963596654000⟩, ⟨.privateRow 14 6, 83325186945000⟩, ⟨.privateRow 14 7, 1016789481227520⟩, ⟨.privateRow 14 8, 3377077243339800⟩, ⟨.privateRow 14 9, 7870341657578400⟩, ⟨.privateRow 14 10, 14204325582532800⟩, ⟨.privateRow 14 11, 7929409956768300⟩, ⟨.privateRow 15 5, 221998498066800⟩, ⟨.privateRow 15 6, 1286318685932280⟩, ⟨.privateRow 15 7, 3527309469283600⟩, ⟨.privateRow 15 8, 6375210053161950⟩, ⟨.privateRow 16 3, 15554034896400⟩, ⟨.privateRow 16 4, 396627889858200⟩, ⟨.privateRow 16 5, 1567846717557120⟩, ⟨.privateRow 16 6, 1547626472191800⟩, ⟨.privateRow 17 2, 69129043984000⟩, ⟨.privateRow 17 3, 607078695350400⟩, ⟨.privateRow 17 4, 265455528898560⟩, ⟨.privateRow 18 1, 198313944929100⟩, ⟨.privateRow 19 0, 37774084748400⟩, ⟨.hall 10 16, 314246883050100⟩, ⟨.hall 10 17, 3080449323451500⟩, ⟨.hall 9 18, 10726156022662080⟩, ⟨.hall 11 18, 182386613195186400⟩, ⟨.hall 9 19, 5040396108427680⟩, ⟨.hall 8 20, 44707727859995200⟩, ⟨.hall 7 21, 403795410460696800⟩, ⟨.hall 8 21, 3642822844889155200⟩, ⟨.hall 6 23, 16183768329744315300⟩, ⟨.hall 4 24, 1687399049890639008⟩, ⟨.hall 5 24, 29055100726042110720⟩, ⟨.hall 3 26, 53138911970079135200⟩, ⟨.hall 2 27, 55654277780673772200⟩, ⟨.assumptionRow 19, 306954192837600⟩]
  caps := #[0, 0, 0, 20988064626429600, 0, 5469853733479800, 0, 0, 1398781120857120, 0, 125219349052980, 285921883028600, 0, 69065729567100, 217273191436860, 272932125922820, 0, 306954192837600, 1517956716761100, 0, 762701940000000, 0, 0, 0, 0, 0] }

theorem case_55_30_19_checked :
    (Witness.linear .conditional case_55_30_19).check 55 30 19 = true := by
  change case_55_30_19.check 55 30 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_31_1_checked :
    (Witness.rising).check 55 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_31_2_checked :
    (Witness.rising).check 55 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_31_3_checked :
    (Witness.rising).check 55 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_31_4_checked :
    (Witness.rising).check 55 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_31_5_checked :
    (Witness.rising).check 55 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_31_6_checked :
    (Witness.rising).check 55 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_31_7_checked :
    (Witness.rising).check 55 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_31_8_checked :
    (Witness.rising).check 55 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_31_9_checked :
    (Witness.rising).check 55 31 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_31_10_checked :
    (Witness.rising).check 55 31 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_31_11_checked :
    (Witness.linear .positive case_55_31_11).check 55 31 11 = true := by
  change case_55_31_11.check 55 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_31_12_checked :
    (Witness.linear .positive case_55_31_12).check 55 31 12 = true := by
  change case_55_31_12.check 55 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_31_13 : Certificate := {
  objectiveScale := 5396554800000
  eta := 29402837845565184000
  rows := #[⟨.count 2, 6383931369186571200⟩, ⟨.count 3, 978399767242497600⟩, ⟨.count 4, 152949544693545600⟩, ⟨.count 5, 26408181224224800⟩, ⟨.count 6, 4816878469603200⟩, ⟨.count 7, 949358322712800⟩, ⟨.count 8, 206887403923200⟩, ⟨.count 9, 50597462916000⟩, ⟨.count 10, 14617044842400⟩, ⟨.count 11, 6184134356400⟩, ⟨.count 12, 5708431713600⟩, ⟨.path 13, 791981777664⟩, ⟨.path 14, 1109834631360⟩, ⟨.privateRow 5 23, 1387856282412600⟩, ⟨.privateRow 6 19, 90111672050400⟩, ⟨.privateRow 6 20, 329499245275200⟩, ⟨.privateRow 6 21, 460934855821440⟩, ⟨.privateRow 6 22, 862204862118600⟩, ⟨.privateRow 6 23, 168390498276000⟩, ⟨.privateRow 7 16, 33576964220800⟩, ⟨.privateRow 7 17, 87949902140100⟩, ⟨.privateRow 7 18, 139653586987200⟩, ⟨.privateRow 7 19, 202978816840800⟩, ⟨.privateRow 7 20, 267604359422400⟩, ⟨.privateRow 7 21, 314025523812000⟩, ⟨.privateRow 7 22, 115597801519200⟩, ⟨.privateRow 8 13, 9608407099200⟩, ⟨.privateRow 8 14, 24774017027760⟩, ⟨.privateRow 8 15, 41144274371200⟩, ⟨.privateRow 8 16, 58140232850700⟩, ⟨.privateRow 8 17, 71104159526400⟩, ⟨.privateRow 8 18, 96447509558400⟩, ⟨.privateRow 8 19, 89126493936480⟩, ⟨.privateRow 8 20, 48442385791800⟩, ⟨.privateRow 9 10, 2479419835200⟩, ⟨.privateRow 9 11, 7183590414000⟩, ⟨.privateRow 9 12, 12487521992400⟩, ⟨.privateRow 9 13, 18065168241120⟩, ⟨.privateRow 9 14, 22904201320000⟩, ⟨.privateRow 9 15, 26423119522800⟩, ⟨.privateRow 9 16, 16303626939600⟩, ⟨.privateRow 10 7, 599673634560⟩, ⟨.privateRow 10 8, 2168462696400⟩, ⟨.privateRow 10 9, 3468304722960⟩, ⟨.privateRow 10 10, 7046165206080⟩, ⟨.privateRow 10 11, 7390296098640⟩, ⟨.privateRow 10 12, 2057630158584⟩, ⟨.privateRow 11 4, 113383670400⟩, ⟨.privateRow 11 5, 712781719650⟩, ⟨.privateRow 11 6, 1370682593280⟩, ⟨.privateRow 11 7, 2007835830000⟩, ⟨.privateRow 12 2, 268054663800⟩, ⟨.privateRow 12 3, 383760115200⟩, ⟨.privateRow 13 0, 118031482800⟩, ⟨.privateRow 14 0, 62466003600⟩, ⟨.privateRow 15 0, 79368569280⟩, ⟨.privateRow 16 0, 128836132425⟩, ⟨.privateRow 17 0, 224877612960⟩, ⟨.privateRow 17 4, 68144731200⟩, ⟨.privateRow 18 0, 650156364000⟩, ⟨.privateRow 19 0, 1890454658400⟩, ⟨.privateRow 20 0, 7782371677080⟩, ⟨.privateRow 21 0, 33016122266400⟩, ⟨.privateRow 21 6, 10376495569440⟩, ⟨.privateRow 22 0, 217906406958240⟩, ⟨.privateRow 22 2, 45397168116300⟩, ⟨.privateRow 23 0, 2663300529489600⟩, ⟨.privateRow 24 0, 68912901200543400⟩, ⟨.hall 6 21, 433235419344⟩, ⟨.hall 5 22, 1935615519684⟩, ⟨.hall 4 26, 11921440465334400⟩, ⟨.hall 3 27, 10661849197599600⟩]
  caps := #[0, 45638707116038400, 0, 66727320791040, 120148896067200, 17068998411360, 5988698876160, 1419374695992, 0, 896797070960, 889142717736, 4402221264, 0, 3320596944, 0, 0, 1932541986375, 0, 0, 34028183851200, 0, 90086847898320, 0, 58592611648771200, 0] }

theorem case_55_31_13_checked :
    (Witness.linear .positive case_55_31_13).check 55 31 13 = true := by
  change case_55_31_13.check 55 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_31_14 : Certificate := {
  objectiveScale := 35446844160000
  eta := 238898057495217120000
  rows := #[⟨.count 2, 48298955102293896000⟩, ⟨.count 3, 8555005537180502400⟩, ⟨.count 4, 1594452309200150400⟩, ⟨.count 5, 312280634162296800⟩, ⟨.count 6, 64536341128459200⟩, ⟨.count 7, 14081086531512000⟩, ⟨.count 8, 3235239258451200⟩, ⟨.count 9, 811245988753200⟩, ⟨.count 10, 233872717478400⟩, ⟨.count 11, 80393746633200⟩, ⟨.count 12, 31804119547200⟩, ⟨.count 13, 34454462842800⟩, ⟨.path 15, 9747882144000⟩, ⟨.privateRow 5 23, 21684281616237240⟩, ⟨.privateRow 5 26, 200588035852844640⟩, ⟨.privateRow 6 20, 4218409536541200⟩, ⟨.privateRow 6 21, 7653484679480640⟩, ⟨.privateRow 6 22, 15548359413787200⟩, ⟨.privateRow 6 23, 12696643570010400⟩, ⟨.privateRow 7 17, 761739449971500⟩, ⟨.privateRow 7 18, 1886493705782400⟩, ⟨.privateRow 7 19, 3374333201038800⟩, ⟨.privateRow 7 20, 5286915514520640⟩, ⟨.privateRow 7 21, 6880799847121200⟩, ⟨.privateRow 8 14, 119372532879600⟩, ⟨.privateRow 8 15, 454752506208000⟩, ⟨.privateRow 8 16, 835607730157200⟩, ⟨.privateRow 8 17, 1275859199815200⟩, ⟨.privateRow 8 18, 2035829523327600⟩, ⟨.privateRow 8 20, 6820069506049800⟩, ⟨.privateRow 9 11, 10962783631800⟩, ⟨.privateRow 9 12, 106527251048400⟩, ⟨.privateRow 9 13, 213408854699040⟩, ⟨.privateRow 9 14, 360824458794800⟩, ⟨.privateRow 9 15, 504897090597900⟩, ⟨.privateRow 9 16, 744773237208000⟩, ⟨.privateRow 9 17, 893669880503400⟩, ⟨.privateRow 9 18, 123270411504240⟩, ⟨.privateRow 9 19, 1455614048889000⟩, ⟨.privateRow 10 9, 20238985166400⟩, ⟨.privateRow 10 10, 55788387815160⟩, ⟨.privateRow 10 11, 104711193961920⟩, ⟨.privateRow 10 12, 154940675329440⟩, ⟨.privateRow 10 13, 210485445730560⟩, ⟨.privateRow 10 14, 295995158058600⟩, ⟨.privateRow 10 15, 341830034385840⟩, ⟨.privateRow 11 7, 19091650406400⟩, ⟨.privateRow 11 8, 28029388186800⟩, ⟨.privateRow 11 9, 50463607194000⟩, ⟨.privateRow 11 10, 73275055963200⟩, ⟨.privateRow 11 11, 93549086991360⟩, ⟨.privateRow 11 12, 131901428458800⟩, ⟨.privateRow 11 15, 56032005229200⟩, ⟨.privateRow 12 5, 14488543349280⟩, ⟨.privateRow 12 6, 16217576832600⟩, ⟨.privateRow 12 7, 25280197588800⟩, ⟨.privateRow 12 8, 11779303536000⟩, ⟨.privateRow 12 9, 99909910900800⟩, ⟨.privateRow 12 10, 41257010634840⟩, ⟨.privateRow 13 4, 27327984203520⟩, ⟨.privateRow 13 5, 13125509654400⟩, ⟨.privateRow 13 6, 14406994324800⟩, ⟨.privateRow 13 7, 7877409239700⟩, ⟨.privateRow 13 8, 88826657119200⟩, ⟨.privateRow 13 14, 9187856758080⟩, ⟨.privateRow 14 1, 5588870086800⟩, ⟨.privateRow 14 2, 3327987888225⟩, ⟨.privateRow 14 3, 12111265726560⟩, ⟨.privateRow 14 4, 29532396722400⟩, ⟨.privateRow 14 6, 15835131912600⟩, ⟨.privateRow 14 7, 94915875600000⟩, ⟨.privateRow 15 0, 12983375124720⟩, ⟨.privateRow 15 2, 16273643257872⟩, ⟨.privateRow 15 3, 35394130011240⟩, ⟨.privateRow 15 6, 143911450584720⟩, ⟨.privateRow 16 0, 45526004248725⟩, ⟨.privateRow 16 2, 55161943036200⟩, ⟨.privateRow 16 6, 142516187213400⟩, ⟨.privateRow 16 12, 58468179369600⟩, ⟨.privateRow 17 0, 118235651614080⟩, ⟨.privateRow 17 2, 93324209378400⟩, ⟨.privateRow 17 4, 54038771841600⟩, ⟨.privateRow 17 6, 210593720136800⟩, ⟨.privateRow 18 0, 483456272270400⟩, ⟨.privateRow 18 5, 602160376417600⟩, ⟨.privateRow 18 12, 41414960386800⟩, ⟨.privateRow 19 0, 1256102095248000⟩, ⟨.privateRow 19 2, 225899783928000⟩, ⟨.privateRow 19 4, 35498537474400⟩, ⟨.privateRow 19 8, 134894442402720⟩, ⟨.privateRow 19 12, 1029457586757600⟩, ⟨.privateRow 20 0, 6767204527203120⟩, ⟨.privateRow 20 6, 5463224917310160⟩, ⟨.privateRow 21 0, 36176236826184000⟩, ⟨.privateRow 21 6, 23471632978073280⟩, ⟨.privateRow 21 10, 3372361060068000⟩, ⟨.privateRow 22 0, 250229190657045600⟩, ⟨.privateRow 23 0, 3006422414372176800⟩, ⟨.privateRow 23 5, 259671801625236000⟩, ⟨.privateRow 24 0, 71818728534499646700⟩, ⟨.hall 18 2, 188415314287200⟩, ⟨.hall 21 3, 5901631855119000⟩, ⟨.hall 18 5, 165494347200⟩, ⟨.hall 22 6, 27203712551215200⟩, ⟨.hall 23 6, 639905511147903000⟩, ⟨.hall 17 8, 124120760400⟩, ⟨.hall 19 8, 8516063283000⟩, ⟨.hall 16 11, 1677658382400⟩, ⟨.hall 17 12, 42325179296400⟩, ⟨.hall 9 13, 1929662280⟩, ⟨.hall 15 13, 4111043861925⟩, ⟨.hall 13 15, 65681165550⟩, ⟨.hall 14 16, 6878609337600⟩, ⟨.hall 6 18, 227809271664⟩, ⟨.hall 8 18, 15059116800⟩, ⟨.hall 5 21, 5674261510008⟩, ⟨.hall 7 23, 5618629625809200⟩, ⟨.hall 4 24, 320057241119616⟩, ⟨.hall 6 24, 8519648993856000⟩, ⟨.hall 3 27, 286819308158783400⟩]
  caps := #[0, 0, 48116653976664000, 4540585656952800, 0, 358671761327880, 364542673294800, 0, 31032218217000, 7576111342800, 2098653331320, 11785909402800, 3642724612800, 15562241694000, 0, 19972518038928, 35215767261675, 0, 0, 385816971627360, 0, 1778154013490400, 61376971293237600, 582818932536640800, 0] }

theorem case_55_31_14_checked :
    (Witness.linear .positive case_55_31_14).check 55 31 14 = true := by
  change case_55_31_14.check 55 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_31_15 : Certificate := {
  objectiveScale := 191456720000000
  eta := 1838320552425695738400
  rows := #[⟨.count 2, 401037130430014478400⟩, ⟨.count 3, 84006188478505893600⟩, ⟨.count 4, 19012022712239356800⟩, ⟨.count 5, 4091348438074497600⟩, ⟨.count 6, 973795879997740800⟩, ⟨.count 7, 223640786088720000⟩, ⟨.count 8, 56129452194816000⟩, ⟨.count 9, 14405097692185200⟩, ⟨.count 10, 3946602107448000⟩, ⟨.count 11, 1240360662340800⟩, ⟨.count 12, 381649434566400⟩, ⟨.count 13, 206726777056800⟩, ⟨.count 14, 131553403581600⟩, ⟨.path 16, 43513037445150⟩, ⟨.privateRow 3 28, 3824257442117112000⟩, ⟨.privateRow 6 23, 913519363366209600⟩, ⟨.privateRow 7 19, 54064272573511200⟩, ⟨.privateRow 7 20, 55249923725156160⟩, ⟨.privateRow 7 23, 1341525229695050400⟩, ⟨.privateRow 8 16, 5711610272167800⟩, ⟨.privateRow 8 17, 11714517366552000⟩, ⟨.privateRow 8 18, 38990967117102000⟩, ⟨.privateRow 8 19, 47367995516281440⟩, ⟨.privateRow 9 13, 467014582714680⟩, ⟨.privateRow 9 14, 2533621106016000⟩, ⟨.privateRow 9 15, 5952791512067400⟩, ⟨.privateRow 9 16, 11113130378750400⟩, ⟨.privateRow 9 17, 23332457829681000⟩, ⟨.privateRow 9 18, 29147849120229840⟩, ⟨.privateRow 9 20, 61625461055558400⟩, ⟨.privateRow 9 22, 536650184343873600⟩, ⟨.privateRow 10 11, 406619611070400⟩, ⟨.privateRow 10 12, 1120834998515232⟩, ⟨.privateRow 10 13, 2389886831732400⟩, ⟨.privateRow 10 14, 4883920107966900⟩, ⟨.privateRow 10 15, 7351955925874560⟩, ⟨.privateRow 10 16, 12392330617386720⟩, ⟨.privateRow 11 8, 17347701571200⟩, ⟨.privateRow 11 9, 223170952504500⟩, ⟨.privateRow 11 10, 548423929216800⟩, ⟨.privateRow 11 12, 4042656973555200⟩, ⟨.privateRow 11 14, 9373851196023600⟩, ⟨.privateRow 11 15, 4729658081148000⟩, ⟨.privateRow 11 16, 3448578508174800⟩, ⟨.privateRow 12 7, 159020597736000⟩, ⟨.privateRow 12 8, 228592109245500⟩, ⟨.privateRow 12 9, 451040240851200⟩, ⟨.privateRow 12 10, 35779634490600⟩, ⟨.privateRow 12 11, 2751056340832800⟩, ⟨.privateRow 12 12, 110320539679350⟩, ⟨.privateRow 12 13, 4599102858807600⟩, ⟨.privateRow 12 14, 3538208299626000⟩, ⟨.privateRow 12 19, 2941881058116000⟩, ⟨.privateRow 13 4, 17492265750960⟩, ⟨.privateRow 13 5, 52817555676600⟩, ⟨.privateRow 13 6, 166360009939200⟩, ⟨.privateRow 13 7, 219315907710900⟩, ⟨.privateRow 13 8, 445980494559600⟩, ⟨.privateRow 13 9, 75534783924600⟩, ⟨.privateRow 13 10, 2144127726140400⟩, ⟨.privateRow 13 11, 673849782906300⟩, ⟨.privateRow 13 12, 2966870009188800⟩, ⟨.privateRow 13 13, 3743609905035000⟩, ⟨.privateRow 13 15, 4714960722872400⟩, ⟨.privateRow 14 3, 69535370464560⟩, ⟨.privateRow 14 4, 50339312595000⟩, ⟨.privateRow 14 5, 168417269420400⟩, ⟨.privateRow 14 6, 237265960031100⟩, ⟨.privateRow 14 7, 439935083406000⟩, ⟨.privateRow 14 8, 99604719854640⟩, ⟨.privateRow 14 9, 1754045381088000⟩, ⟨.privateRow 14 10, 1057125564495000⟩, ⟨.privateRow 14 11, 2111566365651600⟩, ⟨.privateRow 14 12, 3364008463015200⟩, ⟨.privateRow 14 16, 25347521868669000⟩, ⟨.privateRow 15 0, 19346088762000⟩, ⟨.privateRow 15 2, 96472495959840⟩, ⟨.privateRow 15 3, 46043691253560⟩, ⟨.privateRow 15 4, 214533242763840⟩, ⟨.privateRow 15 5, 280647260974080⟩, ⟨.privateRow 15 6, 503490753707760⟩, ⟨.privateRow 15 7, 182859230978424⟩, ⟨.privateRow 15 8, 1603489819211280⟩, ⟨.privateRow 15 9, 1542463656994260⟩, ⟨.privateRow 15 10, 1999611734440320⟩, ⟨.privateRow 15 11, 3262524408823680⟩, ⟨.privateRow 16 0, 93183660870300⟩, ⟨.privateRow 16 1, 8770226905440⟩, ⟨.privateRow 16 2, 217689560688600⟩, ⟨.privateRow 16 4, 869714168122800⟩, ⟨.privateRow 16 6, 1251949890751560⟩, ⟨.privateRow 16 7, 1244884985744400⟩, ⟨.privateRow 16 8, 2261074124058750⟩, ⟨.privateRow 16 9, 2584084713210000⟩, ⟨.privateRow 16 10, 3734654957233200⟩, ⟨.privateRow 16 12, 5327912845054800⟩, ⟨.privateRow 17 0, 371272938996960⟩, ⟨.privateRow 17 2, 428391852688800⟩, ⟨.privateRow 17 3, 1103586885601200⟩, ⟨.privateRow 17 4, 326890275566400⟩, ⟨.privateRow 17 5, 1289223355099680⟩, ⟨.privateRow 17 6, 2733387385528800⟩, ⟨.privateRow 17 7, 2899656270611100⟩, ⟨.privateRow 17 8, 4090684406608800⟩, ⟨.privateRow 17 10, 859482236733120⟩, ⟨.privateRow 18 0, 1650681992559600⟩, ⟨.privateRow 18 3, 5295736363226400⟩, ⟨.privateRow 18 5, 4614809871672000⟩, ⟨.privateRow 18 6, 6043626005016600⟩, ⟨.privateRow 18 7, 7454692869624000⟩, ⟨.privateRow 18 9, 13269353307930720⟩, ⟨.privateRow 19 0, 6586344029865600⟩, ⟨.privateRow 19 2, 7783861126204800⟩, ⟨.privateRow 19 4, 17536277512353600⟩, ⟨.privateRow 19 5, 8905695588890100⟩, ⟨.privateRow 19 6, 17754339956839200⟩, ⟨.privateRow 19 7, 8359905575221200⟩, ⟨.privateRow 20 0, 40873016048024160⟩, ⟨.privateRow 20 2, 10926449834620320⟩, ⟨.privateRow 20 3, 10251977622606720⟩, ⟨.privateRow 20 4, 88322136163180920⟩, ⟨.privateRow 20 7, 143257897831688640⟩, ⟨.privateRow 20 10, 122619048144072480⟩, ⟨.privateRow 20 11, 307154645350993440⟩, ⟨.privateRow 21 0, 269298359560339200⟩, ⟨.privateRow 21 4, 546322491731016000⟩, ⟨.privateRow 21 6, 77699198823966720⟩, ⟨.privateRow 22 0, 59488449099599520⟩, ⟨.privateRow 22 5, 3067904303565060960⟩, ⟨.privateRow 23 0, 727081044550660800⟩, ⟨.privateRow 23 5, 3856126254134754600⟩, ⟨.hall 23 4, 28872536662993383360⟩, ⟨.hall 22 5, 1880765763199923600⟩, ⟨.hall 23 6, 28795748001655635000⟩, ⟨.hall 11 7, 641969763435⟩, ⟨.hall 16 8, 24360767907840⟩, ⟨.hall 17 8, 9681419311200⟩, ⟨.hall 18 8, 384277874198400⟩, ⟨.hall 21 8, 1175605065539704800⟩, ⟨.hall 20 10, 991106257726166400⟩, ⟨.hall 14 11, 3266867003400⟩, ⟨.hall 9 13, 715924296360⟩, ⟨.hall 17 13, 62992154748322800⟩, ⟨.hall 10 14, 1968549382800⟩, ⟨.hall 12 14, 8399044573920⟩, ⟨.hall 11 15, 7869591319590⟩, ⟨.hall 13 15, 33145531043625⟩, ⟨.hall 15 15, 27132889488705000⟩, ⟨.hall 14 16, 18781182970149600⟩, ⟨.hall 12 18, 743212056787200⟩, ⟨.hall 10 20, 7366990600569600⟩, ⟨.hall 8 21, 316837446307200⟩, ⟨.hall 9 21, 33546117913308000⟩, ⟨.hall 5 22, 1099040062796676⟩, ⟨.hall 6 22, 1556595434105712⟩, ⟨.hall 7 23, 1041327410225602500⟩, ⟨.hall 4 26, 6226727461309555200⟩, ⟨.hall 3 27, 6132469969680654600⟩]
  caps := #[0, 0, 736685550363999600, 41462859507651400, 0, 5636976513022400, 0, 817886303410176, 0, 0, 0, 167584141631400, 51012301582490, 184210374735740, 123515491102900, 0, 319279249516500, 253518843483360, 0, 6501684805504200, 4617068869511280, 0, 346071691984178160, 493376423087948400, 0] }

theorem case_55_31_15_checked :
    (Witness.linear .positive case_55_31_15).check 55 31 15 = true := by
  change case_55_31_15.check 55 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_31_16 : Certificate := {
  objectiveScale := 11924640000000
  eta := 155283737371891128000
  rows := #[⟨.count 2, 34276677814531152000⟩, ⟨.count 3, 7775990132304794400⟩, ⟨.count 4, 1845355972069209600⟩, ⟨.count 5, 427615382416622400⟩, ⟨.count 6, 110968428144974400⟩, ⟨.count 7, 28990472270760000⟩, ⟨.count 8, 7639842104294400⟩, ⟨.count 9, 2170631159096400⟩, ⟨.count 10, 672384062750400⟩, ⟨.count 11, 229696418952000⟩, ⟨.count 12, 84810985459200⟩, ⟨.count 13, 34454462842800⟩, ⟨.count 14, 29234089684800⟩, ⟨.path 15, 3199911728832⟩, ⟨.privateRow 3 28, 533507519702757600⟩, ⟨.privateRow 5 23, 25731114888318840⟩, ⟨.privateRow 6 21, 12609080510906880⟩, ⟨.privateRow 6 22, 29809896844127400⟩, ⟨.privateRow 7 18, 863797745210400⟩, ⟨.privateRow 7 19, 4431400761387600⟩, ⟨.privateRow 7 20, 11515725556695360⟩, ⟨.privateRow 7 21, 19047923566471800⟩, ⟨.privateRow 8 16, 588945098441700⟩, ⟨.privateRow 8 17, 1796504416106400⟩, ⟨.privateRow 8 18, 4174790418598800⟩, ⟨.privateRow 8 19, 7179892426586880⟩, ⟨.privateRow 8 20, 9842143527216000⟩, ⟨.privateRow 8 21, 6530570812365600⟩, ⟨.privateRow 9 14, 294235698957200⟩, ⟨.privateRow 9 15, 756736592361750⟩, ⟨.privateRow 9 16, 1631540624313600⟩, ⟨.privateRow 9 17, 2701311092680200⟩, ⟨.privateRow 9 18, 3759991168293360⟩, ⟨.privateRow 9 19, 4303501619016600⟩, ⟨.privateRow 9 20, 2468656462272000⟩, ⟨.privateRow 10 11, 6378346840320⟩, ⟨.privateRow 10 12, 125852756093064⟩, ⟨.privateRow 10 13, 324173572282560⟩, ⟨.privateRow 10 14, 675490184779410⟩, ⟨.privateRow 10 15, 1091684434800960⟩, ⟨.privateRow 10 16, 1498734331174080⟩, ⟨.privateRow 10 17, 1741474722523536⟩, ⟨.privateRow 10 18, 1007845241883480⟩, ⟨.privateRow 11 9, 7917565956300⟩, ⟨.privateRow 11 10, 53247806211600⟩, ⟨.privateRow 11 11, 137817851371200⟩, ⟨.privateRow 11 12, 294893079280800⟩, ⟨.privateRow 11 13, 477142106641200⟩, ⟨.privateRow 11 14, 656722943276400⟩, ⟨.privateRow 11 15, 298953369514800⟩, ⟨.privateRow 12 7, 5436601632000⟩, ⟨.privateRow 12 8, 25399123249500⟩, ⟨.privateRow 12 9, 60315388333200⟩, ⟨.privateRow 12 10, 132693854333040⟩, ⟨.privateRow 12 11, 226358949616800⟩, ⟨.privateRow 12 12, 86246588077650⟩, ⟨.privateRow 13 5, 3218274001800⟩, ⟨.privateRow 13 6, 13251716478000⟩, ⟨.privateRow 13 7, 29669120781300⟩, ⟨.privateRow 13 8, 62965731628800⟩, ⟨.privateRow 13 9, 24471503096040⟩, ⟨.privateRow 14 3, 1879334336880⟩, ⟨.privateRow 14 4, 7457675940000⟩, ⟨.privateRow 14 5, 16223313506400⟩, ⟨.privateRow 14 6, 2610186579000⟩, ⟨.privateRow 15 0, 1289739250800⟩, ⟨.privateRow 15 2, 3702984693408⟩, ⟨.privateRow 16 0, 1065826186425⟩, ⟨.privateRow 17 0, 649646437440⟩, ⟨.privateRow 18 0, 1690406546400⟩, ⟨.privateRow 19 0, 5461313457600⟩, ⟨.privateRow 20 0, 22482407067120⟩, ⟨.privateRow 21 0, 122631311275200⟩, ⟨.privateRow 22 0, 944261096819040⟩, ⟨.privateRow 23 0, 5770484480560800⟩, ⟨.privateRow 24 0, 149311285934510700⟩, ⟨.hall 6 22, 75689055554112⟩, ⟨.hall 7 22, 1958207366115000⟩, ⟨.hall 8 22, 9468455598201600⟩, ⟨.hall 6 23, 5679765995904000⟩, ⟨.hall 5 25, 339570817509924000⟩, ⟨.hall 4 26, 602828274826377600⟩, ⟨.hall 3 27, 714266072522402400⟩, ⟨.assumptionRow 16, 20074526690400⟩]
  caps := #[0, 0, 0, 5695775140255200, 1089292554735840, 364637264671680, 0, 56672371003248, 37721953323600, 0, 39165240918258, 0, 11450973818298, 3369685724496, 16700806482984, 3566612466144, 0, 22318982999040, 28736911288800, 98303642236800, 427165734275280, 2452626225504000, 0, 126950658572337600, 0] }

theorem case_55_31_16_checked :
    (Witness.linear .conditional case_55_31_16).check 55 31 16 = true := by
  change case_55_31_16.check 55 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_31_17 : Certificate := {
  objectiveScale := 172907280000000
  eta := 1108486986777807436800
  rows := #[⟨.count 2, 278627843143878228000⟩, ⟨.count 3, 70444238475442431600⟩, ⟨.count 4, 17877560451632481600⟩, ⟨.count 5, 4909483231246994400⟩, ⟨.count 6, 1374325878321396000⟩, ⟨.count 7, 393939103199241600⟩, ⟨.count 8, 116429634517996800⟩, ⟨.count 9, 35607121236086400⟩, ⟨.count 10, 11445146111599200⟩, ⟨.count 11, 3830187786024600⟩, ⟨.count 12, 1383479200303200⟩, ⟨.count 13, 499589711220600⟩, ⟨.count 14, 211947150214800⟩, ⟨.count 15, 317920725322200⟩, ⟨.path 14, 27449346873312⟩, ⟨.privateRow 2 29, 11295723370697766000⟩, ⟨.privateRow 5 23, 676765417534446240⟩, ⟨.privateRow 6 20, 17414990842649400⟩, ⟨.privateRow 6 21, 223598187843750720⟩, ⟨.privateRow 6 22, 613942768302563700⟩, ⟨.privateRow 7 18, 11250500769565200⟩, ⟨.privateRow 7 19, 78095796373194600⟩, ⟨.privateRow 7 20, 213543818746418160⟩, ⟨.privateRow 7 21, 398056933546272000⟩, ⟨.privateRow 7 22, 424994407066429200⟩, ⟨.privateRow 8 16, 5254523099075250⟩, ⟨.privateRow 8 17, 28188970978568400⟩, ⟨.privateRow 8 18, 76677769011043200⟩, ⟨.privateRow 8 19, 144604475686550880⟩, ⟨.privateRow 8 20, 222897752975898000⟩, ⟨.privateRow 8 21, 254477878357903200⟩, ⟨.privateRow 9 14, 2170495816088600⟩, ⟨.privateRow 9 15, 10429566016819950⟩, ⟨.privateRow 9 16, 28461474457416000⟩, ⟨.privateRow 9 17, 54505742130239400⟩, ⟨.privateRow 9 18, 84701146130841240⟩, ⟨.privateRow 9 19, 110583425624571900⟩, ⟨.privateRow 9 20, 105950025424042800⟩, ⟨.privateRow 10 12, 843549657854904⟩, ⟨.privateRow 10 13, 3949281899002440⟩, ⟨.privateRow 10 14, 10949719647972105⟩, ⟨.privateRow 10 15, 21461162867464320⟩, ⟨.privateRow 10 16, 33964530821921700⟩, ⟨.privateRow 10 17, 45064203078670776⟩, ⟨.privateRow 10 18, 48917402269575840⟩, ⟨.privateRow 10 19, 31749683102177040⟩, ⟨.privateRow 11 10, 316544445126000⟩, ⟨.privateRow 11 11, 1532075114409840⟩, ⟨.privateRow 11 12, 4380241104439200⟩, ⟨.privateRow 11 13, 8880964071054075⟩, ⟨.privateRow 11 14, 14505403433578200⟩, ⟨.privateRow 11 15, 19857429430839000⟩, ⟨.privateRow 11 16, 16444071040236840⟩, ⟨.privateRow 12 8, 115289933358600⟩, ⟨.privateRow 12 9, 611386010235000⟩, ⟨.privateRow 12 10, 1827985943363580⟩, ⟨.privateRow 12 11, 3603877916839200⟩, ⟨.privateRow 12 12, 7205620834912500⟩, ⟨.privateRow 12 13, 7226665822747800⟩, ⟨.privateRow 13 6, 39415361832000⟩, ⟨.privateRow 13 7, 251929854376200⟩, ⟨.privateRow 13 8, 798877720040400⟩, ⟨.privateRow 13 9, 1801084958913240⟩, ⟨.privateRow 13 10, 3074398222896000⟩, ⟨.privateRow 14 4, 10813630113000⟩, ⟨.privateRow 14 5, 108302664670200⟩, ⟨.privateRow 14 6, 368384332516200⟩, ⟨.privateRow 14 7, 889077006745200⟩, ⟨.privateRow 14 8, 186210710545860⟩, ⟨.privateRow 15 3, 48445062906240⟩, ⟨.privateRow 15 4, 182600621723520⟩, ⟨.privateRow 15 5, 121869611373510⟩, ⟨.privateRow 16 0, 13246696888425⟩, ⟨.privateRow 16 1, 7064905007160⟩, ⟨.privateRow 16 2, 47940426834300⟩, ⟨.privateRow 17 0, 14129810014320⟩, ⟨.privateRow 18 0, 12255447461400⟩, ⟨.privateRow 19 0, 39594522567600⟩, ⟨.privateRow 20 0, 162997451236620⟩, ⟨.privateRow 21 0, 889077006745200⟩, ⟨.privateRow 22 0, 6845892951938040⟩, ⟨.privateRow 23 0, 83672024968131600⟩, ⟨.privateRow 24 7, 17320109168403241200⟩, ⟨.hall 8 20, 1411651262112000⟩, ⟨.hall 9 21, 21979882873412100⟩, ⟨.hall 7 22, 35852601087603300⟩, ⟨.hall 7 23, 254519090303778300⟩, ⟨.hall 6 24, 2868851224472609376⟩, ⟨.hall 5 25, 7621886202479148600⟩, ⟨.hall 4 26, 13471558236427491200⟩, ⟨.hall 3 27, 19716171701581555200⟩, ⟨.hall 2 28, 18644435356691944800⟩, ⟨.assumptionRow 17, 206660510128800⟩]
  caps := #[0, 4896660347701340400, 0, 0, 437106590313120, 6940713560122160, 414005598995040, 1707379132086576, 183569781769374, 0, 259259773872645, 206015895468630, 23669193955680, 59072870705472, 89069311992492, 394069380721380, 0, 0, 381249886843800, 712701406216800, 3096951573495780, 17781540134904000, 143763751990698840, 1840784549298895200, 0] }

theorem case_55_31_17_checked :
    (Witness.linear .conditional case_55_31_17).check 55 31 17 = true := by
  change case_55_31_17.check 55 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_31_18 : Certificate := {
  objectiveScale := 6258469490910000000
  eta := 90057044086737317847457200
  rows := #[⟨.path 13, 1026498241338560928⟩, ⟨.privateRow 2 29, 707891282430752682662400⟩, ⟨.privateRow 4 25, 68663156047463429852400⟩, ⟨.privateRow 5 23, 22509448854890208070860⟩, ⟨.privateRow 6 21, 7094638365441497750880⟩, ⟨.privateRow 6 22, 21172777858502679509100⟩, ⟨.privateRow 7 19, 2309268834256734550200⟩, ⟨.privateRow 7 20, 7148064883396655378160⟩, ⟨.privateRow 7 21, 14559986202166188283500⟩, ⟨.privateRow 8 17, 728166082674068438400⟩, ⟨.privateRow 8 18, 2484590038201332461400⟩, ⟨.privateRow 8 19, 5185574274912863111280⟩, ⟨.privateRow 8 20, 8800180628831852960700⟩, ⟨.privateRow 9 13, 103769596472281740⟩, ⟨.privateRow 9 15, 226088008313983841025⟩, ⟨.privateRow 9 16, 857581593703071237000⟩, ⟨.privateRow 9 17, 1915586750878320920400⟩, ⟨.privateRow 9 18, 3327890958866075401800⟩, ⟨.privateRow 9 19, 4810758492454981466400⟩, ⟨.privateRow 18 0, 360016967352814200⟩, ⟨.hall 11 19, 490667124805150473180⟩, ⟨.hall 10 20, 4173909654676520959200⟩, ⟨.hall 9 21, 12038310886749404657400⟩, ⟨.hall 8 22, 24570474818275155369600⟩, ⟨.hall 7 23, 58166231334599264426550⟩, ⟨.hall 6 24, 117614951111999458877760⟩, ⟨.hall 5 25, 212674567821938949850200⟩, ⟨.hall 4 26, 347859274369080187313600⟩, ⟨.hall 3 27, 469509467659276611867300⟩, ⟨.hall 2 28, 611776733307611693421600⟩, ⟨.mean 5, 2833839783730018103040⟩, ⟨.mean 6, 68578980111805363200⟩, ⟨.unionRow 5, 328070687553003835440⟩, ⟨.tail 2 26, 2411254680779751325318800⟩, ⟨.tail 3 0, 4629448102714751919002400⟩, ⟨.tail 3 15, 2011054779632820121200⟩, ⟨.tail 3 21, 355956695995009161452400⟩, ⟨.tail 3 24, 255403957013368155392400⟩, ⟨.tail 3 25, 30165821694492301818000⟩, ⟨.tail 3 28, 176972820607688170665600⟩, ⟨.tail 4 0, 661349728959250274143200⟩, ⟨.tail 4 27, 154563924491779603600800⟩, ⟨.tail 5 0, 22293978699929548772160⟩, ⟨.tail 5 1, 5516035966992878046720⟩, ⟨.tail 5 12, 47403434091345045714000⟩, ⟨.tail 5 17, 21144804540139365845760⟩, ⟨.tail 5 20, 10400026146101155483920⟩, ⟨.tail 5 25, 62802367832533496927760⟩, ⟨.tail 5 26, 155081052863685185917680⟩, ⟨.tail 6 0, 6698475694566461005200⟩, ⟨.tail 6 13, 11189327345325465336000⟩, ⟨.tail 6 24, 34883484034683579094800⟩, ⟨.tail 6 25, 93808901149188090465600⟩, ⟨.tail 7 0, 992926795959061563600⟩, ⟨.tail 7 6, 1204616772762516313200⟩, ⟨.tail 7 14, 1491910312710062044800⟩, ⟨.tail 7 19, 65523088058212184400⟩, ⟨.tail 7 23, 19102500287740321452000⟩, ⟨.tail 7 24, 47126221026483378780000⟩, ⟨.tail 8 0, 408852210100790055600⟩, ⟨.tail 8 3, 8301567717782539200⟩, ⟨.tail 8 11, 431681521324692038400⟩, ⟨.tail 8 17, 20753919294456348000⟩, ⟨.tail 8 22, 9330962114787574060800⟩, ⟨.tail 8 23, 20232995920165493665200⟩, ⟨.tail 9 0, 204426105050395027800⟩, ⟨.tail 9 9, 11414655611950991400⟩, ⟨.tail 9 21, 3869568252451386084600⟩, ⟨.tail 9 22, 6501165218988451011000⟩, ⟨.tail 10 1, 24282085574513927160⟩, ⟨.tail 10 2, 6848793367170594840⟩, ⟨.tail 10 9, 28640408626349760240⟩, ⟨.tail 10 14, 69110551250539638840⟩, ⟨.tail 10 15, 362986048460041526520⟩, ⟨.tail 10 16, 1086467675064789817800⟩, ⟨.tail 10 17, 1474981044257012652360⟩, ⟨.tail 10 18, 5292872037665202430440⟩, ⟨.tail 10 19, 6750419789714871750480⟩, ⟨.tail 10 20, 7943977688339056323960⟩, ⟨.tail 10 21, 6998221586090680545600⟩, ⟨.tail 11 1, 17789073680962584000⟩, ⟨.tail 11 12, 20012707891082907000⟩, ⟨.tail 11 13, 83163919458500080200⟩, ⟨.tail 11 14, 256162661005861209600⟩, ⟨.tail 11 15, 657306272511567478800⟩, ⟨.tail 11 16, 1332401618704097541600⟩, ⟨.tail 11 17, 1965692641746365532000⟩, ⟨.tail 11 18, 4353431056573568369400⟩, ⟨.tail 11 19, 4534434881277362661600⟩, ⟨.tail 11 20, 2755972240023128326200⟩, ⟨.tail 12 1, 2257843967199097200⟩, ⟨.tail 12 4, 1881536639332581000⟩, ⟨.tail 12 7, 1505229311466064800⟩, ⟨.tail 12 11, 32738737524386909400⟩, ⟨.tail 12 12, 84669148769966145000⟩, ⟨.tail 12 13, 199819191097120102200⟩, ⟨.tail 12 14, 419958977899032079200⟩, ⟨.tail 12 15, 344321204997862323000⟩, ⟨.tail 12 16, 1755473684497298073000⟩, ⟨.tail 12 17, 1663654696497868120200⟩, ⟨.tail 12 18, 2791447758113817171600⟩, ⟨.tail 12 19, 1314817803565607602800⟩, ⟨.tail 13 0, 376307327866516200⟩, ⟨.tail 13 1, 1881536639332581000⟩, ⟨.tail 13 9, 9407683196662905000⟩, ⟨.tail 13 10, 24459976311323553000⟩, ⟨.tail 13 11, 77143002212635821000⟩, ⟨.tail 13 12, 152028160458072544800⟩, ⟨.tail 13 13, 279220037276955020400⟩, ⟨.tail 13 14, 440279573603823954000⟩, ⟨.tail 13 15, 377812557177982264800⟩, ⟨.tail 13 16, 1420560162696098655000⟩, ⟨.tail 13 17, 973883364518543925600⟩, ⟨.tail 14 0, 444726842024064600⟩, ⟨.tail 14 1, 889453684048129200⟩, ⟨.tail 14 7, 2668361052144387600⟩, ⟨.tail 14 8, 8894536840481292000⟩, ⟨.tail 14 9, 27128337363467940600⟩, ⟨.tail 14 10, 53811947884911816600⟩, ⟨.tail 14 11, 116963159452328989800⟩, ⟨.tail 14 12, 194790356806540294800⟩, ⟨.tail 14 13, 306861520996604574000⟩, ⟨.tail 14 14, 394027982033321235600⟩, ⟨.tail 14 15, 275730642054920052000⟩, ⟨.tail 15 1, 622617578833690440⟩, ⟨.tail 15 6, 4358323051835833080⟩, ⟨.tail 15 7, 9961881261339047040⟩, ⟨.tail 15 8, 21791615259179165400⟩, ⟨.tail 15 9, 46696318412526783000⟩, ⟨.tail 15 10, 80317667669546066760⟩, ⟨.tail 15 11, 72846256723541781480⟩, ⟨.tail 15 15, 84675990721381899840⟩, ⟨.tail 15 16, 122655663030237016680⟩, ⟨.tail 16 4, 1037695964722817400⟩, ⟨.tail 16 5, 3113087894168452200⟩, ⟨.tail 16 6, 10376959647228174000⟩, ⟨.tail 16 7, 19716223329733530600⟩, ⟨.tail 16 9, 85091069107271026800⟩, ⟨.tail 17 3, 2075391929445634800⟩, ⟨.tail 17 4, 4150783858891269600⟩, ⟨.tail 17 5, 8301567717782539200⟩, ⟨.tail 17 10, 12452351576673808800⟩, ⟨.assumptionRow 18, 5251019167294992000⟩]
  caps := #[0, 68158534281200879705280, 25927592538023693375040, 0, 0, 436743320726161611540, 118992077210472309900, 9430245710844117096, 0, 11139643419866869320, 0, 11772636606183476520, 4648105577983259448, 3064427544534794928, 0, 0, 24352782334312723200, 5251019167294992000, 0, 6258469490910000000, 0, 0, 0, 0, 0] }

theorem case_55_31_18_checked :
    (Witness.linear .conditional case_55_31_18).check 55 31 18 = true := by
  change case_55_31_18.check 55 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_31_19 : Certificate := {
  objectiveScale := 27733860000000
  eta := 141225505526980274400
  rows := #[⟨.count 2, 34987779055904875200⟩, ⟨.count 3, 8704816191964292400⟩, ⟨.count 4, 2217768398056411200⟩, ⟨.count 5, 577010977377634800⟩, ⟨.count 6, 150855130982556000⟩, ⟨.count 7, 39541729870843200⟩, ⟨.count 8, 11042989980422400⟩, ⟨.count 9, 3154751812812600⟩, ⟨.count 10, 929306735557200⟩, ⟨.count 11, 269009844503400⟩, ⟨.count 12, 118246085496000⟩, ⟨.count 13, 51239970381600⟩, ⟨.count 14, 32607253879200⟩, ⟨.count 15, 24455440409400⟩, ⟨.path 12, 8036460157446⟩, ⟨.privateRow 2 29, 3128046471885535200⟩, ⟨.privateRow 5 22, 1083306137449536⟩, ⟨.privateRow 5 23, 101033343235744920⟩, ⟨.privateRow 6 20, 818286799730400⟩, ⟨.privateRow 6 21, 30171026196511200⟩, ⟨.privateRow 6 22, 96838303569707700⟩, ⟨.privateRow 7 18, 233796228494400⟩, ⟨.privateRow 7 19, 8996755405638000⟩, ⟨.privateRow 7 20, 31042105692998400⟩, ⟨.privateRow 7 21, 69630267478671900⟩, ⟨.privateRow 7 22, 93284695169265600⟩, ⟨.privateRow 8 17, 2621002121337600⟩, ⟨.privateRow 8 18, 9969667873565400⟩, ⟨.privateRow 8 19, 23792426247189600⟩, ⟨.privateRow 8 20, 45152894809222200⟩, ⟨.privateRow 8 21, 66788713515123600⟩, ⟨.privateRow 9 15, 676260859098825⟩, ⟨.privateRow 9 16, 3182700887566200⟩, ⟨.privateRow 9 17, 8245559324702700⟩, ⟨.privateRow 9 18, 16417752328177200⟩, ⟨.privateRow 9 19, 27310613077197450⟩, ⟨.privateRow 9 20, 37131510354939000⟩, ⟨.privateRow 10 13, 161949360933360⟩, ⟨.privateRow 10 14, 969250621559220⟩, ⟨.privateRow 10 15, 2886207786221760⟩, ⟨.privateRow 10 16, 6146467356229200⟩, ⟨.privateRow 10 17, 10681158153209544⟩, ⟨.privateRow 10 18, 15562627095195180⟩, ⟨.privateRow 10 19, 17625851084401560⟩, ⟨.privateRow 11 11, 29346528491280⟩, ⟨.privateRow 11 12, 284537108255400⟩, ⟨.privateRow 11 13, 995831356194675⟩, ⟨.privateRow 11 14, 2361696816679200⟩, ⟨.privateRow 11 15, 4369372019812800⟩, ⟨.privateRow 11 16, 6710339939383080⟩, ⟨.privateRow 11 17, 8454595112964000⟩, ⟨.privateRow 11 18, 7531111101313800⟩, ⟨.privateRow 12 10, 74987725885380⟩, ⟨.privateRow 12 11, 339081598871400⟩, ⟨.privateRow 12 12, 916283989588275⟩, ⟨.privateRow 12 13, 1863501999757200⟩, ⟨.privateRow 12 14, 3071770532107200⟩, ⟨.privateRow 12 15, 4200495110436240⟩, ⟨.privateRow 12 16, 1862622192573450⟩, ⟨.privateRow 13 8, 10122581561400⟩, ⟨.privateRow 13 9, 109180552274640⟩, ⟨.privateRow 13 10, 357584921509200⟩, ⟨.privateRow 13 11, 818607796048350⟩, ⟨.privateRow 13 12, 1486099910215800⟩, ⟨.privateRow 13 13, 1687798639781100⟩, ⟨.privateRow 14 7, 25725852898200⟩, ⟨.privateRow 14 8, 135436558076820⟩, ⟨.privateRow 14 9, 367478575464000⟩, ⟨.privateRow 14 10, 751859224491375⟩, ⟨.privateRow 14 11, 287642561005800⟩, ⟨.privateRow 15 5, 3396588945750⟩, ⟨.privateRow 15 6, 42241215252600⟩, ⟨.privateRow 15 7, 162221088049020⟩, ⟨.privateRow 15 8, 302885158255680⟩, ⟨.privateRow 16 4, 10189766837250⟩, ⟨.privateRow 16 5, 62003187300600⟩, ⟨.privateRow 16 6, 80159499119700⟩, ⟨.privateRow 17 2, 1672166865600⟩, ⟨.privateRow 17 3, 20832412200600⟩, ⟨.privateRow 17 4, 16797676240800⟩, ⟨.privateRow 18 1, 7106709178800⟩, ⟨.privateRow 18 2, 1099847849100⟩, ⟨.hall 9 19, 26519860703700⟩, ⟨.hall 9 20, 2162242055937600⟩, ⟨.hall 10 20, 6155783714480400⟩, ⟨.hall 8 22, 144583399113753600⟩, ⟨.hall 7 23, 332682527319692550⟩, ⟨.hall 6 24, 709175909927380896⟩, ⟨.hall 5 25, 1604039592462337800⟩, ⟨.hall 4 26, 2602052303604353600⟩, ⟨.hall 3 27, 3721043737749838500⟩, ⟨.hall 2 28, 3795203254522680000⟩, ⟨.assumptionRow 19, 15459307390800⟩]
  caps := #[0, 243562294208961000, 11158782058848060, 0, 616388259409650, 219914765676144, 191391748174062, 7179728639328, 21147286996710, 17712505419840, 0, 10335302478270, 4839502477446, 7523983471680, 14825209170135, 0, 69838189744050, 15734242389600, 15459307390800, 289613152609200, 27733860000000, 0, 0, 0, 0] }

theorem case_55_31_19_checked :
    (Witness.linear .conditional case_55_31_19).check 55 31 19 = true := by
  change case_55_31_19.check 55 31 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_31_20 : Certificate := {
  objectiveScale := 2056019588387765000000
  eta := 13321856944086309716462164800
  rows := #[⟨.count 2, 3033963279191499107268816000⟩, ⟨.count 3, 703327851085302065775952800⟩, ⟨.count 4, 170503721475224743218412800⟩, ⟨.count 5, 42088628725501906151604000⟩, ⟨.count 6, 11255055475531752731246400⟩, ⟨.count 7, 3189246596221309051428000⟩, ⟨.count 8, 957420884869683041808000⟩, ⟨.count 9, 296929855510259808236400⟩, ⟨.count 10, 93154464473806998662400⟩, ⟨.count 11, 36596396757567035188800⟩, ⟨.count 12, 12667983493003973719200⟩, ⟨.count 13, 4574549594695879398600⟩, ⟨.count 14, 1940718009870979138800⟩, ⟨.path 9, 1652930211491898736320⟩, ⟨.path 10, 785415941869240281600⟩, ⟨.path 15, 168472018055619034848⟩, ⟨.path 16, 75480217307148285450⟩, ⟨.privateRow 2 29, 289605585741006732966568800⟩, ⟨.privateRow 5 22, 114624350571579659306496⟩, ⟨.privateRow 5 23, 8296832875356918308395980⟩, ⟨.privateRow 6 21, 2364127230538830473196480⟩, ⟨.privateRow 6 22, 8138470285751446410669900⟩, ⟨.privateRow 7 19, 618211101287234045190600⟩, ⟨.privateRow 7 20, 2515577167423428597609120⟩, ⟨.privateRow 7 21, 6078813986418374407506300⟩, ⟨.privateRow 7 22, 8829866479291870593781200⟩, ⟨.privateRow 8 17, 151930495629899509723200⟩, ⟨.privateRow 8 18, 756664388515251755338800⟩, ⟨.privateRow 8 19, 2017311680660553782144640⟩, ⟨.privateRow 8 20, 4131788643015314586505200⟩, ⟨.privateRow 8 21, 6622376755683071147965200⟩, ⟨.privateRow 9 15, 33032637793012290758325⟩, ⟨.privateRow 9 16, 221703928841927569237200⟩, ⟨.privateRow 9 17, 667714813062831878143800⟩, ⟨.privateRow 9 18, 1462913235840744074827440⟩, ⟨.privateRow 9 19, 2640832031931934863122100⟩, ⟨.privateRow 9 20, 3924239633626334873050200⟩, ⟨.privateRow 10 13, 5369319827309708950680⟩, ⟨.privateRow 10 14, 61908904514884234527720⟩, ⟨.privateRow 10 15, 219328859658418799529240⟩, ⟨.privateRow 10 16, 525837544774541797657860⟩, ⟨.privateRow 10 17, 1004670899350008480573984⟩, ⟨.privateRow 10 18, 1605361937765273943615360⟩, ⟨.privateRow 10 19, 2077991463769186396551120⟩, ⟨.privateRow 11 12, 15833794556725131386400⟩, ⟨.privateRow 11 13, 70454994894066081949650⟩, ⟨.privateRow 11 14, 190804265562315142881000⟩, ⟨.privateRow 11 15, 393919548432145170435000⟩, ⟨.privateRow 11 16, 668660528029546783851120⟩, ⟨.privateRow 11 17, 939168894062563118955000⟩, ⟨.privateRow 11 18, 997621472217010466826000⟩, ⟨.privateRow 12 10, 2756459371162901688900⟩, ⟨.privateRow 12 11, 21543391681003671355800⟩, ⟨.privateRow 12 12, 68999456386662847595550⟩, ⟨.privateRow 12 13, 158416820030237523202800⟩, ⟨.privateRow 12 14, 291011731908730174049400⟩, ⟨.privateRow 12 15, 442933696910014866281880⟩, ⟨.privateRow 12 16, 542142775043188578982800⟩, ⟨.privateRow 12 17, 150099964906303256506200⟩, ⟨.privateRow 13 8, 458521288046440126200⟩, ⟨.privateRow 13 9, 5442541056253559079360⟩, ⟨.privateRow 13 10, 24267268790096089573200⟩, ⟨.privateRow 13 11, 64586188989215861380875⟩, ⟨.privateRow 13 12, 131773838874316467364800⟩, ⟨.privateRow 13 13, 220340805477851524365900⟩, ⟨.privateRow 13 14, 194078198958559026998040⟩, ⟨.privateRow 14 7, 1323216824912031231000⟩, ⟨.privateRow 14 8, 7541075695498661796480⟩, ⟨.privateRow 14 9, 25999460322715974494400⟩, ⟨.privateRow 14 10, 61357879222795867236525⟩, ⟨.privateRow 14 11, 115116263177346956467800⟩, ⟨.privateRow 14 12, 30058025367168379280700⟩, ⟨.privateRow 15 5, 145553850740323435410⟩, ⟨.privateRow 15 6, 2275932938848693717320⟩, ⟨.privateRow 15 7, 9645368509058766319836⟩, ⟨.privateRow 15 8, 28528554745103393340360⟩, ⟨.privateRow 15 9, 46528714286656724852730⟩, ⟨.privateRow 16 4, 431270668860217586400⟩, ⟨.privateRow 16 5, 3499173381434038144200⟩, ⟨.privateRow 16 6, 12614667064161364402200⟩, ⟨.privateRow 16 7, 13009998510616563856400⟩, ⟨.privateRow 17 3, 862541337720435172800⟩, ⟨.privateRow 17 4, 5469296209636395754800⟩, ⟨.privateRow 17 5, 2652314613490338156360⟩, ⟨.privateRow 18 2, 1832900342655924742200⟩, ⟨.privateRow 18 3, 571293613295353166400⟩, ⟨.privateRow 19 1, 392764359140555301900⟩, ⟨.hall 10 20, 1797936613430471387874000⟩, ⟨.hall 9 21, 6853733866314356964087600⟩, ⟨.hall 8 22, 16791204726795588087398400⟩, ⟨.hall 7 23, 35344733757605524766213700⟩, ⟨.hall 5 24, 6051945278735999127422784⟩, ⟨.hall 6 24, 70575419219032876020897024⟩, ⟨.hall 4 26, 238004727922932764810016000⟩, ⟨.hall 3 27, 336015015181413887994374700⟩, ⟨.hall 2 28, 346195182954766669293369600⟩]
  caps := #[0, 0, 3780706611037887148647120, 589171713521223610181040, 362679893755214218779960, 0, 41621730092449437076300, 4880294422345624643900, 8711026241608750905076, 0, 2161243648573426062828, 0, 2255723408769206101342, 0, 0, 3816000595610246111432, 75480217307148285450, 1773840993068614520960, 0, 28544542353422696601000, 20560195883877650000000, 2056019588387765000000, 0, 0, 0] }

theorem case_55_31_20_checked :
    (Witness.linear .conditional case_55_31_20).check 55 31 20 = true := by
  change case_55_31_20.check 55 31 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_32_1_checked :
    (Witness.rising).check 55 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_32_2_checked :
    (Witness.rising).check 55 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_32_3_checked :
    (Witness.rising).check 55 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_32_4_checked :
    (Witness.rising).check 55 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_32_5_checked :
    (Witness.rising).check 55 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_32_6_checked :
    (Witness.rising).check 55 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_32_7_checked :
    (Witness.rising).check 55 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_32_8_checked :
    (Witness.rising).check 55 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_32_9_checked :
    (Witness.rising).check 55 32 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_32_10_checked :
    (Witness.rising).check 55 32 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_32_11_checked :
    (Witness.linear .positive case_55_32_11).check 55 32 11 = true := by
  change case_55_32_11.check 55 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_32_12_checked :
    (Witness.linear .positive case_55_32_12).check 55 32 12 = true := by
  change case_55_32_12.check 55 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_32_13_checked :
    (Witness.linear .positive case_55_32_13).check 55 32 13 = true := by
  change case_55_32_13.check 55 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_32_14 : Certificate := {
  objectiveScale := 25040014272000000
  eta := 355860469070462420064000
  rows := #[⟨.count 2, 68949095454739163664000⟩, ⟨.count 3, 13955059387113468624000⟩, ⟨.count 4, 2832321951464102697600⟩, ⟨.count 5, 565975192047593328000⟩, ⟨.count 6, 122526041975889552000⟩, ⟨.count 7, 26205145652557872000⟩, ⟨.count 8, 5781918257859744000⟩, ⟨.count 9, 1370874167589326400⟩, ⟨.count 10, 339721003630008000⟩, ⟨.count 11, 101455141355568000⟩, ⟨.count 12, 33818380451856000⟩, ⟨.count 13, 19983588448824000⟩, ⟨.path 14, 9630837573477120⟩, ⟨.privateRow 3 29, 1613674767242538000000⟩, ⟨.privateRow 5 25, 322281992110334256000⟩, ⟨.privateRow 6 23, 127716223975792452000⟩, ⟨.privateRow 7 18, 1502099731736604000⟩, ⟨.privateRow 7 19, 4206069568752480000⟩, ⟨.privateRow 7 20, 7464980484994032000⟩, ⟨.privateRow 7 21, 12296568092176368000⟩, ⟨.privateRow 7 22, 49262876124425964000⟩, ⟨.privateRow 8 15, 120650915259774900⟩, ⟨.privateRow 8 16, 943576937914611000⟩, ⟨.privateRow 8 17, 1997005789414510875⟩, ⟨.privateRow 8 18, 3549584898222363000⟩, ⟨.privateRow 8 19, 6262773354909571500⟩, ⟨.privateRow 8 20, 8975961811596780000⟩, ⟨.privateRow 8 21, 20433427351302215250⟩, ⟨.privateRow 9 13, 152601948154656000⟩, ⟨.privateRow 9 14, 414992520120578400⟩, ⟨.privateRow 9 15, 868323924746678400⟩, ⟨.privateRow 9 16, 1441593866710998000⟩, ⟨.privateRow 9 17, 2591205302197512000⟩, ⟨.privateRow 9 19, 12820315741432879680⟩, ⟨.privateRow 9 20, 5195177897015106000⟩, ⟨.privateRow 9 22, 18346710514993660800⟩, ⟨.privateRow 10 10, 16448030492493600⟩, ⟨.privateRow 10 11, 84264131292541200⟩, ⟨.privateRow 10 12, 197110849699764000⟩, ⟨.privateRow 10 13, 363901145653085040⟩, ⟨.privateRow 10 14, 609499447689132000⟩, ⟨.privateRow 10 15, 1061628136343775000⟩, ⟨.privateRow 10 16, 1608678870130332000⟩, ⟨.privateRow 10 17, 586851380780464800⟩, ⟨.privateRow 10 18, 809335332177372000⟩, ⟨.privateRow 11 8, 18556189273908000⟩, ⟨.privateRow 11 9, 42568590778560000⟩, ⟨.privateRow 11 10, 94537745354052000⟩, ⟨.privateRow 11 11, 168113684642904000⟩, ⟨.privateRow 11 12, 267933805125386400⟩, ⟨.privateRow 11 13, 477044124252696000⟩, ⟨.privateRow 11 14, 720754233380181000⟩, ⟨.privateRow 11 15, 1028825405304840000⟩, ⟨.privateRow 11 16, 613854845171568000⟩, ⟨.privateRow 11 17, 558003277455624000⟩, ⟨.privateRow 12 6, 15312211149034800⟩, ⟨.privateRow 12 7, 23149486618830000⟩, ⟨.privateRow 12 8, 47475803326644000⟩, ⟨.privateRow 12 9, 85250500722387000⟩, ⟨.privateRow 12 10, 135657821585286000⟩, ⟨.privateRow 12 11, 234051374710553400⟩, ⟨.privateRow 12 12, 369810252904092000⟩, ⟨.privateRow 12 13, 200092084340148000⟩, ⟨.privateRow 12 14, 1401651089799246000⟩, ⟨.privateRow 12 15, 246592357461450000⟩, ⟨.privateRow 12 16, 454293577403265600⟩, ⟨.privateRow 13 4, 11336843446929000⟩, ⟨.privateRow 13 5, 15064551292190400⟩, ⟨.privateRow 13 7, 101691633526560000⟩, ⟨.privateRow 13 8, 52008569937324000⟩, ⟨.privateRow 13 9, 136950466292640000⟩, ⟨.privateRow 13 11, 753739964313336000⟩, ⟨.privateRow 13 13, 948012652017288000⟩, ⟨.privateRow 13 14, 645623626808160000⟩, ⟨.privateRow 14 0, 1577651719644000⟩, ⟨.privateRow 14 3, 22731331860537300⟩, ⟨.privateRow 14 4, 8926002840474720⟩, ⟨.privateRow 14 5, 10134534141903600⟩, ⟨.privateRow 14 6, 111908095313414400⟩, ⟨.privateRow 14 7, 62448713902575000⟩, ⟨.privateRow 14 8, 150785258295672000⟩, ⟨.privateRow 14 9, 13788676029688560⟩, ⟨.privateRow 14 10, 84153111356714400⟩, ⟨.privateRow 14 11, 1414338472465518600⟩, ⟨.privateRow 14 12, 69371599900917600⟩, ⟨.privateRow 14 13, 861292662144314400⟩, ⟨.privateRow 15 0, 7253302474017600⟩, ⟨.privateRow 15 1, 2559989108476800⟩, ⟨.privateRow 15 3, 59684317500487680⟩, ⟨.privateRow 15 5, 154710550572177600⟩, ⟨.privateRow 15 6, 83153931934273200⟩, ⟨.privateRow 15 7, 191035031393606400⟩, ⟨.privateRow 15 8, 48804363789461280⟩, ⟨.privateRow 15 9, 88766606467739200⟩, ⟨.privateRow 15 10, 1294714491612141600⟩, ⟨.privateRow 15 11, 839754794593915200⟩, ⟨.privateRow 15 16, 7131032518027017600⟩, ⟨.privateRow 16 0, 29485588838706000⟩, ⟨.privateRow 16 3, 184015543632921000⟩, ⟨.privateRow 16 5, 462883744937864250⟩, ⟨.privateRow 16 7, 381186949661317800⟩, ⟨.privateRow 16 9, 1350037113383833875⟩, ⟨.privateRow 16 10, 317239466625081000⟩, ⟨.privateRow 16 13, 1244394705698644500⟩, ⟨.privateRow 16 16, 24462410209916679000⟩, ⟨.privateRow 17 0, 99085292725419000⟩, ⟨.privateRow 17 2, 333059807480400000⟩, ⟨.privateRow 17 3, 26644784598432000⟩, ⟨.privateRow 17 4, 793792541161620000⟩, ⟨.privateRow 17 5, 198624757915584000⟩, ⟨.privateRow 17 7, 1360364280331056000⟩, ⟨.privateRow 17 8, 997514123403798000⟩, ⟨.privateRow 17 9, 1657686241802448000⟩, ⟨.privateRow 17 11, 498257471990678400⟩, ⟨.privateRow 18 1, 1385845998935112000⟩, ⟨.privateRow 18 4, 1650563664101352000⟩, ⟨.privateRow 18 6, 5787839321103840000⟩, ⟨.privateRow 18 10, 10531351112530248000⟩, ⟨.privateRow 19 0, 3882525755771520000⟩, ⟨.privateRow 19 1, 836236316627712000⟩, ⟨.privateRow 19 3, 3631926366080812800⟩, ⟨.privateRow 19 4, 1983970661199246720⟩, ⟨.privateRow 19 6, 798344358530518800⟩, ⟨.privateRow 19 8, 1653308884332705600⟩, ⟨.privateRow 19 9, 63296817396343090560⟩, ⟨.privateRow 20 0, 27258690683573949600⟩, ⟨.privateRow 20 3, 15684918737597469360⟩, ⟨.privateRow 20 8, 80941926324885706080⟩, ⟨.privateRow 20 12, 773272948462624209600⟩, ⟨.privateRow 21 0, 233086355268366600000⟩, ⟨.privateRow 21 6, 15060964494263688000⟩, ⟨.privateRow 22 0, 1491035484932105112000⟩, ⟨.privateRow 22 1, 1491035484932105112000⟩, ⟨.privateRow 22 5, 120487715954109504000⟩, ⟨.privateRow 23 0, 62623490367148414704000⟩, ⟨.hall 19 2, 504790568214332400⟩, ⟨.hall 19 3, 241486993139792400⟩, ⟨.hall 20 4, 6876319142835542400⟩, ⟨.hall 19 5, 25578061578669600⟩, ⟨.hall 21 7, 59559268681860948000⟩, ⟨.hall 22 7, 1416483710685499856400⟩, ⟨.hall 16 9, 1185506587465200⟩, ⟨.hall 17 13, 218931313450449600⟩, ⟨.hall 13 15, 7795455555888000⟩, ⟨.hall 12 16, 5002956488930400⟩, ⟨.hall 14 16, 79633946910117600⟩, ⟨.hall 15 16, 696682750235472000⟩, ⟨.hall 10 18, 413194498002000⟩, ⟨.hall 12 19, 2959953749048696400⟩, ⟨.hall 11 20, 10623802659090192000⟩, ⟨.hall 10 21, 18502986213752040000⟩, ⟨.hall 8 22, 2111792257575000⟩, ⟨.hall 9 22, 38704387878016660800⟩, ⟨.hall 7 23, 194440315607057520⟩, ⟨.hall 4 24, 247059714791301984⟩, ⟨.hall 6 25, 294546820942181808000⟩, ⟨.hall 5 26, 561420414147072480000⟩, ⟨.hall 3 28, 1625248710400691376000⟩]
  caps := #[0, 0, 17059048083106848000, 0, 3501149754025123200, 325707559366606560, 72618242274264960, 69397291253656080, 2432895538993920, 4416301502907840, 0, 0, 24137087709885600, 17521712606349360, 0, 0, 148842223890735375, 0, 1418265742619668800, 39074137413854400, 1633535379762446160, 53071970122643472000, 0, 0] }

theorem case_55_32_14_checked :
    (Witness.linear .positive case_55_32_14).check 55 32 14 = true := by
  change case_55_32_14.check 55 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_32_15 : Certificate := {
  objectiveScale := 263579097600000
  eta := 3451973062085237289600
  rows := #[⟨.count 2, 782074810829401689600⟩, ⟨.count 3, 169699906431469814400⟩, ⟨.count 4, 40230378924417601920⟩, ⟨.count 5, 9302178753941673600⟩, ⟨.count 6, 2137153950108777600⟩, ⟨.count 7, 527324509734422400⟩, ⟨.count 8, 128016078729739200⟩, ⟨.count 9, 32555082272993280⟩, ⟨.count 10, 8720111323123200⟩, ⟨.count 11, 2459518578316800⟩, ⟨.count 12, 922319466868800⟩, ⟨.count 13, 363337971796800⟩, ⟨.count 14, 508673160515520⟩, ⟨.path 15, 70287320061504⟩, ⟨.privateRow 2 30, 15608635930418731200⟩, ⟨.privateRow 3 29, 54688904838910742400⟩, ⟨.privateRow 6 21, 176609168217081600⟩, ⟨.privateRow 6 22, 482472455660395200⟩, ⟨.privateRow 7 19, 92218637603664000⟩, ⟨.privateRow 7 23, 1615077655522531200⟩, ⟨.privateRow 8 16, 6275990614693800⟩, ⟨.privateRow 8 17, 30454156146489075⟩, ⟨.privateRow 8 18, 75649993544525400⟩, ⟨.privateRow 8 19, 78950313455013000⟩, ⟨.privateRow 8 22, 1108412946573332400⟩, ⟨.privateRow 9 14, 4351981484410560⟩, ⟨.privateRow 9 15, 12333754163610880⟩, ⟨.privateRow 9 16, 26903158267265280⟩, ⟨.privateRow 9 17, 59708540031940800⟩, ⟨.privateRow 9 18, 70309934631256320⟩, ⟨.privateRow 9 19, 66760526355659136⟩, ⟨.privateRow 10 11, 166529903740200⟩, ⟨.privateRow 10 12, 2071026439241760⟩, ⟨.privateRow 10 13, 5439169437798096⟩, ⟨.privateRow 10 14, 10653876750797280⟩, ⟨.privateRow 10 15, 22340743540855740⟩, ⟨.privateRow 10 16, 40133274256183680⟩, ⟨.privateRow 10 17, 48984014231071920⟩, ⟨.privateRow 10 18, 53919355014645120⟩, ⟨.privateRow 10 19, 40766520435600960⟩, ⟨.privateRow 11 9, 208543096238400⟩, ⟨.privateRow 11 10, 915332198180400⟩, ⟨.privateRow 11 11, 2406161253787200⟩, ⟨.privateRow 11 12, 4684264928703360⟩, ⟨.privateRow 11 13, 9307041892948800⟩, ⟨.privateRow 11 14, 16416587783395800⟩, ⟨.privateRow 11 15, 26894995362892800⟩, ⟨.privateRow 11 16, 33417777047054400⟩, ⟨.privateRow 11 17, 37938074070536640⟩, ⟨.privateRow 11 20, 101804504789988000⟩, ⟨.privateRow 12 7, 155549910087000⟩, ⟨.privateRow 12 8, 459188965342800⟩, ⟨.privateRow 12 9, 1084579373077200⟩, ⟨.privateRow 12 10, 2187015099469200⟩, ⟨.privateRow 12 11, 4409199451336680⟩, ⟨.privateRow 12 12, 7620522261752400⟩, ⟨.privateRow 12 13, 12489742780515000⟩, ⟨.privateRow 12 14, 19255248869828400⟩, ⟨.privateRow 12 15, 24104136067011000⟩, ⟨.privateRow 12 16, 26844620482920240⟩, ⟨.privateRow 12 18, 20180008335286800⟩, ⟨.privateRow 13 5, 108069755713920⟩, ⟨.privateRow 13 6, 249545310300000⟩, ⟨.privateRow 13 7, 554681637417600⟩, ⟨.privateRow 13 8, 1085355736264800⟩, ⟨.privateRow 13 9, 2301987429705600⟩, ⟨.privateRow 13 10, 4142052878483520⟩, ⟨.privateRow 13 12, 24207392370961800⟩, ⟨.privateRow 13 13, 9039529320307200⟩, ⟨.privateRow 13 14, 20267737375485600⟩, ⟨.privateRow 13 16, 50294360019103200⟩, ⟨.privateRow 14 3, 77209319006820⟩, ⟨.privateRow 14 4, 155024201299968⟩, ⟨.privateRow 14 5, 324408903390000⟩, ⟨.privateRow 14 6, 628854181956000⟩, ⟨.privateRow 14 7, 1323155780626680⟩, ⟨.privateRow 14 8, 2553275019990240⟩, ⟨.privateRow 14 9, 4392756079023312⟩, ⟨.privateRow 14 10, 847788600859200⟩, ⟨.privateRow 14 11, 19388622520006740⟩, ⟨.privateRow 14 13, 47246047599310560⟩, ⟨.privateRow 14 17, 140975133057158400⟩, ⟨.privateRow 15 0, 21979704466720⟩, ⟨.privateRow 15 2, 169557720171840⟩, ⟨.privateRow 15 3, 199701314869056⟩, ⟨.privateRow 15 4, 431968477580640⟩, ⟨.privateRow 15 6, 3584261806965840⟩, ⟨.privateRow 15 7, 2358393744208320⟩, ⟨.privateRow 15 8, 5448454741521792⟩, ⟨.privateRow 15 9, 2311008926786560⟩, ⟨.privateRow 15 10, 17598678372835560⟩, ⟨.privateRow 15 11, 10657913839372800⟩, ⟨.privateRow 15 12, 30868924944617760⟩, ⟨.privateRow 15 15, 21062836794679680⟩, ⟨.privateRow 16 0, 149609753092800⟩, ⟨.privateRow 16 2, 734750120744640⟩, ⟨.privateRow 16 3, 552576498774300⟩, ⟨.privateRow 16 5, 5378158936700550⟩, ⟨.privateRow 16 7, 5288081397859260⟩, ⟨.privateRow 16 9, 53463668641683300⟩, ⟨.privateRow 16 11, 32745834708186600⟩, ⟨.privateRow 16 15, 285863718852211500⟩, ⟨.privateRow 17 0, 696397779277200⟩, ⟨.privateRow 17 1, 1130384801145600⟩, ⟨.privateRow 17 2, 1020806682667200⟩, ⟨.privateRow 17 4, 9144005623552800⟩, ⟨.privateRow 17 5, 2224068797059200⟩, ⟨.privateRow 17 6, 7460539687560960⟩, ⟨.privateRow 17 7, 3687207565641600⟩, ⟨.privateRow 17 8, 61010501097546000⟩, ⟨.privateRow 17 12, 236533019639716800⟩, ⟨.privateRow 17 15, 499226373248803200⟩, ⟨.privateRow 18 0, 6542774884726080⟩, ⟨.privateRow 18 1, 931414007066400⟩, ⟨.privateRow 18 3, 17901123591951600⟩, ⟨.privateRow 18 4, 8984357120793600⟩, ⟨.privateRow 18 6, 36679192535585600⟩, ⟨.privateRow 18 7, 70517844692895600⟩, ⟨.privateRow 18 11, 451073999264288400⟩, ⟨.privateRow 18 13, 398400086075191200⟩, ⟨.privateRow 19 1, 69939764663408640⟩, ⟨.privateRow 19 4, 96851369762155008⟩, ⟨.privateRow 19 5, 31570032660566400⟩, ⟨.privateRow 19 6, 179434457371849680⟩, ⟨.privateRow 19 7, 136241358338891520⟩, ⟨.privateRow 19 8, 10706358902279040⟩, ⟨.privateRow 19 9, 12353491041091200⟩, ⟨.privateRow 19 10, 374928453097117920⟩, ⟨.privateRow 19 12, 2550995899985332800⟩, ⟨.privateRow 20 1, 428357301849837360⟩, ⟨.privateRow 20 3, 127920399730499376⟩, ⟨.privateRow 20 4, 264707860808270880⟩, ⟨.privateRow 20 5, 429824278910966940⟩, ⟨.privateRow 20 6, 687383537215003200⟩, ⟨.privateRow 20 12, 20983639882397512320⟩, ⟨.privateRow 21 0, 1714733187009242400⟩, ⟨.privateRow 21 1, 1002878863608585600⟩, ⟨.privateRow 21 2, 430313271264676800⟩, ⟨.privateRow 21 4, 4391151336314542800⟩, ⟨.privateRow 21 8, 8351989401364408800⟩, ⟨.privateRow 22 3, 1848391097023270800⟩, ⟨.privateRow 22 10, 933232127208193612800⟩, ⟨.hall 16 2, 78723227222640⟩, ⟨.hall 17 3, 429883387876800⟩, ⟨.hall 22 8, 26908923229751122560⟩, ⟨.hall 20 10, 92464008701500800⟩, ⟨.hall 14 11, 14547676082940⟩, ⟨.hall 11 12, 649891503360⟩, ⟨.hall 12 12, 1385639113320⟩, ⟨.hall 18 13, 10588706606649600⟩, ⟨.hall 7 17, 11160796055136⟩, ⟨.hall 6 19, 49903854157872⟩, ⟨.hall 9 19, 81916197277824⟩, ⟨.hall 10 19, 1074363643445040⟩, ⟨.hall 11 19, 650747623846320⟩, ⟨.hall 10 21, 379390904005276800⟩, ⟨.hall 9 22, 1137990324970699200⟩, ⟨.hall 8 23, 2832249768320372400⟩, ⟨.hall 7 24, 92510692125755904⟩, ⟨.hall 5 26, 18548995566551049600⟩, ⟨.hall 3 27, 1399337133581930400⟩, ⟨.hall 4 27, 31740353967205952640⟩]
  caps := #[0, 5212784473118913600, 0, 2332477329436800, 0, 0, 0, 355189889134080, 1062814678082157, 31695720984928, 162138898853568, 346313527230240, 0, 737155424265984, 0, 0, 318453696574650, 5385851906082960, 9715177925168560, 0, 350756543851100244, 0, 0, 0] }

theorem case_55_32_15_checked :
    (Witness.linear .positive case_55_32_15).check 55 32 15 = true := by
  change case_55_32_15.check 55 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_32_16 : Certificate := {
  objectiveScale := 58788475200000
  eta := 873535940667293904000
  rows := #[⟨.count 2, 209758160047381545600⟩, ⟨.count 3, 53750039519787811200⟩, ⟨.count 4, 13801320191107088640⟩, ⟨.count 5, 3545451928793174400⟩, ⟨.count 6, 911413116809395200⟩, ⟨.count 7, 234554846237712000⟩, ⟨.count 8, 61323375462148800⟩, ⟨.count 9, 17294887457527680⟩, ⟨.count 10, 4965618947889600⟩, ⟨.count 11, 1537199111448000⟩, ⟨.count 12, 512399703816000⟩, ⟨.count 13, 121112657265600⟩, ⟨.path 14, 12058743715200⟩, ⟨.privateRow 2 30, 21085350291969163200⟩, ⟨.privateRow 3 29, 33173241275676902400⟩, ⟨.privateRow 6 24, 2004849586181041600⟩, ⟨.privateRow 7 19, 22342401630806400⟩, ⟨.privateRow 7 20, 67876915916409600⟩, ⟨.privateRow 8 17, 9930607100689275⟩, ⟨.privateRow 8 18, 28299990914395200⟩, ⟨.privateRow 8 19, 67717114493628600⟩, ⟨.privateRow 9 14, 71591037405888⟩, ⟨.privateRow 9 15, 3780509168275840⟩, ⟨.privateRow 9 16, 10722170832533160⟩, ⟨.privateRow 9 17, 26009615995883520⟩, ⟨.privateRow 9 18, 49426075430091360⟩, ⟨.privateRow 9 19, 41232669596454336⟩, ⟨.privateRow 9 20, 57649624858425600⟩, ⟨.privateRow 10 12, 137628019620000⟩, ⟨.privateRow 10 13, 1358884014520032⟩, ⟨.privateRow 10 14, 4046508448862880⟩, ⟨.privateRow 10 15, 10016016755865120⟩, ⟨.privateRow 10 16, 19492217096489280⟩, ⟨.privateRow 10 18, 103706346163387968⟩, ⟨.privateRow 11 10, 100150851200400⟩, ⟨.privateRow 11 11, 543736545206400⟩, ⟨.privateRow 11 12, 1530677660672160⟩, ⟨.privateRow 11 13, 3983260727846400⟩, ⟨.privateRow 11 14, 8031865357315800⟩, ⟨.privateRow 11 15, 14062377326025600⟩, ⟨.privateRow 11 16, 7016770489528800⟩, ⟨.privateRow 11 17, 13383880263673920⟩, ⟨.privateRow 12 8, 57152274656400⟩, ⟨.privateRow 12 9, 241254860546700⟩, ⟨.privateRow 12 10, 634288724269200⟩, ⟨.privateRow 12 11, 1633701055666680⟩, ⟨.privateRow 12 12, 3515631301182000⟩, ⟨.privateRow 12 13, 6428481284124900⟩, ⟨.privateRow 12 14, 10546893903546000⟩, ⟨.privateRow 12 15, 8347845174669000⟩, ⟨.privateRow 12 16, 9614326442600880⟩, ⟨.privateRow 13 6, 30610891396800⟩, ⟨.privateRow 13 7, 115379513726400⟩, ⟨.privateRow 13 8, 292688921725200⟩, ⟨.privateRow 13 9, 740227010140800⟩, ⟨.privateRow 13 10, 1628499422309760⟩, ⟨.privateRow 13 11, 3211038143913600⟩, ⟨.privateRow 13 12, 5549055883371000⟩, ⟨.privateRow 13 13, 8753384031163200⟩, ⟨.privateRow 13 14, 8734085860500000⟩, ⟨.privateRow 13 15, 8574776134404480⟩, ⟨.privateRow 14 4, 16955772017184⟩, ⟨.privateRow 14 5, 59691238223760⟩, ⟨.privateRow 14 6, 150925003669440⟩, ⟨.privateRow 14 7, 380495598242760⟩, ⟨.privateRow 14 8, 848889625016160⟩, ⟨.privateRow 14 9, 1742811138051984⟩, ⟨.privateRow 14 10, 3261967569020160⟩, ⟨.privateRow 14 11, 5454611301599460⟩, ⟨.privateRow 14 12, 8405218414232640⟩, ⟨.privateRow 14 13, 9680938404096960⟩, ⟨.privateRow 15 2, 10597357510740⟩, ⟨.privateRow 15 3, 33911544034368⟩, ⟨.privateRow 15 4, 86124556277760⟩, ⟨.privateRow 15 5, 224627748945600⟩, ⟨.privateRow 15 6, 514953076077440⟩, ⟨.privateRow 15 7, 1087567195041600⟩, ⟨.privateRow 15 8, 2132659324828032⟩, ⟨.privateRow 15 9, 3849588239456960⟩, ⟨.privateRow 15 10, 6304250234722440⟩, ⟨.privateRow 15 11, 9573282708749760⟩, ⟨.privateRow 15 14, 16753244740312080⟩, ⟨.privateRow 15 16, 23860539177515040⟩, ⟨.privateRow 16 1, 39740090665275⟩, ⟨.privateRow 16 2, 44744398378680⟩, ⟨.privateRow 16 3, 151390821582000⟩, ⟨.privateRow 16 4, 364114334984400⟩, ⟨.privateRow 16 5, 800689234144800⟩, ⟨.privateRow 16 6, 1621716831189000⟩, ⟨.privateRow 16 7, 3073233678114600⟩, ⟨.privateRow 16 8, 5396802436025000⟩, ⟨.privateRow 16 9, 8711910986954175⟩, ⟨.privateRow 16 10, 13105398788281800⟩, ⟨.privateRow 16 12, 16757954676983520⟩, ⟨.privateRow 16 15, 28436242653819000⟩, ⟨.privateRow 17 0, 95880853668600⟩, ⟨.privateRow 17 1, 80741771510400⟩, ⟨.privateRow 17 2, 299898008467200⟩, ⟨.privateRow 17 3, 695621416089600⟩, ⟨.privateRow 17 4, 1473537330064800⟩, ⟨.privateRow 17 5, 2892023452281600⟩, ⟨.privateRow 17 6, 5320882742535360⟩, ⟨.privateRow 17 7, 9132791488620800⟩, ⟨.privateRow 17 8, 14583982479066000⟩, ⟨.privateRow 17 9, 21823347385382400⟩, ⟨.privateRow 17 12, 53370310968374400⟩, ⟨.privateRow 17 13, 20400754268294400⟩, ⟨.privateRow 17 15, 366971351514768000⟩, ⟨.privateRow 18 0, 732058728360960⟩, ⟨.privateRow 18 1, 457536705225600⟩, ⟨.privateRow 18 2, 1618976033875200⟩, ⟨.privateRow 18 3, 3298077083501200⟩, ⟨.privateRow 18 4, 6280731135369600⟩, ⟨.privateRow 18 6, 41559584057992000⟩, ⟨.privateRow 18 8, 74774570111155200⟩, ⟨.privateRow 18 10, 48041354048688000⟩, ⟨.privateRow 18 12, 98522903858579200⟩, ⟨.privateRow 19 0, 5941440929286720⟩, ⟨.privateRow 19 1, 2280644499893760⟩, ⟨.privateRow 19 2, 9196487775034560⟩, ⟨.privateRow 19 3, 17145148172181120⟩, ⟨.privateRow 19 4, 7576807838535936⟩, ⟨.privateRow 19 5, 74212453587592320⟩, ⟨.privateRow 19 6, 63311641585592400⟩, ⟨.privateRow 19 7, 95063054868587520⟩, ⟨.privateRow 19 8, 127240957723239360⟩, ⟨.privateRow 19 11, 45845177863605120⟩, ⟨.privateRow 20 0, 54767143615504320⟩, ⟨.privateRow 20 2, 80372561409766080⟩, ⟨.privateRow 20 3, 39119388296788800⟩, ⟨.privateRow 20 5, 535935619666006560⟩, ⟨.privateRow 20 8, 1707952493037799008⟩, ⟨.privateRow 21 0, 584617525102010400⟩, ⟨.privateRow 21 1, 56900928431692800⟩, ⟨.privateRow 21 2, 344250617011741440⟩, ⟨.privateRow 21 3, 118807031123580800⟩, ⟨.privateRow 21 7, 14568060201724149120⟩, ⟨.privateRow 22 0, 8912107915613884800⟩, ⟨.privateRow 22 2, 1490883353977617600⟩, ⟨.privateRow 22 3, 650359830434113800⟩, ⟨.privateRow 23 6, 582859325928004725600⟩, ⟨.hall 18 6, 642014042117760⟩, ⟨.hall 19 7, 2177098824209400⟩, ⟨.hall 17 9, 55855130248320⟩, ⟨.hall 20 9, 45165111942656160⟩, ⟨.hall 16 15, 12222285662386800⟩, ⟨.hall 15 16, 155361416933923200⟩, ⟨.hall 14 17, 147449277436100640⟩, ⟨.hall 11 18, 75794061451680⟩, ⟨.hall 13 18, 192530878950009600⟩, ⟨.hall 12 19, 225373885726429440⟩, ⟨.hall 11 20, 336885725268892800⟩, ⟨.hall 10 21, 617008432439599200⟩, ⟨.hall 5 22, 476664493905600⟩, ⟨.hall 9 22, 849240899592845760⟩, ⟨.hall 8 23, 1627106497357341000⟩, ⟨.hall 7 24, 3566364047614368000⟩, ⟨.hall 6 25, 6534257662982649600⟩, ⟨.hall 4 27, 16624063480922520480⟩, ⟨.hall 3 28, 20981481571319068800⟩]
  caps := #[0, 672243003156816000, 115838751553761600, 6341899144089600, 0, 0, 36427258857600, 0, 492845056028325, 48236123353600, 43085453287968, 51985939527600, 0, 61735293131760, 460511590726044, 62852705784960, 0, 2212849956895760, 2826751809570000, 0, 2449901085253440, 108763753825162800, 0, 0] }

theorem case_55_32_16_checked :
    (Witness.linear .positive case_55_32_16).check 55 32 16 = true := by
  change case_55_32_16.check 55 32 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_32_17 : Certificate := {
  objectiveScale := 259360920000000
  eta := 3614631478623285120000
  rows := #[⟨.count 2, 814935096998704281600⟩, ⟨.count 3, 200447745632745811200⟩, ⟨.count 4, 49572088849690767360⟩, ⟨.count 5, 12229956130680288000⟩, ⟨.count 6, 3022487474720313600⟩, ⟨.count 7, 817268211228268800⟩, ⟨.count 8, 227207345030265600⟩, ⟨.count 9, 65110164545986560⟩, ⟨.count 10, 19620250477027200⟩, ⟨.count 11, 6148796445792000⟩, ⟨.count 12, 1844638933737600⟩, ⟨.count 13, 726675943593600⟩, ⟨.path 13, 82888011687936⟩, ⟨.privateRow 2 30, 49290429253953888000⟩, ⟨.privateRow 4 25, 1167713740659145680⟩, ⟨.privateRow 4 26, 7409212143411798720⟩, ⟨.privateRow 5 23, 761963327414505216⟩, ⟨.privateRow 5 24, 2558407994609987520⟩, ⟨.privateRow 5 25, 5832494903533858560⟩, ⟨.privateRow 6 21, 353904641492001600⟩, ⟨.privateRow 6 22, 922668519757944960⟩, ⟨.privateRow 6 23, 2031806123730583200⟩, ⟨.privateRow 6 24, 3323546626758758400⟩, ⟨.privateRow 7 19, 144781530856934400⟩, ⟨.privateRow 7 20, 342829561833158400⟩, ⟨.privateRow 7 21, 730163988122849280⟩, ⟨.privateRow 7 22, 1185087351343896000⟩, ⟨.privateRow 7 23, 1646163237554035200⟩, ⟨.privateRow 8 16, 4403790787796400⟩, ⟨.privateRow 8 17, 51423677320865850⟩, ⟨.privateRow 8 18, 130196106560520000⟩, ⟨.privateRow 8 19, 272670008751340200⟩, ⟨.privateRow 8 20, 439917504985838880⟩, ⟨.privateRow 8 21, 605533008163683600⟩, ⟨.privateRow 8 22, 700485331459914000⟩, ⟨.privateRow 9 14, 3210292835253504⟩, ⟨.privateRow 9 15, 19455178410828160⟩, ⟨.privateRow 9 16, 48564157019217840⟩, ⟨.privateRow 9 17, 106175429536176000⟩, ⟨.privateRow 9 18, 172176444961160640⟩, ⟨.privateRow 9 19, 236951262016140672⟩, ⟨.privateRow 9 20, 275474776039182720⟩, ⟨.privateRow 9 21, 244389194007678720⟩, ⟨.privateRow 10 12, 1638323945556480⟩, ⟨.privateRow 10 13, 7833566671939008⟩, ⟨.privateRow 10 14, 19071206430756480⟩, ⟨.privateRow 10 15, 42156288177723720⟩, ⟨.privateRow 10 16, 71754058887413760⟩, ⟨.privateRow 10 17, 100317614013096480⟩, ⟨.privateRow 10 18, 118898717890784832⟩, ⟨.privateRow 10 19, 38531991909050640⟩, ⟨.privateRow 11 10, 726675943593600⟩, ⟨.privateRow 11 11, 3292909170969600⟩, ⟨.privateRow 11 12, 8004615009431040⟩, ⟨.privateRow 11 13, 17806666070793600⟩, ⟨.privateRow 11 14, 31386810948292800⟩, ⟨.privateRow 11 15, 46467333140342400⟩, ⟨.privateRow 11 16, 21492838485518400⟩, ⟨.privateRow 12 8, 295615213740000⟩, ⟨.privateRow 12 9, 1426179175621200⟩, ⟨.privateRow 12 10, 3582139747586400⟩, ⟨.privateRow 12 11, 8157403284750720⟩, ⟨.privateRow 12 12, 14899444720960800⟩, ⟨.privateRow 12 13, 10965353661662400⟩, ⟨.privateRow 13 6, 111796299014400⟩, ⟨.privateRow 13 7, 636378932851200⟩, ⟨.privateRow 13 8, 1704893559969600⟩, ⟨.privateRow 13 9, 4070401614115200⟩, ⟨.privateRow 13 10, 4438313070871680⟩, ⟨.privateRow 14 4, 38756050324992⟩, ⟨.privateRow 14 5, 290670377437440⟩, ⟨.privateRow 14 6, 860831502410880⟩, ⟨.privateRow 14 7, 1532075114409840⟩, ⟨.privateRow 15 3, 143182074811776⟩, ⟨.privateRow 15 4, 436005566156160⟩, ⟨.privateRow 16 0, 12467479424400⟩, ⟨.privateRow 16 1, 39740090665275⟩, ⟨.privateRow 16 2, 56519240057280⟩, ⟨.privateRow 17 0, 30278164316400⟩, ⟨.hall 7 23, 32973324649417152⟩, ⟨.hall 8 23, 189551401342102800⟩, ⟨.hall 7 24, 811028487125945088⟩, ⟨.hall 6 25, 4976873108657049600⟩, ⟨.hall 5 26, 11986546603500268800⟩, ⟨.hall 4 27, 24745807339740115200⟩, ⟨.hall 3 28, 44871287320840780800⟩, ⟨.hall 2 29, 65172900902450140800⟩, ⟨.assumptionRow 17, 320124687966720⟩]
  caps := #[0, 2245294815708672000, 886632733116748800, 66717659815148160, 0, 20122443323933184, 0, 5391350977284480, 0, 0, 238333868942520, 0, 856325228298960, 218875683766656, 320124687966720, 893611473815424, 68437447086645, 0, 259360920000000, 0, 0, 0, 0, 0] }

theorem case_55_32_17_checked :
    (Witness.linear .conditional case_55_32_17).check 55 32 17 = true := by
  change case_55_32_17.check 55 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_32_18 : Certificate := {
  objectiveScale := 695996014391496000000
  eta := 12609840501030765704404492800
  rows := #[⟨.count 2, 2593982340829755415882742400⟩, ⟨.count 3, 582622500672000912915792000⟩, ⟨.count 4, 129751605555061824930435840⟩, ⟨.count 5, 28841056932269746471507200⟩, ⟨.count 6, 6482791851953352974438400⟩, ⟨.count 7, 1539446393988254441289600⟩, ⟨.count 8, 382965728553728321601600⟩, ⟨.count 9, 111477152668114976783040⟩, ⟨.count 10, 37375721740038549067200⟩, ⟨.count 11, 13750265523091105008000⟩, ⟨.count 12, 5500106209236442003200⟩, ⟨.count 13, 1625031380001676046400⟩, ⟨.count 14, 2275043932002346464960⟩, ⟨.path 10, 793828682420729155200⟩, ⟨.path 11, 243637774570961735328⟩, ⟨.privateRow 2 30, 150642033957535371177326400⟩, ⟨.privateRow 4 25, 3766050848938384279433160⟩, ⟨.privateRow 4 26, 21590275250127601397540160⟩, ⟨.privateRow 5 23, 2190152292711058908296064⟩, ⟨.privateRow 5 24, 7215789339759442316434560⟩, ⟨.privateRow 5 25, 17319367777207196412391680⟩, ⟨.privateRow 6 21, 907038348604268846565600⟩, ⟨.privateRow 6 22, 2498576026273688125564800⟩, ⟨.privateRow 6 23, 5881936499197733256282000⟩, ⟨.privateRow 6 24, 10374922566099589514016000⟩, ⟨.privateRow 7 19, 326863454720337124761600⟩, ⟨.privateRow 7 20, 879141976580906741102400⟩, ⟨.privateRow 7 21, 2054473006023452302928640⟩, ⟨.privateRow 7 22, 3654966412187103041028000⟩, ⟨.privateRow 7 23, 5575663223827972923648000⟩, ⟨.privateRow 8 16, 1211250241575323349400⟩, ⟨.privateRow 8 17, 107649865220006862677925⟩, ⟨.privateRow 8 18, 310719541784487140705400⟩, ⟨.privateRow 8 19, 740100229129513334382300⟩, ⟨.privateRow 8 20, 1336683103548545312600040⟩, ⟨.privateRow 8 21, 2053227148632117684626400⟩, ⟨.privateRow 8 22, 2700508745119174175386200⟩, ⟨.privateRow 9 15, 34715485184628397909760⟩, ⟨.privateRow 9 16, 109107315238945865882040⟩, ⟨.privateRow 9 17, 274449744178060843392000⟩, ⟨.privateRow 9 18, 511295058495934753680640⟩, ⟨.privateRow 9 19, 798135967878245414273856⟩, ⟨.privateRow 9 20, 1063203864222429914624640⟩, ⟨.privateRow 9 21, 1150329620729482738504960⟩, ⟨.privateRow 10 13, 10253948007810575852784⟩, ⟨.privateRow 10 14, 38675746844039889904320⟩, ⟨.privateRow 10 15, 104042634104607308870760⟩, ⟨.privateRow 10 16, 205148604358211588886240⟩, ⟨.privateRow 10 17, 330666801974007714174960⟩, ⟨.privateRow 10 18, 452343734937266544275904⟩, ⟨.privateRow 10 19, 511438001071027493703240⟩, ⟨.privateRow 10 20, 251013180497592226633920⟩, ⟨.privateRow 11 11, 2852327806856088724800⟩, ⟨.privateRow 11 12, 13375258281552256689600⟩, ⟨.privateRow 11 13, 40584117028759806902400⟩, ⟨.privateRow 11 14, 85970410122780976993200⟩, ⟨.privateRow 11 15, 146717118880151323046400⟩, ⟨.privateRow 11 16, 210045722733037152561600⟩, ⟨.privateRow 11 17, 162628140414013887412800⟩, ⟨.privateRow 12 9, 697062071656701851100⟩, ⟨.privateRow 12 10, 4573004973209844771600⟩, ⟨.privateRow 12 11, 15915932342977954046760⟩, ⟨.privateRow 12 12, 37762303279155756901600⟩, ⟨.privateRow 12 13, 69510456857876179795650⟩, ⟨.privateRow 12 14, 96219119934201803853600⟩, ⟨.privateRow 13 7, 105771273254546961600⟩, ⟨.privateRow 13 8, 1520862701796440402400⟩, ⟨.privateRow 13 9, 6306939971335176264000⟩, ⟨.privateRow 13 10, 17000328283094457100800⟩, ⟨.privateRow 13 11, 35125678290805459156800⟩, ⟨.privateRow 13 12, 13015876341744193717800⟩, ⟨.privateRow 14 6, 412507965692733150240⟩, ⟨.privateRow 14 7, 2505256710835917238200⟩, ⟨.privateRow 14 8, 7874015686735393933920⟩, ⟨.privateRow 14 9, 11001462442611346834128⟩, ⟨.privateRow 15 4, 90279521111204224800⟩, ⟨.privateRow 15 5, 913906536787267383360⟩, ⟨.privateRow 15 6, 3707479000300120165120⟩, ⟨.privateRow 15 7, 1103051603395077073920⟩, ⟨.privateRow 16 3, 304693383750314258700⟩, ⟨.privateRow 16 4, 1020853046411309311200⟩, ⟨.privateRow 17 1, 72223616888963379840⟩, ⟨.privateRow 17 2, 154764893333492956800⟩, ⟨.hall 8 23, 1940106908679778790952000⟩, ⟨.hall 7 24, 7406026346644971858933120⟩, ⟨.hall 6 25, 19059493046384273217134400⟩, ⟨.hall 5 26, 41368724772439704460620800⟩, ⟨.hall 4 27, 80022488123186534654277120⟩, ⟨.hall 3 28, 139655645081862660579628800⟩, ⟨.hall 2 29, 200611098880034908933707840⟩, ⟨.assumptionRow 18, 665116991219659960800⟩]
  caps := #[0, 16117555446883327948449120, 0, 0, 40423751384299475748192, 9949885883183371260096, 0, 14616124642200616367040, 389478533884771941792, 1851168798019962573152, 0, 1388246269284820902528, 0, 775270195763236639200, 1210021849117626900264, 665116991219659960800, 665116991219659960800, 1708752661661716357440, 8382831195869788039200, 695996014391496000000, 0, 0, 0, 0] }

theorem case_55_32_18_checked :
    (Witness.linear .conditional case_55_32_18).check 55 32 18 = true := by
  change case_55_32_18.check 55 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_32_19 : Certificate := {
  objectiveScale := 5159801951765935783920000000
  eta := 109538504327678674799903222020550400
  rows := #[⟨.count 2, 20925823617588964893433514441942400⟩, ⟨.count 3, 4312500374720616249728275973654400⟩, ⟨.count 4, 864489694494167363555679774188160⟩, ⟨.count 5, 169641245845866528854727301094400⟩, ⟨.count 6, 33247589849421372167515998825600⟩, ⟨.count 7, 6898990390245842858289563443200⟩, ⟨.count 8, 1634916993521801302355078836800⟩, ⟨.count 9, 463525916844642567041330043840⟩, ⟨.count 10, 153995321210844706658249184000⟩, ⟨.count 11, 71667053332739267329415966400⟩, ⟨.count 12, 32575933333063303331552712000⟩, ⟨.count 13, 15399532121084470665824918400⟩, ⟨.count 14, 10779672484759129466077442880⟩, ⟨.path 9, 15451789760969492895363020160⟩, ⟨.path 10, 4898744315653921516358467200⟩, ⟨.privateRow 2 30, 1096777776961817627526049425825600⟩, ⟨.privateRow 4 25, 29160361530334040096922742670760⟩, ⟨.privateRow 4 26, 157179944453484975191941777125120⟩, ⟨.privateRow 5 23, 15759881172717847279405221490560⟩, ⟨.privateRow 5 24, 50787656935336584255890580883200⟩, ⟨.privateRow 5 25, 128365366583986452646761244809600⟩, ⟨.privateRow 6 21, 5970313050388221030081066280800⟩, ⟨.privateRow 6 22, 16873951768722080485018399753920⟩, ⟨.privateRow 6 23, 42308503443555018213168871646400⟩, ⟨.privateRow 6 24, 80321678131410512404695985497600⟩, ⟨.privateRow 7 19, 1922008270922018934053671958400⟩, ⟨.privateRow 7 20, 5616551576384419440063366072000⟩, ⟨.privateRow 7 21, 14265099921497914660109149411200⟩, ⟨.privateRow 7 22, 27717874523608623492596034376800⟩, ⟨.privateRow 7 23, 46210573777125366585770396803200⟩, ⟨.privateRow 8 17, 550493170380537835494215247075⟩, ⟨.privateRow 8 18, 1838639970540314612205054319800⟩, ⟨.privateRow 8 19, 4911862570051876943865773712300⟩, ⟨.privateRow 8 20, 9867891853756586432071725836400⟩, ⟨.privateRow 8 21, 16810113222196515382490870691150⟩, ⟨.privateRow 8 22, 24650266336849539874198896985800⟩, ⟨.privateRow 9 15, 139071083291028275210505281600⟩, ⟨.privateRow 9 16, 583449773237587882351441595880⟩, ⟨.privateRow 9 17, 1713283501426875608632276754880⟩, ⟨.privateRow 9 18, 3636941722219010735971572811680⟩, ⟨.privateRow 9 19, 6394022621404237415745313452288⟩, ⟨.privateRow 9 20, 9616366162445540077863252169200⟩, ⟨.privateRow 9 21, 12059658780542009801938342208640⟩, ⟨.privateRow 10 13, 28412136763400848378446974448⟩, ⟨.privateRow 10 14, 175896878005275953827422401280⟩, ⟨.privateRow 10 15, 597790587525347795658991051140⟩, ⟨.privateRow 10 16, 1383647961079439689324368918240⟩, ⟨.privateRow 10 17, 2556450661534364501115818328720⟩, ⟨.privateRow 10 18, 3987400852112401989502046121312⟩, ⟨.privateRow 10 19, 5232376026441476020480661649360⟩, ⟨.privateRow 10 20, 5277932975633017579533727032960⟩, ⟨.privateRow 11 11, 2584536859482708363495091200⟩, ⟨.privateRow 11 12, 48330839272326646397358205440⟩, ⟨.privateRow 11 13, 204998045116145838136942824000⟩, ⟨.privateRow 11 14, 538169225904629890720583326200⟩, ⟨.privateRow 11 15, 1073821220597159435274637579200⟩, ⟨.privateRow 11 16, 1767886030490396058681143997600⟩, ⟨.privateRow 11 17, 2456225373312973071199074484800⟩, ⟨.privateRow 11 18, 2086932747255428168885926922400⟩, ⟨.privateRow 12 10, 8785630504977678777297549600⟩, ⟨.privateRow 12 11, 67052129443888632690779332200⟩, ⟨.privateRow 12 12, 210537050615538756716886972000⟩, ⟨.privateRow 12 13, 470111437912769796203470075050⟩, ⟨.privateRow 12 14, 837977104120037926652608334400⟩, ⟨.privateRow 12 15, 1252363659248878105857470928000⟩, ⟨.privateRow 12 16, 182208053776267409967818169120⟩, ⟨.privateRow 13 8, 691004646458918555517784800⟩, ⟨.privateRow 13 9, 17607157355225950726310308800⟩, ⟨.privateRow 13 10, 80669856726604034795590534080⟩, ⟨.privateRow 13 11, 211052562018452553099574843200⟩, ⟨.privateRow 13 12, 421117974541963793976981422400⟩, ⟨.privateRow 13 13, 368996481209062508646497083200⟩, ⟨.privateRow 14 7, 3272400575730450016487795160⟩, ⟨.privateRow 14 8, 26599191845509540240970313600⟩, ⟨.privateRow 14 9, 94399131902247805181506749792⟩, ⟨.privateRow 14 10, 220384415243964424639805498880⟩, ⟨.privateRow 14 11, 28392887348249492790114693300⟩, ⟨.privateRow 15 5, 368535811444756562942818560⟩, ⟨.privateRow 15 6, 7286260105439041213181975280⟩, ⟨.privateRow 15 7, 37674410906329886820836315520⟩, ⟨.privateRow 15 8, 73541321173801172135239443648⟩, ⟨.privateRow 16 4, 1727511616147296388794462000⟩, ⟨.privateRow 16 5, 13100296422450330948358003500⟩, ⟨.privateRow 16 6, 18986923126564375764113677800⟩, ⟨.privateRow 17 2, 366655526692487396805355200⟩, ⟨.privateRow 17 3, 4343457777741773777540361600⟩, ⟨.privateRow 17 4, 3422118249129882370183315200⟩, ⟨.privateRow 18 1, 1038857325628714290948506400⟩, ⟨.hall 9 22, 4386389338472204029261686431040⟩, ⟨.hall 8 23, 28051103288117645788392634694400⟩, ⟨.hall 7 24, 78763473621973372632139182643200⟩, ⟨.hall 6 25, 177119100699945957200096334547200⟩, ⟨.hall 5 26, 353244734148182977779802528204800⟩, ⟨.hall 4 27, 645311783704486348194222083617440⟩, ⟨.hall 3 28, 1086057844041321325747899752025600⟩, ⟨.hall 2 29, 1534328276342352278930621524805760⟩, ⟨.assumptionRow 19, 3409944182492990448738584880⟩]
  caps := #[0, 119656348511262917002336953064800, 16389265530650876344798852626000, 0, 127736298220603202738953745400, 0, 50689897731162461332915504800, 0, 2875319271802980935853427470, 8962191399411532704390527840, 517410040986682172032736340, 901155182944555525282808400, 3053479396718176274132420070, 1380874723221780912995269920, 2415785806144876165269603516, 5668472410253998238348539920, 10563019178437309113718933500, 3409944182492990448738584880, 108844004390820321155339392560, 58507679238698238958301415120, 5159801951765935783920000000, 0, 0, 0] }

theorem case_55_32_19_checked :
    (Witness.linear .conditional case_55_32_19).check 55 32 19 = true := by
  change case_55_32_19.check 55 32 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_32_20 : Certificate := {
  objectiveScale := 213188976000000
  eta := 4644801450030921379200
  rows := #[⟨.count 2, 980879542153682371200⟩, ⟨.count 3, 222511080632134694400⟩, ⟨.count 4, 49525145583734620800⟩, ⟨.count 5, 10772244187831526400⟩, ⟨.count 6, 2273042351560780800⟩, ⟨.count 7, 484935079691462400⟩, ⟨.count 8, 100039054901385600⟩, ⟨.count 9, 18820906939074240⟩, ⟨.count 10, 2906703774374400⟩, ⟨.count 11, 307439822289600⟩, ⟨.path 11, 297072642655152⟩, ⟨.privateRow 2 30, 69828108109768008000⟩, ⟨.privateRow 4 25, 1246930501960143000⟩, ⟨.privateRow 4 26, 8629737058271609280⟩, ⟨.privateRow 5 23, 715514201100002304⟩, ⟨.privateRow 5 24, 2749887105746901120⟩, ⟨.privateRow 5 25, 7178201860943393280⟩, ⟨.privateRow 6 21, 291222112876094400⟩, ⟨.privateRow 6 22, 900706757907116160⟩, ⟨.privateRow 6 23, 2342530738666918800⟩, ⟨.privateRow 6 24, 4570562916851131200⟩, ⟨.privateRow 7 19, 102253686348528000⟩, ⟨.privateRow 7 20, 298219733073662400⟩, ⟨.privateRow 7 21, 777543259645152000⟩, ⟨.privateRow 7 22, 1557084878135186400⟩, ⟨.privateRow 7 23, 2683775743234185600⟩, ⟨.privateRow 8 16, 1554279101575200⟩, ⟨.privateRow 8 17, 31195971172240875⟩, ⟨.privateRow 8 18, 98449451274774600⟩, ⟨.privateRow 8 19, 263008751154048900⟩, ⟨.privateRow 8 20, 543602050870919040⟩, ⟨.privateRow 8 21, 961922141249869800⟩, ⟨.privateRow 8 22, 1477236312472120200⟩, ⟨.privateRow 9 14, 994738625008128⟩, ⟨.privateRow 9 15, 9344514356136960⟩, ⟨.privateRow 9 16, 31410567661833360⟩, ⟨.privateRow 9 17, 90414635737345920⟩, ⟨.privateRow 9 18, 195528310978160160⟩, ⟨.privateRow 9 19, 358151120394971904⟩, ⟨.privateRow 9 20, 567340131694976640⟩, ⟨.privateRow 9 21, 760164939023730240⟩, ⟨.privateRow 10 12, 376550261680320⟩, ⟨.privateRow 10 13, 2819502661143168⟩, ⟨.privateRow 10 14, 9943349161505760⟩, ⟨.privateRow 10 15, 30997270718914500⟩, ⟨.privateRow 10 16, 72568974052729440⟩, ⟨.privateRow 10 17, 139394612879842320⟩, ⟨.privateRow 10 18, 229862134477527552⟩, ⟨.privateRow 10 19, 323407128696331680⟩, ⟨.privateRow 10 20, 361412280546276960⟩, ⟨.privateRow 11 10, 100150851200400⟩, ⟨.privateRow 11 11, 818145642787200⟩, ⟨.privateRow 11 12, 3155450539681440⟩, ⟨.privateRow 11 13, 10698284725128000⟩, ⟨.privateRow 11 14, 27452978676723600⟩, ⟨.privateRow 11 15, 56872374398611200⟩, ⟨.privateRow 11 16, 98949040985995200⟩, ⟨.privateRow 11 17, 147369881360782080⟩, ⟨.privateRow 11 18, 181599113211516000⟩, ⟨.privateRow 11 19, 55478913385896000⟩, ⟨.privateRow 12 8, 17736912824400⟩, ⟨.privateRow 12 9, 209229879058200⟩, ⟨.privateRow 12 10, 971230347687600⟩, ⟨.privateRow 12 11, 3732831842299560⟩, ⟨.privateRow 12 12, 10620907194097200⟩, ⟨.privateRow 12 13, 24137228547882450⟩, ⟨.privateRow 12 14, 45372993772906800⟩, ⟨.privateRow 12 15, 72402078149200800⟩, ⟨.privateRow 12 16, 67718744856322560⟩, ⟨.privateRow 13 7, 38698718889600⟩, ⟨.privateRow 13 8, 267845299722000⟩, ⟨.privateRow 13 9, 1283116613688000⟩, ⟨.privateRow 13 10, 4209130657892160⟩, ⟨.privateRow 13 11, 10657913839372800⟩, ⟨.privateRow 13 12, 22044832711902000⟩, ⟨.privateRow 13 13, 38378072361657600⟩, ⟨.privateRow 13 14, 9008918428910400⟩, ⟨.privateRow 14 5, 2595271227120⟩, ⟨.privateRow 14 6, 50308334556480⟩, ⟨.privateRow 14 7, 399671768976480⟩, ⟨.privateRow 14 8, 1664748525323520⟩, ⟨.privateRow 14 9, 4890529100384928⟩, ⟨.privateRow 14 10, 11328070542909120⟩, ⟨.privateRow 14 11, 13389004260712080⟩, ⟨.privateRow 15 5, 86952677011200⟩, ⟨.privateRow 15 6, 612291767287200⟩, ⟨.privateRow 15 7, 2276183940488640⟩, ⟨.privateRow 15 8, 6137989470220608⟩, ⟨.privateRow 15 9, 1927934077509440⟩, ⟨.privateRow 16 4, 154884455926200⟩, ⟨.privateRow 16 5, 997917832261350⟩, ⟨.privateRow 16 6, 2418124304723400⟩, ⟨.privateRow 17 3, 316756180540800⟩, ⟨.privateRow 17 4, 746861386471200⟩, ⟨.privateRow 18 2, 263963483784000⟩, ⟨.hall 9 22, 485539589824248960⟩, ⟨.hall 8 23, 1995765015472628400⟩, ⟨.hall 7 24, 5065842094030029312⟩, ⟨.hall 6 25, 10828626787967788800⟩, ⟨.hall 5 26, 20926356286903267200⟩, ⟨.hall 4 27, 37385281698432576480⟩, ⟨.hall 3 28, 61754675731965216000⟩, ⟨.hall 2 29, 86093949763572791040⟩, ⟨.assumptionRow 20, 30379209213600⟩]
  caps := #[0, 11771068543617080880, 0, 0, 9881814615256584, 1798610758259328, 1391406170927760, 229044938391360, 1472599165731057, 94577677964640, 124246559099520, 133056386797752, 199127695169670, 20991703824000, 1103844899985984, 30379209213600, 646706767174650, 30379209213600, 30379209213600, 13492732929436800, 2314699526786400, 213188976000000, 0, 0] }

theorem case_55_32_20_checked :
    (Witness.linear .conditional case_55_32_20).check 55 32 20 = true := by
  change case_55_32_20.check 55 32 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_33_1_checked :
    (Witness.rising).check 55 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_33_2_checked :
    (Witness.rising).check 55 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_33_3_checked :
    (Witness.rising).check 55 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_33_4_checked :
    (Witness.rising).check 55 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_33_5_checked :
    (Witness.rising).check 55 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_33_6_checked :
    (Witness.rising).check 55 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_33_7_checked :
    (Witness.rising).check 55 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_33_8_checked :
    (Witness.rising).check 55 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_33_9_checked :
    (Witness.rising).check 55 33 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_33_10_checked :
    (Witness.rising).check 55 33 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_33_11_checked :
    (Witness.linear .positive case_55_33_11).check 55 33 11 = true := by
  change case_55_33_11.check 55 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_33_12_checked :
    (Witness.linear .positive case_55_33_12).check 55 33 12 = true := by
  change case_55_33_12.check 55 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_33_13_checked :
    (Witness.linear .positive case_55_33_13).check 55 33 13 = true := by
  change case_55_33_13.check 55 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_33_14_checked :
    (Witness.linear .positive case_55_33_14).check 55 33 14 = true := by
  change case_55_33_14.check 55 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_33_15 : Certificate := {
  objectiveScale := 147294201600000
  eta := 5175495071665158240000
  rows := #[⟨.count 2, 1075000790395756224000⟩, ⟨.count 3, 237122172160985311200⟩, ⟨.count 4, 49623973512063350400⟩, ⟨.count 5, 11324033454333600000⟩, ⟨.count 6, 2474331587936208000⟩, ⟨.count 7, 575436512833182000⟩, ⟨.count 8, 133102810334894400⟩, ⟨.count 9, 32155410504016800⟩, ⟨.count 10, 8384722426080000⟩, ⟨.count 11, 2305798667172000⟩, ⟨.count 12, 838472242608000⟩, ⟨.path 13, 98195939566400⟩, ⟨.privateRow 2 31, 61026245742990528000⟩, ⟨.privateRow 3 30, 120761551672187025600⟩, ⟨.privateRow 6 21, 111942698929776000⟩, ⟨.privateRow 6 23, 204074827492536000⟩, ⟨.privateRow 6 25, 9420344336547144000⟩, ⟨.privateRow 6 27, 21638592910358424000⟩, ⟨.privateRow 7 19, 79423409772456750⟩, ⟨.privateRow 7 20, 163729173540933000⟩, ⟨.privateRow 7 21, 261679035104487000⟩, ⟨.privateRow 7 22, 509808591677385000⟩, ⟨.privateRow 7 23, 721509731807114250⟩, ⟨.privateRow 7 25, 8601231680475934500⟩, ⟨.privateRow 8 16, 5107926320176680⟩, ⟨.privateRow 8 17, 34370762859833400⟩, ⟨.privateRow 8 18, 76923568831083975⟩, ⟨.privateRow 8 19, 130574583614475000⟩, ⟨.privateRow 8 20, 221431785186912300⟩, ⟨.privateRow 8 21, 326186664180577200⟩, ⟨.privateRow 8 22, 378829037615178150⟩, ⟨.privateRow 8 23, 77961226754010600⟩, ⟨.privateRow 8 24, 471953316740805900⟩, ⟨.privateRow 9 14, 4602280976092800⟩, ⟨.privateRow 9 15, 14345794253110320⟩, ⟨.privateRow 9 16, 31818986456056800⟩, ⟨.privateRow 9 17, 55885921786995300⟩, ⟨.privateRow 9 18, 100921447118606400⟩, ⟨.privateRow 9 19, 149150237422586400⟩, ⟨.privateRow 10 11, 248316779541600⟩, ⟨.privateRow 10 12, 2515416727824000⟩, ⟨.privateRow 10 13, 6597252054338400⟩, ⟨.privateRow 10 14, 13340093379893280⟩, ⟨.privateRow 10 15, 23663549958048000⟩, ⟨.privateRow 10 16, 43909743255077700⟩, ⟨.privateRow 10 17, 67712622678043200⟩, ⟨.privateRow 10 18, 94838197907653200⟩, ⟨.privateRow 10 19, 47205987258830400⟩, ⟨.privateRow 10 20, 31400785485669600⟩, ⟨.privateRow 11 9, 304445278566000⟩, ⟨.privateRow 11 10, 1249646130810000⟩, ⟨.privateRow 11 11, 3196675424943000⟩, ⟨.privateRow 11 12, 6218669132676000⟩, ⟨.privateRow 11 13, 10687027458907800⟩, ⟨.privateRow 11 14, 20193206509476000⟩, ⟨.privateRow 11 16, 112345298697060000⟩, ⟨.privateRow 11 18, 66742390511596800⟩, ⟨.privateRow 11 20, 100500214634820000⟩, ⟨.privateRow 12 6, 13101128790750⟩, ⟨.privateRow 12 7, 221263508466000⟩, ⟨.privateRow 12 8, 683754150222000⟩, ⟨.privateRow 12 9, 1633945908672000⟩, ⟨.privateRow 12 10, 3243257216199000⟩, ⟨.privateRow 12 11, 5548526544834000⟩, ⟨.privateRow 12 12, 10295740412357400⟩, ⟨.privateRow 12 13, 17235262764720000⟩, ⟨.privateRow 12 14, 2698832530894500⟩, ⟨.privateRow 12 15, 72517867173180000⟩, ⟨.privateRow 12 16, 31838654323476000⟩, ⟨.privateRow 12 17, 31722199845336000⟩, ⟨.privateRow 12 19, 93058773481674000⟩, ⟨.privateRow 13 4, 27127043143200⟩, ⟨.privateRow 13 5, 141492190940100⟩, ⟨.privateRow 13 6, 419236121304000⟩, ⟨.privateRow 13 7, 949270360381200⟩, ⟨.privateRow 13 8, 1883337652627200⟩, ⟨.privateRow 13 9, 3346901701743600⟩, ⟨.privateRow 13 10, 6219939545164800⟩, ⟨.privateRow 13 11, 10426402336830480⟩, ⟨.privateRow 13 12, 16690255807024800⟩, ⟨.privateRow 13 14, 63280697967115200⟩, ⟨.privateRow 13 15, 42531504506290800⟩, ⟨.privateRow 13 20, 920558675159323200⟩, ⟨.privateRow 14 2, 30278164316400⟩, ⟨.privateRow 14 3, 99739835395200⟩, ⟨.privateRow 14 4, 280073019926700⟩, ⟨.privateRow 14 5, 645934172083200⟩, ⟨.privateRow 14 6, 1280333805379200⟩, ⟨.privateRow 14 7, 2319773204548800⟩, ⟨.privateRow 14 8, 4476121958107800⟩, ⟨.privateRow 14 9, 7619087166163200⟩, ⟨.privateRow 14 10, 12292934712458400⟩, ⟨.privateRow 14 11, 19021415671658400⟩, ⟨.privateRow 14 13, 60391961455082400⟩, ⟨.privateRow 14 14, 57952406501589600⟩, ⟨.privateRow 14 17, 46224664189704000⟩, ⟨.privateRow 15 2, 492465437263800⟩, ⟨.privateRow 15 3, 357660815987475⟩, ⟨.privateRow 15 4, 1052670846066840⟩, ⟨.privateRow 15 5, 1922663434091400⟩, ⟨.privateRow 15 6, 3766137823047600⟩, ⟨.privateRow 15 7, 6711659756802000⟩, ⟨.privateRow 15 8, 11040519733916400⟩, ⟨.privateRow 15 9, 17273692742506200⟩, ⟨.privateRow 15 10, 26010625268027400⟩, ⟨.privateRow 15 11, 9511128365889150⟩, ⟨.privateRow 15 12, 52850535814276200⟩, ⟨.privateRow 15 13, 88752869152447500⟩, ⟨.privateRow 15 16, 151612861453653600⟩, ⟨.privateRow 16 0, 227086232373000⟩, ⟨.privateRow 16 1, 854912874816000⟩, ⟨.privateRow 16 2, 766416034258875⟩, ⟨.privateRow 16 3, 1952941598407800⟩, ⟨.privateRow 16 5, 14673264245640000⟩, ⟨.privateRow 16 6, 8212952070823500⟩, ⟨.privateRow 16 7, 19261041345819000⟩, ⟨.privateRow 16 8, 29407667092303500⟩, ⟨.privateRow 16 9, 43323006776049000⟩, ⟨.privateRow 16 10, 29436052871350125⟩, ⟨.privateRow 16 11, 60988873837320000⟩, ⟨.privateRow 17 0, 3811486566888000⟩, ⟨.privateRow 17 1, 794801813305500⟩, ⟨.privateRow 17 3, 9732267101700000⟩, ⟨.privateRow 17 5, 75140311111866000⟩, ⟨.privateRow 17 6, 12496624181496000⟩, ⟨.privateRow 17 7, 61767455205456000⟩, ⟨.privateRow 17 8, 88950518280624000⟩, ⟨.privateRow 18 0, 21361244925220200⟩, ⟨.privateRow 18 3, 45454511907604800⟩, ⟨.privateRow 18 5, 395124539208235200⟩, ⟨.privateRow 18 10, 680814617375692800⟩, ⟨.privateRow 19 0, 133417703243784960⟩, ⟨.privateRow 19 2, 105479808120086400⟩, ⟨.privateRow 19 3, 45553498214023800⟩, ⟨.privateRow 19 4, 1086545689295976000⟩, ⟨.privateRow 19 5, 592967569972377600⟩, ⟨.privateRow 19 10, 3148287191822092320⟩, ⟨.privateRow 20 0, 1358001622302811200⟩, ⟨.privateRow 20 2, 254276023929127200⟩, ⟨.privateRow 20 3, 4075528998919996800⟩, ⟨.privateRow 20 12, 75373281400837820400⟩, ⟨.privateRow 21 3, 58913798774963932800⟩, ⟨.privateRow 21 12, 542194721793492768000⟩, ⟨.hall 16 8, 77619712060800⟩, ⟨.hall 20 8, 213378481618848000⟩, ⟨.hall 17 9, 186634181375460⟩, ⟨.hall 18 9, 840432307590720⟩, ⟨.hall 17 15, 56620167271668000⟩, ⟨.hall 13 16, 49045001765760⟩, ⟨.hall 16 16, 2137282187040000⟩, ⟨.hall 7 17, 4343281242300⟩, ⟨.hall 14 17, 1157652855559200⟩, ⟨.hall 9 20, 41724370420200⟩, ⟨.hall 11 21, 374587474385124000⟩, ⟨.hall 10 22, 678816191020968000⟩, ⟨.hall 9 23, 1433777053956647400⟩, ⟨.hall 8 24, 3603508492180012416⟩, ⟨.hall 6 26, 597623678796144000⟩, ⟨.hall 4 28, 51448882326547305600⟩, ⟨.hall 3 29, 70039352806570667520⟩]
  caps := #[0, 4382921204267424000, 34573570097976000, 0, 0, 0, 3783969529912000, 350011395215300, 778656693850035, 757015331933380, 22194063390880, 1246809053850, 122841454010250, 245490141166400, 2217776428048740, 0, 75138826888125, 18705338438221500, 37257245902094400, 0, 0, 0, 0] }

theorem case_55_33_15_checked :
    (Witness.linear .positive case_55_33_15).check 55 33 15 = true := by
  change case_55_33_15.check 55 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_33_16 : Certificate := {
  objectiveScale := 32301360000000
  eta := 1203507980950707432000
  rows := #[⟨.count 2, 277356463024232592000⟩, ⟨.count 3, 62434543721674924800⟩, ⟨.count 4, 13564133163118137600⟩, ⟨.count 5, 3205044620105328000⟩, ⟨.count 6, 744842842183440000⟩, ⟨.count 7, 169027852296303000⟩, ⟨.count 8, 41259045241814400⟩, ⟨.count 9, 10173463210310400⟩, ⟨.count 10, 2515416727824000⟩, ⟨.count 11, 640499629770000⟩, ⟨.count 12, 139745373768000⟩, ⟨.path 11, 2841465987360⟩, ⟨.path 12, 26237329896960⟩, ⟨.privateRow 2 31, 32469092286334704000⟩, ⟨.privateRow 3 30, 49622944054476592800⟩, ⟨.privateRow 4 29, 41819655546853984800⟩, ⟨.privateRow 5 27, 11965385530883584800⟩, ⟨.privateRow 6 21, 24539731269768000⟩, ⟨.privateRow 6 22, 139447767879420000⟩, ⟨.privateRow 6 23, 295676367271084800⟩, ⟨.privateRow 7 20, 92088874042308000⟩, ⟨.privateRow 7 21, 107298244796242500⟩, ⟨.privateRow 7 22, 258408993358315800⟩, ⟨.privateRow 7 23, 288986154547340250⟩, ⟨.privateRow 8 17, 6177866934038800⟩, ⟨.privateRow 8 18, 20148225967294425⟩, ⟨.privateRow 8 19, 57745505712094200⟩, ⟨.privateRow 8 21, 347939506697622840⟩, ⟨.privateRow 8 23, 474255298288972200⟩, ⟨.privateRow 9 14, 289936361332800⟩, ⟨.privateRow 9 15, 3017723710201200⟩, ⟨.privateRow 9 16, 8065205843094400⟩, ⟨.privateRow 9 17, 16804381195602000⟩, ⟨.privateRow 9 18, 42896949749596800⟩, ⟨.privateRow 9 19, 22809550451688000⟩, ⟨.privateRow 9 21, 421073384787455400⟩, ⟨.privateRow 9 23, 85636741408218000⟩, ⟨.privateRow 10 12, 258528941470800⟩, ⟨.privateRow 10 13, 1289468676132000⟩, ⟨.privateRow 10 14, 3408389666201520⟩, ⟨.privateRow 10 16, 27984011097042000⟩, ⟨.privateRow 10 17, 22592834213320800⟩, ⟨.privateRow 10 18, 23197732045488000⟩, ⟨.privateRow 10 19, 16663238368096320⟩, ⟨.privateRow 10 20, 145813816623875400⟩, ⟨.privateRow 10 21, 142093096047302400⟩, ⟨.privateRow 11 10, 155869839972000⟩, ⟨.privateRow 11 11, 584213298669000⟩, ⟨.privateRow 11 12, 1477913195304000⟩, ⟨.privateRow 11 13, 3010348259919000⟩, ⟨.privateRow 11 14, 1152899333586000⟩, ⟨.privateRow 11 15, 20367888226686000⟩, ⟨.privateRow 11 16, 17958944164590000⟩, ⟨.privateRow 11 17, 18758875520385000⟩, ⟨.privateRow 11 18, 17421589929744000⟩, ⟨.privateRow 11 19, 61144423747407000⟩, ⟨.privateRow 12 8, 81518134698000⟩, ⟨.privateRow 12 9, 287552980638000⟩, ⟨.privateRow 12 10, 700667776809000⟩, ⟨.privateRow 12 11, 1429214049900000⟩, ⟨.privateRow 12 12, 3059259140737800⟩, ⟨.privateRow 12 13, 1394865860388000⟩, ⟨.privateRow 12 14, 15529204659969000⟩, ⟨.privateRow 12 15, 15932636244954000⟩, ⟨.privateRow 12 16, 16158058841925000⟩, ⟨.privateRow 12 17, 16033452550315200⟩, ⟨.privateRow 12 18, 31751313464871000⟩, ⟨.privateRow 12 19, 35180897846094000⟩, ⟨.privateRow 13 6, 40060340480160⟩, ⟨.privateRow 13 7, 149727186180000⟩, ⟨.privateRow 13 8, 362263007383200⟩, ⟨.privateRow 13 9, 718524130123800⟩, ⟨.privateRow 13 10, 1520683749093600⟩, ⟨.privateRow 13 11, 2825651457588960⟩, ⟨.privateRow 13 12, 939399456996000⟩, ⟨.privateRow 13 14, 35876630171210400⟩, ⟨.privateRow 13 16, 8105231678544000⟩, ⟨.privateRow 13 17, 9404863654586400⟩, ⟨.privateRow 14 4, 20185442877600⟩, ⟨.privateRow 14 6, 390732501416400⟩, ⟨.privateRow 14 7, 378865235548800⟩, ⟨.privateRow 14 8, 994133061721800⟩, ⟨.privateRow 14 9, 1937802516249600⟩, ⟨.privateRow 14 10, 3481988896386000⟩, ⟨.privateRow 14 11, 1917617073372000⟩, ⟨.privateRow 14 12, 946192634887500⟩, ⟨.privateRow 14 13, 28934390547691200⟩, ⟨.privateRow 14 14, 21440304576490800⟩, ⟨.privateRow 14 16, 25514399797286400⟩, ⟨.privateRow 14 17, 3518995541661600⟩, ⟨.privateRow 15 2, 12467479424400⟩, ⟨.privateRow 15 3, 30908959406325⟩, ⟨.privateRow 15 4, 51809303385840⟩, ⟨.privateRow 15 5, 590424204169800⟩, ⟨.privateRow 15 6, 619537823704800⟩, ⟨.privateRow 15 7, 1495404893182200⟩, ⟨.privateRow 15 8, 2797060118743800⟩, ⟨.privateRow 15 10, 11975013987136200⟩, ⟨.privateRow 15 12, 25484121632970000⟩, ⟨.privateRow 15 14, 94245832795514400⟩, ⟨.privateRow 16 0, 8410601199000⟩, ⟨.privateRow 16 1, 26716027338000⟩, ⟨.privateRow 16 2, 56771558093250⟩, ⟨.privateRow 16 3, 95880853668600⟩, ⟨.privateRow 16 4, 1178685682317000⟩, ⟨.privateRow 16 5, 1152899333586000⟩, ⟨.privateRow 16 6, 2655647328584250⟩, ⟨.privateRow 16 7, 4823862087681000⟩, ⟨.privateRow 16 8, 1195987490497800⟩, ⟨.privateRow 16 10, 39342689758622250⟩, ⟨.privateRow 16 11, 10089116895429000⟩, ⟨.privateRow 16 12, 25484121632970000⟩, ⟨.privateRow 16 13, 67323498357515400⟩, ⟨.privateRow 16 17, 484677715294773000⟩, ⟨.privateRow 17 0, 142485479136000⟩, ⟨.privateRow 17 1, 88311312589500⟩, ⟨.privateRow 17 2, 242225314531200⟩, ⟨.privateRow 17 3, 490217898456000⟩, ⟨.privateRow 17 4, 7220177644680000⟩, ⟨.privateRow 17 5, 3414704086794000⟩, ⟨.privateRow 17 6, 9175201308000000⟩, ⟨.privateRow 17 7, 7206203107303200⟩, ⟨.privateRow 17 9, 52456919678163000⟩, ⟨.privateRow 17 11, 154284068394456000⟩, ⟨.privateRow 17 12, 36616393379966400⟩, ⟨.privateRow 17 13, 103046685890148000⟩, ⟨.privateRow 18 0, 1243927917332100⟩, ⟨.privateRow 18 1, 228768352612800⟩, ⟨.privateRow 18 2, 1421631905522400⟩, ⟨.privateRow 18 3, 18952578135691200⟩, ⟨.privateRow 18 4, 12525067305550800⟩, ⟨.privateRow 18 5, 22897632384244800⟩, ⟨.privateRow 18 6, 23608893989640960⟩, ⟨.privateRow 18 8, 67686836329312200⟩, ⟨.privateRow 18 10, 436261248432609600⟩, ⟨.privateRow 18 11, 202871775097031040⟩, ⟨.privateRow 18 14, 767289054663331200⟩, ⟨.privateRow 19 0, 11324033454333600⟩, ⟨.privateRow 19 2, 62717723747078400⟩, ⟨.privateRow 19 3, 56620167271668000⟩, ⟨.privateRow 19 4, 78613124806944000⟩, ⟨.privateRow 19 6, 206920974938277600⟩, ⟨.privateRow 19 8, 47207983621312800⟩, ⟨.privateRow 19 10, 697972243821652800⟩, ⟨.privateRow 20 0, 124343769943364400⟩, ⟨.privateRow 20 1, 215156635632338400⟩, ⟨.privateRow 20 8, 7230566936856463200⟩, ⟨.privateRow 20 9, 3106079430765030720⟩, ⟨.privateRow 21 0, 3280010249499984000⟩, ⟨.privateRow 21 8, 97915828906862366400⟩, ⟨.hall 19 4, 644825081815200⟩, ⟨.hall 18 6, 3006304113496320⟩, ⟨.hall 20 6, 12766233943008000⟩, ⟨.hall 12 8, 1654707740400⟩, ⟨.hall 19 8, 3132938023768800⟩, ⟨.hall 13 9, 1536742427220⟩, ⟨.hall 19 9, 14127531337951200⟩, ⟨.hall 20 9, 176174028413510400⟩, ⟨.hall 16 13, 74168780657400⟩, ⟨.hall 19 13, 92209986699573600⟩, ⟨.hall 7 18, 603966791610⟩, ⟨.hall 9 18, 7423544700000⟩, ⟨.hall 12 19, 172019900566800⟩, ⟨.hall 8 20, 41155963849728⟩, ⟨.hall 11 20, 641331447471000⟩, ⟨.hall 9 21, 829807200904500⟩, ⟨.hall 11 21, 1409099185494000⟩, ⟨.hall 8 22, 1596914267444496⟩, ⟨.hall 10 22, 21921796024128000⟩, ⟨.hall 7 25, 1507148033363973000⟩, ⟨.hall 6 26, 4706662144039856000⟩, ⟨.hall 5 27, 10063315573979382000⟩, ⟨.hall 4 28, 2287525754850336000⟩]
  caps := #[0, 1991821725685864800, 196575509558937600, 0, 0, 21410651283840, 68959081900800, 1362118270470100, 0, 251799745069184, 60632204613120, 125422545930480, 47998756128960, 83083673933820, 343114100298840, 32301360000000, 138871228222350, 182227336734300, 23022200865959100, 3283362928553760, 264242153804737680, 0, 0] }

theorem case_55_33_16_checked :
    (Witness.linear .positive case_55_33_16).check 55 33 16 = true := by
  change case_55_33_16.check 55 33 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_33_17 : Certificate := {
  objectiveScale := 272129457600000
  eta := 9932021494671708432000
  rows := #[⟨.count 2, 2047039350794364326400⟩, ⟨.count 3, 454035268327849528320⟩, ⟨.count 4, 96505472013004454400⟩, ⟨.count 5, 22637086027741785600⟩, ⟨.count 6, 5241271355826105600⟩, ⟨.count 7, 1208946544825219200⟩, ⟨.count 8, 304864780868968320⟩, ⟨.count 9, 78844339879905600⟩, ⟨.count 10, 20794111616678400⟩, ⟨.count 11, 6353756327318400⟩, ⟨.count 12, 1732842634723200⟩, ⟨.path 12, 230909225863680⟩, ⟨.privateRow 2 31, 97016082976036224000⟩, ⟨.privateRow 3 28, 3072175960907813760⟩, ⟨.privateRow 3 29, 46082639413617206400⟩, ⟨.privateRow 4 26, 5390136978504117840⟩, ⟨.privateRow 4 27, 16811865957821014080⟩, ⟨.privateRow 5 24, 3016008754974319104⟩, ⟨.privateRow 5 25, 6042229729209273600⟩, ⟨.privateRow 5 26, 12220622381893685760⟩, ⟨.privateRow 6 21, 204172871072227200⟩, ⟨.privateRow 6 22, 1101317763401856000⟩, ⟨.privateRow 6 23, 2280228369225206400⟩, ⟨.privateRow 6 24, 4308905749309761600⟩, ⟨.privateRow 6 25, 6365116073479363200⟩, ⟨.privateRow 7 19, 143374677579233100⟩, ⟨.privateRow 7 20, 415541852530318800⟩, ⟨.privateRow 7 21, 830681438020434000⟩, ⟨.privateRow 7 22, 1588337999342574480⟩, ⟨.privateRow 7 23, 2287424479611070800⟩, ⟨.privateRow 7 24, 2866554928490853600⟩, ⟨.privateRow 8 16, 1138862687154192⟩, ⟨.privateRow 8 17, 69548494869373520⟩, ⟨.privateRow 8 18, 167982246355243320⟩, ⟨.privateRow 8 19, 313875562569528960⟩, ⟨.privateRow 8 20, 595639786185323880⟩, ⟨.privateRow 8 21, 871229955672956880⟩, ⟨.privateRow 8 22, 1072721046477160080⟩, ⟨.privateRow 8 23, 1084693705495960560⟩, ⟨.privateRow 9 14, 3071857397918400⟩, ⟨.privateRow 9 15, 27733183678392192⟩, ⟨.privateRow 9 16, 70556645599760320⟩, ⟨.privateRow 9 17, 127308578956879320⟩, ⟨.privateRow 9 18, 235531821672987840⟩, ⟨.privateRow 9 19, 349501523552301120⟩, ⟨.privateRow 9 20, 437723751053901312⟩, ⟨.privateRow 9 21, 434332192941606960⟩, ⟨.privateRow 10 12, 2223814714561440⟩, ⟨.privateRow 10 13, 11515526963478720⟩, ⟨.privateRow 10 14, 29458324790294400⟩, ⟨.privateRow 10 15, 55489471925247360⟩, ⟨.privateRow 10 16, 101587899460647600⟩, ⟨.privateRow 10 17, 151896034380879360⟩, ⟨.privateRow 10 18, 196302189803559840⟩, ⟨.privateRow 10 19, 4921273082613888⟩, ⟨.privateRow 11 10, 1188552319970400⟩, ⟨.privateRow 11 11, 5186494274761800⟩, ⟨.privateRow 11 12, 12970064568988800⟩, ⟨.privateRow 11 13, 25212860335222560⟩, ⟨.privateRow 11 14, 48407279897776800⟩, ⟨.privateRow 11 15, 73970719969746600⟩, ⟨.privateRow 11 16, 6910741459908000⟩, ⟨.privateRow 12 8, 556985132589600⟩, ⟨.privateRow 12 9, 2488184296012800⟩, ⟨.privateRow 12 10, 6269520921463800⟩, ⟨.privateRow 12 11, 12418705548849600⟩, ⟨.privateRow 12 12, 24866291808277920⟩, ⟨.privateRow 12 13, 4444420461280800⟩, ⟨.privateRow 13 6, 242597968861248⟩, ⟨.privateRow 13 7, 1250122186478880⟩, ⟨.privateRow 13 8, 3359048799617280⟩, ⟨.privateRow 13 9, 6859168762446000⟩, ⟨.privateRow 13 10, 1937633127917760⟩, ⟨.privateRow 14 4, 93862309380840⟩, ⟨.privateRow 14 5, 650778678373824⟩, ⟨.privateRow 14 6, 1948760328097440⟩, ⟨.privateRow 14 7, 539106597469440⟩, ⟨.privateRow 15 2, 25766124143760⟩, ⟨.privateRow 15 3, 355894589735685⟩, ⟨.privateRow 15 4, 292016073629280⟩, ⟨.privateRow 16 1, 110426246330400⟩, ⟨.hall 7 25, 1176094736541925200⟩, ⟨.hall 6 26, 6128443998566489600⟩, ⟨.hall 5 27, 17736132587927925600⟩, ⟨.hall 4 28, 41153482892901899520⟩, ⟨.hall 3 29, 82172622280702681728⟩, ⟨.hall 2 30, 69319556061909753600⟩, ⟨.assumptionRow 17, 347097235605120⟩]
  caps := #[0, 3845968551039888000, 1265360199488985600, 0, 178479903305431728, 31628560807299456, 0, 3872946232921480, 2064583990971320, 1511999925380672, 562326870964320, 1209021144494880, 468654507048960, 769162249215360, 2456866502379432, 269798863173840, 126244742944320, 3734844628394880, 272129457600000, 0, 0, 0, 0] }

theorem case_55_33_17_checked :
    (Witness.linear .conditional case_55_33_17).check 55 33 17 = true := by
  change case_55_33_17.check 55 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_33_18 : Certificate := {
  objectiveScale := 20532319004624427000000
  eta := 947141010448624021461847416000
  rows := #[⟨.count 2, 181421338545001283939722512000⟩, ⟨.count 3, 37044412982233502391043898400⟩, ⟨.count 4, 7212044978325249511511462400⟩, ⟨.count 5, 1529181134457523318515744000⟩, ⟨.count 6, 321107119205512762506384000⟩, ⟨.count 7, 68640569048409690682350000⟩, ⟨.count 8, 15619542823460338501939200⟩, ⟨.count 9, 4079210960591204474836800⟩, ⟨.count 10, 1206867148103906649360000⟩, ⟨.count 11, 442517954304765771432000⟩, ⟨.count 12, 120686714810390664936000⟩, ⟨.path 10, 70327331688109335840000⟩, ⟨.privateRow 2 31, 8108216247821286433060224000⟩, ⟨.privateRow 3 28, 253381757744415201033132000⟩, ⟨.privateRow 3 29, 3910525127855474602611337200⟩, ⟨.privateRow 4 26, 431415782264833250180095800⟩, ⟨.privateRow 4 27, 1389598902998319155139597600⟩, ⟨.privateRow 5 24, 226650723184711983333496320⟩, ⟨.privateRow 5 25, 485129751377318928761680800⟩, ⟨.privateRow 5 26, 1044347736013238793497961600⟩, ⟨.privateRow 6 21, 12227671438646406575976000⟩, ⟨.privateRow 6 22, 78824069345327191881996000⟩, ⟨.privateRow 6 23, 176870403445121199152539200⟩, ⟨.privateRow 6 24, 362422204575603166802808000⟩, ⟨.privateRow 6 25, 581955808694030097086760000⟩, ⟨.privateRow 7 19, 7673035040054368994134125⟩, ⟨.privateRow 7 20, 28025897648201017923501000⟩, ⟨.privateRow 7 21, 62353964549848993615093500⟩, ⟨.privateRow 7 22, 131096949685410279708937800⟩, ⟨.privateRow 7 23, 208977846767146360656002250⟩, ⟨.privateRow 7 24, 290491246344237963963939000⟩, ⟨.privateRow 8 17, 3294747314323665152752800⟩, ⟨.privateRow 8 18, 10490566969565281059285825⟩, ⟨.privateRow 8 19, 22684073771236345396929000⟩, ⟨.privateRow 8 20, 48246693311137744806282900⟩, ⟨.privateRow 8 21, 79092239695514206250249160⟩, ⟨.privateRow 8 22, 109855417397032576065396600⟩, ⟨.privateRow 8 23, 128668017802893009807966600⟩, ⟨.privateRow 9 15, 1197614499968443365048240⟩, ⟨.privateRow 9 16, 4017228647799695195067200⟩, ⟨.privateRow 9 17, 8720620867674145463833800⟩, ⟨.privateRow 9 18, 18590543236149781077324000⟩, ⟨.privateRow 9 19, 31346586220668450910978800⟩, ⟨.privateRow 9 20, 44648184240453815816034240⟩, ⟨.privateRow 9 21, 53391467391242356860283800⟩, ⟨.privateRow 9 22, 48596070175818010004359200⟩, ⟨.privateRow 10 13, 392780399110180527700800⟩, ⟨.privateRow 10 14, 1539962480980584884583360⟩, ⟨.privateRow 10 15, 3530756889952873564183200⟩, ⟨.privateRow 10 16, 7665114974394937106747700⟩, ⟨.privateRow 10 17, 13266918149513659524036000⟩, ⟨.privateRow 10 18, 19583430923232725230281600⟩, ⟨.privateRow 10 19, 24453542154881356529332320⟩, ⟨.privateRow 10 20, 5029618839723030961207800⟩, ⟨.privateRow 11 11, 118172408251840859416500⟩, ⟨.privateRow 11 12, 583319121583554880524000⟩, ⟨.privateRow 11 13, 1482435146920965334297200⟩, ⟨.privateRow 11 14, 3394872588833026296996000⟩, ⟨.privateRow 11 15, 6118565010230951731703250⟩, ⟨.privateRow 11 16, 9416437248420243071316000⟩, ⟨.privateRow 11 17, 5147623627537635166923000⟩, ⟨.privateRow 12 9, 30945311489843760240000⟩, ⟨.privateRow 12 10, 217068466221466543183500⟩, ⟨.privateRow 12 11, 635433839342587213110000⟩, ⟨.privateRow 12 12, 1598093248614256388194200⟩, ⟨.privateRow 12 13, 3095390740970205017340000⟩, ⟨.privateRow 12 14, 3115225826043209038660500⟩, ⟨.privateRow 13 7, 6034335740519533246800⟩, ⟨.privateRow 13 8, 78910544299101588612000⟩, ⟨.privateRow 13 9, 275567998817058684937200⟩, ⟨.privateRow 13 10, 786657950173182788719200⟩, ⟨.privateRow 13 11, 1542376215276792697882080⟩, ⟨.privateRow 14 6, 24903607818017121336000⟩, ⟨.privateRow 14 7, 119345751312497435325600⟩, ⟨.privateRow 14 8, 399495375414024654765000⟩, ⟨.privateRow 14 9, 231377156272849981867200⟩, ⟨.privateRow 15 4, 6101383915414194727320⟩, ⟨.privateRow 15 5, 47939445049682958571800⟩, ⟨.privateRow 15 6, 143147853400102260910200⟩, ⟨.privateRow 16 3, 17432525472611984935200⟩, ⟨.privateRow 16 4, 28016558795269261503000⟩, ⟨.hall 7 24, 2501332736707688523019380⟩, ⟨.hall 8 24, 4334423133510243934288128⟩, ⟨.hall 7 25, 153702074230708161212554500⟩, ⟨.hall 6 26, 729841733120021769287040000⟩, ⟨.hall 5 27, 1814844193836043213080666000⟩, ⟨.hall 4 28, 3860599877705833930514246400⟩, ⟨.hall 3 29, 7305840681630638296455306000⟩, ⟨.hall 2 30, 6113856606220082915251056000⟩, ⟨.assumptionRow 18, 20889707708037228180120⟩]
  caps := #[0, 0, 441930549925252735755408000, 0, 14289156459128133549766800, 551362785404194432468800, 580857860425825955200800, 593437865246807794120050, 0, 218200621431278947932328, 100699719537631930272180, 5815402556161652213760, 194573504555790806384400, 73277102868173852127480, 156162859454296940007360, 207400871200413757786920, 20889707708037228180120, 1822015560860381985298200, 266562758356704749819880, 20532319004624427000000, 0, 0, 0] }

theorem case_55_33_18_checked :
    (Witness.linear .conditional case_55_33_18).check 55 33 18 = true := by
  change case_55_33_18.check 55 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_33_19 : Certificate := {
  objectiveScale := 2256298791716970000000
  eta := 62214966978474870899827488000
  rows := #[⟨.count 2, 13175851402709590453722864000⟩, ⟨.count 3, 2728726621862932934202960000⟩, ⟨.count 4, 549028003015429212926851200⟩, ⟨.count 5, 118313209419119648525592000⟩, ⟨.count 6, 25505125729929227189808000⟩, ⟨.count 7, 5596846399331867086407000⟩, ⟨.count 8, 1295370738964859803646400⟩, ⟨.count 9, 325854129988054795327200⟩, ⟨.count 10, 120686714810390664936000⟩, ⟨.count 11, 51059763958242204396000⟩, ⟨.count 12, 18567186893906256144000⟩, ⟨.count 13, 12068671481039066493600⟩, ⟨.path 10, 5414315465081997936000⟩, ⟨.privateRow 2 31, 1442326928698978836650136000⟩, ⟨.privateRow 3 28, 92690078901375817130068800⟩, ⟨.privateRow 3 29, 426850807277130223278891600⟩, ⟨.privateRow 4 26, 53240944238603841836516400⟩, ⟨.privateRow 4 27, 149088321695769268084272000⟩, ⟨.privateRow 5 24, 21638323387404310285258560⟩, ⟨.privateRow 5 25, 50140636631474694977271600⟩, ⟨.privateRow 5 26, 114164268356637996111014400⟩, ⟨.privateRow 6 21, 630252844009817916888000⟩, ⟨.privateRow 6 22, 6977480067371104739448000⟩, ⟨.privateRow 6 23, 17258200217885865085848000⟩, ⟨.privateRow 6 24, 38841007716477395665236000⟩, ⟨.privateRow 6 25, 67897451776660525939920000⟩, ⟨.privateRow 7 19, 355145801395160029629375⟩, ⟨.privateRow 7 20, 2265749395904596173858000⟩, ⟨.privateRow 7 21, 5818105376484249972123000⟩, ⟨.privateRow 7 22, 13612455707988647082573000⟩, ⟨.privateRow 7 23, 24163743180942905945154750⟩, ⟨.privateRow 7 24, 37159774730993759041197000⟩, ⟨.privateRow 8 17, 128024765062750838081800⟩, ⟨.privateRow 8 18, 752699573411193445687650⟩, ⟨.privateRow 8 19, 1993342239618285815859600⟩, ⟨.privateRow 8 20, 4846689069218762888522400⟩, ⟨.privateRow 8 21, 8959178273949351011523960⟩, ⟨.privateRow 8 22, 14002089414345248611244850⟩, ⟨.privateRow 8 23, 18704652844280028758932800⟩, ⟨.privateRow 9 15, 33524087447330740260000⟩, ⟨.privateRow 9 16, 248227243054457836769600⟩, ⟨.privateRow 9 17, 701826770709869047343100⟩, ⟨.privateRow 9 18, 1779841694132285187175200⟩, ⟨.privateRow 9 19, 3450522573995595325827600⟩, ⟨.privateRow 9 20, 5583772005227408097705600⟩, ⟨.privateRow 9 21, 7668635003576906834475000⟩, ⟨.privateRow 9 22, 8508860381965172954524800⟩, ⟨.privateRow 10 13, 4473004115350143525600⟩, ⟨.privateRow 10 14, 77796513085467213243360⟩, ⟨.privateRow 10 15, 251379080335830812349600⟩, ⟨.privateRow 10 16, 680023219989316631274000⟩, ⟨.privateRow 10 17, 1393467376387664523607200⟩, ⟨.privateRow 10 18, 2364840704053860157540800⟩, ⟨.privateRow 10 19, 3394081764206063623123200⟩, ⟨.privateRow 10 20, 4025598208435050160221000⟩, ⟨.privateRow 10 21, 953425047002086252994400⟩, ⟨.privateRow 11 12, 19481480187924367242000⟩, ⟨.privateRow 11 13, 89045133812025420090600⟩, ⟨.privateRow 11 14, 269138250763057814754000⟩, ⟨.privateRow 11 15, 594826909293840528863250⟩, ⟨.privateRow 11 16, 1071923486214266537742000⟩, ⟨.privateRow 11 17, 1631591548302012258654000⟩, ⟨.privateRow 11 18, 1278660270760344173116800⟩, ⟨.privateRow 12 10, 3223469946858725025000⟩, ⟨.privateRow 12 11, 27921110594245392762000⟩, ⟨.privateRow 12 12, 107999137099554723237600⟩, ⟨.privateRow 12 13, 267676944387148526076000⟩, ⟨.privateRow 12 14, 523265876473576833308250⟩, ⟨.privateRow 12 15, 856853571359852404074000⟩, ⟨.privateRow 12 16, 10057226234199222078000⟩, ⟨.privateRow 13 7, 66311381763950914800⟩, ⟨.privateRow 13 9, 7194784921388674255800⟩, ⟨.privateRow 13 10, 40172640734088081475200⟩, ⟨.privateRow 13 11, 114373871266462537847040⟩, ⟨.privateRow 13 12, 294599365383312597484800⟩, ⟨.privateRow 13 13, 181958431560281310211200⟩, ⟨.privateRow 14 7, 928359344695312807200⟩, ⟨.privateRow 14 8, 13074394104458988701400⟩, ⟨.privateRow 14 9, 55223314958693910319200⟩, ⟨.privateRow 14 10, 139460203780895879481600⟩, ⟨.privateRow 15 6, 3068743389409506223800⟩, ⟨.privateRow 15 7, 22097960975698846288050⟩, ⟨.privateRow 15 8, 39253658756510903140800⟩, ⟨.privateRow 16 4, 718373302442801577000⟩, ⟨.privateRow 16 5, 6575878691591799051000⟩, ⟨.privateRow 16 6, 10476277327290856331250⟩, ⟨.privateRow 17 3, 1915662139847470872000⟩, ⟨.privateRow 17 4, 2063020765989584016000⟩, ⟨.hall 8 24, 8875354645696045228577856⟩, ⟨.hall 7 25, 40529074458248372786328000⟩, ⟨.hall 6 26, 107908822634910290337344000⟩, ⟨.hall 5 27, 237432433683580120420578000⟩, ⟨.hall 4 28, 465829078791659206947523200⟩, ⟨.hall 3 29, 836419679282461871307831120⟩, ⟨.hall 2 30, 715085655437505927150576000⟩, ⟨.assumptionRow 19, 1698923044900335183930⟩]
  caps := #[0, 204570448488187764532149600, 14434617859147624531793400, 0, 295900880027340627159120, 99148858472547344607300, 12503094486210199625160, 27968257241645649192550, 11442013830511792042900, 7475678969259021810000, 0, 0, 7345242883852363366470, 0, 25123454656872739188840, 13116724405123322688180, 1698923044900335183930, 1698923044900335183930, 179281968625922607424980, 27632961247420274816070, 2256298791716970000000, 0, 0] }

theorem case_55_33_19_checked :
    (Witness.linear .conditional case_55_33_19).check 55 33 19 = true := by
  change case_55_33_19.check 55 33 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_33_20 : Certificate := {
  objectiveScale := 19554589528213740000000
  eta := 886836152105453203615962000000
  rows := #[⟨.count 2, 173988806984498438042750640000⟩, ⟨.count 3, 34839991689857090142055650000⟩, ⟨.count 4, 6603928759738653029031945600⟩, ⟨.count 5, 1321734081333440697786864000⟩, ⟨.count 6, 251551342569790942614936000⟩, ⟨.count 7, 44845171778294331245802000⟩, ⟨.count 8, 7321660698497033672784000⟩, ⟨.count 9, 1098249104774555050917600⟩, ⟨.count 10, 181030072215585997404000⟩, ⟨.count 11, 55314744288095721429000⟩, ⟨.path 10, 76987858923194899680000⟩, ⟨.privateRow 2 31, 12838009059050370185678688000⟩, ⟨.privateRow 3 28, 591224101403635469077308000⟩, ⟨.privateRow 3 29, 4548202551512252858544719400⟩, ⟨.privateRow 4 26, 492760839402954825167064600⟩, ⟨.privateRow 4 27, 1564298957022100162167704400⟩, ⟨.privateRow 5 24, 222205429189195927175020320⟩, ⟨.privateRow 5 25, 519210338676275359309996800⟩, ⟨.privateRow 5 26, 1219689888058594341971181600⟩, ⟨.privateRow 6 21, 9650148029481634517700000⟩, ⟨.privateRow 6 22, 71502408646830158209212000⟩, ⟨.privateRow 6 23, 177410811734772170685530400⟩, ⟨.privateRow 6 24, 407659608177031267709652000⟩, ⟨.privateRow 6 25, 738848537947537961503560000⟩, ⟨.privateRow 7 19, 5695532931754946953047375⟩, ⟨.privateRow 7 20, 23263082653005243467991000⟩, ⟨.privateRow 7 21, 58480675296403018212303750⟩, ⟨.privateRow 7 22, 140196727982113735845112200⟩, ⟨.privateRow 7 23, 258415399474631911683171000⟩, ⟨.privateRow 7 24, 417018695290139827121737500⟩, ⟨.privateRow 8 17, 2243953417780109394158800⟩, ⟨.privateRow 8 18, 7870785250884311198242800⟩, ⟨.privateRow 8 19, 19585442368479565074697200⟩, ⟨.privateRow 8 20, 48592438399677882507497700⟩, ⟨.privateRow 8 21, 93820980467324072321999640⟩, ⟨.privateRow 8 22, 154784483204163852488699250⟩, ⟨.privateRow 8 23, 220798914925647350190498600⟩, ⟨.privateRow 9 15, 720834928292505577070520⟩, ⟨.privateRow 9 16, 2682671975507511015028000⟩, ⟨.privateRow 9 17, 6799774467160712373786450⟩, ⟨.privateRow 9 18, 17324194778603610457388400⟩, ⟨.privateRow 9 19, 35146876773697863626852400⟩, ⟨.privateRow 9 20, 60433336055903968174857840⟩, ⟨.privateRow 9 21, 89169546858094379441664900⟩, ⟨.privateRow 9 22, 108781864370010887993137200⟩, ⟨.privateRow 10 13, 195293047602268530532800⟩, ⟨.privateRow 10 14, 887650787430423340604280⟩, ⟨.privateRow 10 15, 2431166821680425283655200⟩, ⟨.privateRow 10 16, 6454476366453205749108450⟩, ⟨.privateRow 10 17, 13748802960792290821887600⟩, ⟨.privateRow 10 18, 24867497586680996510062800⟩, ⟨.privateRow 10 19, 38484579618737375234791680⟩, ⟨.privateRow 10 20, 50092529565987775364998500⟩, ⟨.privateRow 10 21, 41268822129413087874865200⟩, ⟨.privateRow 11 11, 42324160402255059578250⟩, ⟨.privateRow 11 12, 274287988205433329400000⟩, ⟨.privateRow 11 13, 872967237128492476370400⟩, ⟨.privateRow 11 14, 2514306558549805519500000⟩, ⟨.privateRow 11 15, 5693018625196397147527875⟩, ⟨.privateRow 11 16, 10888384145125543502589000⟩, ⟨.privateRow 11 17, 17859119485379268605008500⟩, ⟨.privateRow 11 18, 24984161410997707486167600⟩, ⟨.privateRow 11 19, 6903028656498491053787250⟩, ⟨.privateRow 12 9, 5415429510722658042000⟩, ⟨.privateRow 12 10, 74591094570310897078500⟩, ⟨.privateRow 12 11, 302631080319994773438000⟩, ⟨.privateRow 12 12, 1006225484731632168903900⟩, ⟨.privateRow 12 13, 2504249332315606297422000⟩, ⟨.privateRow 12 14, 5131699686000153065299500⟩, ⟨.privateRow 12 15, 8989723506769218934578000⟩, ⟨.privateRow 12 16, 9231695580808702599097500⟩, ⟨.privateRow 13 8, 13461210498082035704400⟩, ⟨.privateRow 13 9, 94537926601472687533200⟩, ⟨.privateRow 13 10, 398814734850700060947600⟩, ⟨.privateRow 13 11, 1153764993587334756788160⟩, ⟨.privateRow 13 12, 2612867375644957895864400⟩, ⟨.privateRow 13 13, 4953435350998971853966950⟩, ⟨.privateRow 13 14, 1016354548296075671139600⟩, ⟨.privateRow 14 7, 20784934217345058961200⟩, ⟨.privateRow 14 8, 145997400833125373832300⟩, ⟨.privateRow 14 9, 537238739565042081184800⟩, ⟨.privateRow 14 10, 1417264320923354375231760⟩, ⟨.privateRow 14 11, 1596044554381363954067200⟩, ⟨.privateRow 15 6, 38720321001667005000300⟩, ⟨.privateRow 15 7, 236428626722300045683650⟩, ⟨.privateRow 15 8, 791793230841251179386300⟩, ⟨.privateRow 15 9, 196769631272107779956070⟩, ⟨.privateRow 16 5, 77943503315043971104500⟩, ⟨.privateRow 16 6, 321412188401283472242750⟩, ⟨.privateRow 17 4, 113981897320924516884000⟩, ⟨.privateRow 18 3, 22796379464184903376800⟩, ⟨.hall 8 24, 156551749055263573991467488⟩, ⟨.hall 7 25, 537358854846543710530299750⟩, ⟨.hall 6 26, 1304572728479291565950656000⟩, ⟨.hall 5 27, 2730998118245257072789434000⟩, ⟨.hall 4 28, 5198602713156197757966153600⟩, ⟨.hall 3 29, 9147926060432536807966175640⟩, ⟨.hall 2 30, 7694086923335790620618976000⟩, ⟨.assumptionRow 20, 6741053648061122590200⟩]
  caps := #[0, 1025836857004711570666848000, 49479716355256199131119000, 10181199752405150502033000, 1896465518804636983082880, 364746290700039306938880, 0, 0, 297946280584397758443130, 33683900689799043684000, 10214915335216807683390, 26510009777926271502750, 55430922683199068603400, 12716699585779187113500, 153157981015178070147580, 7409625064030750360800, 6741053648061122590200, 6741053648061122590200, 1290597162821183934116400, 1418069696247663386327400, 227914020690503757409800, 19554589528213740000000, 0] }

theorem case_55_33_20_checked :
    (Witness.linear .conditional case_55_33_20).check 55 33 20 = true := by
  change case_55_33_20.check 55 33 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_33_21 : Certificate := {
  objectiveScale := 5546018821956307695000000
  eta := 298951894722392077872357812160000
  rows := #[⟨.count 2, 52039774266490472814817841376000⟩, ⟨.count 3, 9549852192520858043144763444000⟩, ⟨.count 4, 1813191942927791550002771692800⟩, ⟨.count 5, 376013939802136141759068816000⟩, ⟨.count 6, 75904702412847104804847840000⟩, ⟨.count 7, 14568805785691621728672408000⟩, ⟨.count 8, 2570965726886756775648072000⟩, ⟨.count 9, 404008899939347493316125600⟩, ⟨.count 10, 56504741250258390673584000⟩, ⟨.path 4, 24565210846911528196324521600⟩, ⟨.path 10, 11354702528943022721472000⟩, ⟨.path 11, 4138033374719072748279360⟩, ⟨.privateRow 2 31, 6129304719837403712991463080000⟩, ⟨.privateRow 3 30, 9344223905145667725031501456800⟩, ⟨.privateRow 6 21, 2116237094920391631655896000⟩, ⟨.privateRow 6 25, 606775117531802501241047088000⟩, ⟨.privateRow 7 19, 1260614891382717794011963875⟩, ⟨.privateRow 7 20, 5397716309254593944791743000⟩, ⟨.privateRow 7 21, 12992558941231288705507221000⟩, ⟨.privateRow 7 22, 29480407001634811027431225600⟩, ⟨.privateRow 7 24, 322880648113143168395675328000⟩, ⟨.privateRow 7 25, 85966666492775929685732407500⟩, ⟨.privateRow 8 17, 506258065973379883599836400⟩, ⟨.privateRow 8 18, 2054094492210565048877157525⟩, ⟨.privateRow 8 19, 5439837006254042511014095200⟩, ⟨.privateRow 8 20, 13734432186364021497316251300⟩, ⟨.privateRow 8 22, 91110383339415336818122751550⟩, ⟨.privateRow 8 23, 96344560091260018725952564800⟩, ⟨.privateRow 9 15, 167724906944516989649421840⟩, ⟨.privateRow 9 16, 682870261850344921362609600⟩, ⟨.privateRow 9 17, 1883844529641427137394509900⟩, ⟨.privateRow 9 18, 5165250870797429712526512000⟩, ⟨.privateRow 9 19, 11132689687217575371377683200⟩, ⟨.privateRow 9 20, 10954762535325095061189975360⟩, ⟨.privateRow 9 21, 25507652818897894009822657200⟩, ⟨.privateRow 9 22, 1360299326395109405104800⟩, ⟨.privateRow 10 13, 48542709528631071987760800⟩, ⟨.privateRow 10 14, 218390824932248679953402160⟩, ⟨.privateRow 10 15, 639131406586256018952316800⟩, ⟨.privateRow 10 16, 1857946523235058708335783900⟩, ⟨.privateRow 10 17, 4333913653894818564663892800⟩, ⟨.privateRow 10 18, 8552463461070359581702551600⟩, ⟨.privateRow 10 19, 11017294448975381013535408320⟩, ⟨.privateRow 10 20, 17541896921142717384614152800⟩, ⟨.privateRow 10 21, 15013309750193654401971268800⟩, ⟨.privateRow 11 10, 181104939904674329082000⟩, ⟨.privateRow 11 11, 12164215130263959103341000⟩, ⟨.privateRow 11 12, 66778330568487188977872000⟩, ⟨.privateRow 11 13, 216836944547866574209878600⟩, ⟨.privateRow 11 14, 677533702954487184465660000⟩, ⟨.privateRow 11 15, 1701322443581998731687443250⟩, ⟨.privateRow 11 16, 3608231334123642947298864000⟩, ⟨.privateRow 11 17, 6584764325837403152037591000⟩, ⟨.privateRow 11 18, 8975778147603545358498818400⟩, ⟨.privateRow 11 19, 11763580819038168708356769000⟩, ⟨.privateRow 12 9, 2716574098570114936230000⟩, ⟨.privateRow 12 10, 19031110768316194081033500⟩, ⟨.privateRow 12 11, 72343191449194454726028000⟩, ⟨.privateRow 12 12, 252623280673030221636481800⟩, ⟨.privateRow 12 13, 692967868388585541177426000⟩, ⟨.privateRow 12 14, 1587135778972101567201242250⟩, ⟨.privateRow 12 15, 3110115132982972253325186000⟩, ⟨.privateRow 12 16, 5296534704138803870222478000⟩, ⟨.privateRow 12 17, 7195407925376653899025309200⟩, ⟨.privateRow 12 18, 2524467033566231641656268500⟩, ⟨.privateRow 13 7, 605407941967054185788400⟩, ⟨.privateRow 13 8, 4998496341369011482663200⟩, ⟨.privateRow 13 9, 22837332921979432897240200⟩, ⟨.privateRow 13 10, 94517021727704944399449600⟩, ⟨.privateRow 13 11, 294107178207594923456004720⟩, ⟨.privateRow 13 12, 740526025607553019994359200⟩, ⟨.privateRow 13 13, 1572950734554067950375894600⟩, ⟨.privateRow 13 15, 10442076183047750596478323200⟩, ⟨.privateRow 14 5, 272059865279021881020960⟩, ⟨.privateRow 14 6, 1165970851195808061518400⟩, ⟨.privateRow 14 7, 6592219812530145578584800⟩, ⟨.privateRow 14 8, 34347557991476512478896200⟩, ⟨.privateRow 14 9, 127991800256267112207588000⟩, ⟨.privateRow 14 10, 366872728328761006556764560⟩, ⟨.privateRow 14 11, 861069473608104253431338400⟩, ⟨.privateRow 14 12, 1726729957442792001104905500⟩, ⟨.privateRow 14 13, 780034499449995593155809600⟩, ⟨.privateRow 14 14, 6957931054510984607111052000⟩, ⟨.privateRow 15 4, 476104764238288291786680⟩, ⟨.privateRow 15 5, 2040448989592664107657200⟩, ⟨.privateRow 15 6, 11536384671927754762523400⟩, ⟨.privateRow 15 7, 54752047887403153555468200⟩, ⟨.privateRow 15 8, 189576260669427519820514400⟩, ⟨.privateRow 15 9, 509908202499206760503534280⟩, ⟨.privateRow 15 10, 1135509862708317575911231800⟩, ⟨.privateRow 15 11, 2186213564286690049847961225⟩, ⟨.privateRow 15 12, 1761927702513265456961992200⟩, ⟨.privateRow 15 13, 5713257170859459501440160000⟩, ⟨.privateRow 15 15, 860559361360706087404424100⟩, ⟨.privateRow 16 3, 1020224494796332053828600⟩, ⟨.privateRow 16 4, 3279293018988210173020500⟩, ⟨.privateRow 16 5, 22366460078227279641627000⟩, ⟨.privateRow 16 6, 98196607624146960181002750⟩, ⟨.privateRow 16 7, 321370715860844596956009000⟩, ⟨.privateRow 16 8, 820260493816250971278194400⟩, ⟨.privateRow 16 9, 1758186879365678906097954000⟩, ⟨.privateRow 16 10, 3288311074790427750996306375⟩, ⟨.privateRow 16 12, 13431255473993711488653519000⟩, ⟨.privateRow 17 2, 2720598652790218810209600⟩, ⟨.privateRow 17 3, 8744781383968560461388000⟩, ⟨.privateRow 17 4, 50226436666896347265408000⟩, ⟨.privateRow 17 5, 207445647275254184278482000⟩, ⟨.privateRow 17 6, 641813954908237982953992000⟩, ⟨.privateRow 17 7, 1587469313903092675757301600⟩, ⟨.privateRow 17 8, 3323664687492050646472728000⟩, ⟨.privateRow 17 9, 6141751458673918964048172000⟩, ⟨.privateRow 17 10, 3853533663202145643318312000⟩, ⟨.privateRow 17 12, 39829564276848803381468544000⟩, ⟨.privateRow 18 2, 19821504470328737045812800⟩, ⟨.privateRow 18 3, 138750531292301159320689600⟩, ⟨.privateRow 18 4, 531877036620487777395976800⟩, ⟨.privateRow 18 5, 1576710582867058628644200000⟩, ⟨.privateRow 18 6, 3774014451150591533522757120⟩, ⟨.privateRow 18 7, 7615862495377419189380073600⟩, ⟨.privateRow 18 8, 13562864433822438323597408400⟩, ⟨.privateRow 18 10, 27102603779096159787308035200⟩, ⟨.privateRow 18 14, 34826383354367590989493089600⟩, ⟨.privateRow 19 0, 41625159387690347796206880⟩, ⟨.privateRow 19 1, 89196770116479316706157600⟩, ⟨.privateRow 19 2, 432261270564476688652917600⟩, ⟨.privateRow 19 3, 1717037824742226846593533800⟩, ⟨.privateRow 19 4, 4995019126522841735544825600⟩, ⟨.privateRow 19 5, 11800732686410213600224650480⟩, ⟨.privateRow 19 6, 23934466647921949982818956000⟩, ⟨.privateRow 19 7, 43550323009371026381781448200⟩, ⟨.privateRow 19 9, 120504836427363556870018917600⟩, ⟨.privateRow 19 13, 749252868978426260331723840000⟩, ⟨.privateRow 20 0, 564912877404369005805664800⟩, ⟨.privateRow 20 1, 1825103142383346018756763200⟩, ⟨.privateRow 20 2, 7579247771841950827892669400⟩, ⟨.privateRow 20 3, 21928890786515051407183533600⟩, ⟨.privateRow 20 4, 51011632829614521224251531440⟩, ⟨.privateRow 20 6, 394450416647600658303805446600⟩, ⟨.privateRow 21 5, 4028534956989906472651647105000⟩, ⟨.hall 17 7, 42740985338642420056478160⟩, ⟨.hall 15 9, 576315626276866718601450⟩, ⟨.hall 20 11, 45627578559583650468919080000⟩, ⟨.hall 13 14, 391980990105959157523620⟩, ⟨.hall 16 14, 39728742091480695272619600⟩, ⟨.hall 14 16, 47364808330826616437808000⟩, ⟨.hall 12 18, 12306421089341990349710400⟩, ⟨.hall 10 20, 12464437557933904360896000⟩, ⟨.hall 6 22, 40495974461900159989026240⟩, ⟨.hall 5 23, 23977808541599948004706880⟩, ⟨.hall 8 24, 36226621068985660806731766528⟩, ⟨.hall 5 27, 805099957823577476958301404000⟩, ⟨.hall 4 28, 3639560401827272665273446115200⟩, ⟨.hall 3 29, 4918470458408879185947601147680⟩]
  caps := #[0, 367386756734502078183832622400, 72575929132728446347898976000, 6477329537870011526967861600, 0, 524693151812419842963110400, 100899955142442711205030080, 121095232885441690766155980, 4968488913061309786745595, 46781883291279942066317940, 0, 4138033374719072748279360, 3492508407947586652603500, 29039734321851294766635840, 30351553904470641895992420, 0, 154257687667466447524132725, 0, 3965293711576812184689060240, 0, 54194844901535866307981363760, 16638056465868923085000000, 5546018821956307695000000] }

theorem case_55_33_21_checked :
    (Witness.linear .conditional case_55_33_21).check 55 33 21 = true := by
  change case_55_33_21.check 55 33 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_34_1_checked :
    (Witness.rising).check 55 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_34_2_checked :
    (Witness.rising).check 55 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_34_3_checked :
    (Witness.rising).check 55 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_34_4_checked :
    (Witness.rising).check 55 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_34_5_checked :
    (Witness.rising).check 55 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_34_6_checked :
    (Witness.rising).check 55 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_34_7_checked :
    (Witness.rising).check 55 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_34_8_checked :
    (Witness.rising).check 55 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_34_9_checked :
    (Witness.rising).check 55 34 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_34_10_checked :
    (Witness.rising).check 55 34 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_34_11_checked :
    (Witness.linear .positive case_55_34_11).check 55 34 11 = true := by
  change case_55_34_11.check 55 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_34_12_checked :
    (Witness.linear .positive case_55_34_12).check 55 34 12 = true := by
  change case_55_34_12.check 55 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_34_13_checked :
    (Witness.linear .positive case_55_34_13).check 55 34 13 = true := by
  change case_55_34_13.check 55 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_34_14_checked :
    (Witness.linear .positive case_55_34_14).check 55 34 14 = true := by
  change case_55_34_14.check 55 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_15 : Certificate := {
  objectiveScale := 69
  eta := 143825440
  rows := #[⟨.assumptionRow 15, 304⟩]
  caps := #[0, 0, 40681204, 11630584, 3367598, 990080, 296582, 90948, 28743, 9456, 3290, 1244, 539, 19824, 5954, 938, 69, 0, 0, 0, 0, 0] }

theorem case_55_34_15_checked :
    (Witness.linear .conditional case_55_34_15).check 55 34 15 = true := by
  change case_55_34_15.check 55 34 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_16 : Certificate := {
  objectiveScale := 276604058822520000000
  eta := 27591056828555432699174688000
  rows := #[⟨.count 2, 5638172482356979725483523200⟩, ⟨.count 3, 1089471427784047469662300800⟩, ⟨.count 4, 226671167775345928438003200⟩, ⟨.count 5, 44384191764409511030016000⟩, ⟨.count 6, 9405276173217459659124000⟩, ⟨.count 7, 1893664380031108270185600⟩, ⟨.count 8, 403492652403722827545600⟩, ⟨.count 9, 88881248606414469004800⟩, ⟨.count 10, 18516926793003014376000⟩, ⟨.count 11, 5290550512286575536000⟩, ⟨.path 10, 235077431826549312000⟩, ⟨.path 11, 729929303714743164032⟩, ⟨.privateRow 2 32, 568704552987938065296998400⟩, ⟨.privateRow 3 31, 925080267935971622662387200⟩, ⟨.privateRow 5 28, 213722721748208277699494400⟩, ⟨.privateRow 6 22, 1270739846855880333504000⟩, ⟨.privateRow 6 23, 2713831973198334642654000⟩, ⟨.privateRow 6 24, 5196114185642260162682400⟩, ⟨.privateRow 6 26, 31683343501246872026592000⟩, ⟨.privateRow 6 27, 28492370003721691852785000⟩, ⟨.privateRow 7 19, 105967767297947409254400⟩, ⟨.privateRow 7 20, 584175974378543312465700⟩, ⟨.privateRow 7 22, 4803893345024436789126000⟩, ⟨.privateRow 7 23, 3136467600872347729347360⟩, ⟨.privateRow 8 17, 81042416264043192918960⟩, ⟨.privateRow 8 18, 238427476420381670822400⟩, ⟨.privateRow 8 19, 419970512853448724267100⟩, ⟨.privateRow 8 20, 446314620181147145485200⟩, ⟨.privateRow 8 21, 2794645132273512083966400⟩, ⟨.privateRow 8 22, 2251305594661680776419200⟩, ⟨.privateRow 8 23, 1803107790429136385594400⟩, ⟨.privateRow 8 24, 1837305321101611000239600⟩, ⟨.privateRow 9 14, 3762169253181564825600⟩, ⟨.privateRow 9 15, 39182137733419365484800⟩, ⟨.privateRow 9 16, 103342086673331108803200⟩, ⟨.privateRow 9 17, 200531459047188200131200⟩, ⟨.privateRow 9 18, 324575273928781409133600⟩, ⟨.privateRow 9 19, 452316875702824653206400⟩, ⟨.privateRow 9 20, 1620201702440473276924800⟩, ⟨.privateRow 9 21, 1578559191519319831261440⟩, ⟨.privateRow 9 23, 5059529806583395070928000⟩, ⟨.privateRow 10 12, 3540599188991785166400⟩, ⟨.privateRow 10 13, 17833564018499331702600⟩, ⟨.privateRow 10 15, 184746023889047217717120⟩, ⟨.privateRow 10 16, 108015406292517583860000⟩, ⟨.privateRow 10 17, 275075560698200136774900⟩, ⟨.privateRow 10 18, 351594871187959277049600⟩, ⟨.privateRow 10 19, 975004371493480149822000⟩, ⟨.privateRow 10 20, 1109481347931617755654560⟩, ⟨.privateRow 10 24, 16338278092043402570275200⟩, ⟨.privateRow 11 10, 2284555903032839436000⟩, ⟨.privateRow 11 11, 8749756616473951848000⟩, ⟨.privateRow 11 12, 13887695094752260782000⟩, ⟨.privateRow 11 13, 23720030189384026680000⟩, ⟨.privateRow 11 14, 145153467691644408796800⟩, ⟨.privateRow 11 15, 104394852785371972824000⟩, ⟨.privateRow 11 16, 222924560222257069176000⟩, ⟨.privateRow 11 17, 280399177151188503408000⟩, ⟨.privateRow 11 18, 638192695508629865604000⟩, ⟨.privateRow 11 19, 824027290245508169620800⟩, ⟨.privateRow 11 21, 583002634482731270808000⟩, ⟨.privateRow 12 8, 1305002459697355298880⟩, ⟨.privateRow 12 9, 4761495461057917982400⟩, ⟨.privateRow 12 10, 10214832142953311227200⟩, ⟨.privateRow 12 11, 15540992129841815637000⟩, ⟨.privateRow 12 12, 24384628270266307243200⟩, ⟨.privateRow 12 13, 149405146466972893136640⟩, ⟨.privateRow 12 14, 99697485209311467878400⟩, ⟨.privateRow 12 15, 196345555887235534579800⟩, ⟨.privateRow 12 16, 250545356403285684312000⟩, ⟨.privateRow 12 17, 479235700571292300636000⟩, ⟨.privateRow 12 18, 682322299569599646877920⟩, ⟨.privateRow 12 20, 1056787464829243463316000⟩, ⟨.privateRow 13 6, 727450695439404136200⟩, ⟨.privateRow 13 7, 2868654055550943179520⟩, ⟨.privateRow 13 9, 26425621533164741395200⟩, ⟨.privateRow 13 10, 11168939970382770576000⟩, ⟨.privateRow 13 11, 30813448741256964182400⟩, ⟨.privateRow 13 12, 167005044504512901086400⟩, ⟨.privateRow 13 13, 116548868322520560326400⟩, ⟨.privateRow 13 14, 194075027959045879245600⟩, ⟨.privateRow 13 16, 900863184453241889880000⟩, ⟨.privateRow 13 18, 819329922669447664675200⟩, ⟨.privateRow 14 4, 438285802243348659600⟩, ⟨.privateRow 14 5, 1898536095294505491825⟩, ⟨.privateRow 14 7, 10234695931506768150000⟩, ⟨.privateRow 14 8, 33198204464598261488400⟩, ⟨.privateRow 14 9, 17003241507543244153200⟩, ⟨.privateRow 14 11, 298320917011559278036200⟩, ⟨.privateRow 14 12, 131122375520717377196400⟩, ⟨.privateRow 14 14, 585833995119447408906000⟩, ⟨.privateRow 14 15, 456603901157621949732000⟩, ⟨.privateRow 15 2, 318412762313543898000⟩, ⟨.privateRow 15 3, 1416000284170818746400⟩, ⟨.privateRow 15 4, 2794071989301347704950⟩, ⟨.privateRow 15 5, 1528381259105010710400⟩, ⟨.privateRow 15 6, 17603677002191641218000⟩, ⟨.privateRow 15 7, 59165989895738203077600⟩, ⟨.privateRow 15 8, 34102006843780551475800⟩, ⟨.privateRow 15 10, 426189114101432236595040⟩, ⟨.privateRow 15 12, 667998134057583743614200⟩, ⟨.privateRow 15 14, 1472404295490289693131600⟩, ⟨.privateRow 16 1, 1592063811567719490000⟩, ⟨.privateRow 16 2, 3202857785624470974000⟩, ⟨.privateRow 16 4, 14901717276273854426400⟩, ⟨.privateRow 16 5, 35207354004383282436000⟩, ⟨.privateRow 16 6, 128295849922949456748000⟩, ⟨.privateRow 16 7, 78090729957396640984500⟩, ⟨.privateRow 16 8, 11462859443287580328000⟩, ⟨.privateRow 16 9, 710410713997747790827800⟩, ⟨.privateRow 16 10, 284024183983681157016000⟩, ⟨.privateRow 16 11, 890520893000403896731500⟩, ⟨.privateRow 16 12, 668120950408761824832000⟩, ⟨.privateRow 16 14, 3829168197030216208568400⟩, ⟨.privateRow 17 0, 7132445875823383315200⟩, ⟨.privateRow 17 1, 3236572078104728563200⟩, ⟨.privateRow 17 2, 8597144582465685246000⟩, ⟨.privateRow 17 4, 178820607315286253116800⟩, ⟨.privateRow 17 5, 300503269097877490444800⟩, ⟨.privateRow 17 7, 387653064809361807456000⟩, ⟨.privateRow 17 9, 4088929328525605320556800⟩, ⟨.privateRow 17 13, 13518837913035640735630080⟩, ⟨.privateRow 18 0, 75654872325698030164800⟩, ⟨.privateRow 18 3, 626363391008214210780000⟩, ⟨.privateRow 18 5, 2354662377308657125710000⟩, ⟨.privateRow 18 7, 483274154129004386628480⟩, ⟨.privateRow 18 8, 9202128830861418652200000⟩, ⟨.privateRow 18 9, 7156549721930518588278600⟩, ⟨.privateRow 19 0, 643066414768433256400800⟩, ⟨.privateRow 19 4, 17752530419819475653973600⟩, ⟨.privateRow 19 10, 25449840535987085844225600⟩, ⟨.privateRow 19 13, 203598724287896686753804800⟩, ⟨.privateRow 20 0, 7553107344371052429725760⟩, ⟨.privateRow 20 3, 104780851885147443020215200⟩, ⟨.privateRow 20 4, 53316051842619193621593600⟩, ⟨.privateRow 20 11, 534271269506246502749719200⟩, ⟨.privateRow 20 13, 1527282735075028983951900000⟩, ⟨.hall 12 11, 6453768850160385600⟩, ⟨.hall 16 15, 12511748542673371992000⟩, ⟨.hall 14 16, 302245674691432071600⟩, ⟨.hall 7 18, 6334904561101340224⟩, ⟨.hall 10 18, 31550332435798176000⟩, ⟨.hall 11 18, 70799574896212219200⟩, ⟨.hall 15 18, 74206932185493283176000⟩, ⟨.hall 8 19, 24204293488076377104⟩, ⟨.hall 11 22, 8050837736088267120000⟩, ⟨.hall 5 24, 3450353993650629711360⟩, ⟨.hall 8 25, 170355726495627732259200⟩, ⟨.hall 4 28, 2196146842048601320919040⟩, ⟨.hall 3 30, 440445805183742515049692800⟩]
  caps := #[0, 16051698188050990892993280, 0, 23654533156936359392000, 94888962321422414745600, 8282632605763972904448, 0, 5993619360659237078200, 2256801679520751554048, 0, 4256116734114140842188, 0, 4269648677168418762240, 2484605475291977542560, 11981302000151300398725, 276604058822520000000, 10945390261352057511000, 5094604197016702368000, 842280904634527262550360, 2104580993787599748220800, 0, 0] }

theorem case_55_34_16_checked :
    (Witness.linear .positive case_55_34_16).check 55 34 16 = true := by
  change case_55_34_16.check 55 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_17 : Certificate := {
  objectiveScale := 32983098148000000
  eta := 2857366183851706887360000
  rows := #[⟨.count 2, 542899574931824308598400⟩, ⟨.count 3, 103104033661893633969600⟩, ⟨.count 4, 21201716059745895273600⟩, ⟨.count 5, 4241037042140122224000⟩, ⟨.count 6, 897642809532725256000⟩, ⟨.count 7, 185165932207958301600⟩, ⟨.count 8, 41629811456590156800⟩, ⟨.count 9, 9606879566905420800⟩, ⟨.count 10, 2501791553881620000⟩, ⟨.count 11, 500358310776324000⟩, ⟨.path 11, 86168986025954832⟩, ⟨.privateRow 2 32, 25212054563397413712000⟩, ⟨.privateRow 3 29, 2639156588800080148800⟩, ⟨.privateRow 3 30, 11721393788246166024000⟩, ⟨.privateRow 4 27, 2331377852536383651000⟩, ⟨.privateRow 4 28, 4285557812725642252800⟩, ⟨.privateRow 4 29, 7729485149041575519600⟩, ⟨.privateRow 5 24, 251224348304005876800⟩, ⟨.privateRow 5 25, 880817427402353400960⟩, ⟨.privateRow 5 26, 1591906644345234016800⟩, ⟨.privateRow 5 27, 2826779836267628841600⟩, ⟨.privateRow 5 28, 3587969374914864139200⟩, ⟨.privateRow 6 21, 11586422133914252625⟩, ⟨.privateRow 6 22, 158280012308910492000⟩, ⟨.privateRow 6 23, 329840368116342583500⟩, ⟨.privateRow 6 24, 573494017201463358000⟩, ⟨.privateRow 6 25, 1007815455086787096750⟩, ⟨.privateRow 6 26, 1329660514362183003000⟩, ⟨.privateRow 6 27, 1410155657608324126500⟩, ⟨.privateRow 7 19, 16984384882462998000⟩, ⟨.privateRow 7 20, 65588635237596471000⟩, ⟨.privateRow 7 21, 131425066971958359600⟩, ⟨.privateRow 7 22, 212196400063452604800⟩, ⟨.privateRow 7 23, 367122899782804445280⟩, ⟨.privateRow 7 24, 483621325280855962200⟩, ⟨.privateRow 7 25, 535622452612482034800⟩, ⟨.privateRow 7 26, 414780361023213385200⟩, ⟨.privateRow 8 16, 216821934669740400⟩, ⟨.privateRow 8 17, 10689321379218201720⟩, ⟨.privateRow 8 18, 27211152801052420200⟩, ⟨.privateRow 8 19, 52647076011996340875⟩, ⟨.privateRow 8 20, 84250808900241984000⟩, ⟨.privateRow 8 21, 140735504095217331300⟩, ⟨.privateRow 8 22, 186553592589844640160⟩, ⟨.privateRow 8 23, 206089248903588250200⟩, ⟨.privateRow 8 24, 138476942275740868800⟩, ⟨.privateRow 9 14, 572632288999570800⟩, ⟨.privateRow 9 15, 4942933615547928000⟩, ⟨.privateRow 9 16, 12142028341505462400⟩, ⟨.privateRow 9 17, 22215908998468785600⟩, ⟨.privateRow 9 18, 35408689792604528400⟩, ⟨.privateRow 9 19, 59147117651006985600⟩, ⟨.privateRow 9 20, 78389468688290760000⟩, ⟨.privateRow 9 21, 66420897894521089920⟩, ⟨.privateRow 10 12, 446473569615796800⟩, ⟨.privateRow 10 13, 2259951703673063400⟩, ⟨.privateRow 10 14, 5622207928359422400⟩, ⟨.privateRow 10 15, 10347409866854380320⟩, ⟨.privateRow 10 16, 16244966489871319200⟩, ⟨.privateRow 10 17, 27307054810617882300⟩, ⟨.privateRow 10 18, 26790613554138033600⟩, ⟨.privateRow 11 10, 259926395208480000⟩, ⟨.privateRow 11 11, 1109185905706956000⟩, ⟨.privateRow 11 12, 2774714268850524000⟩, ⟨.privateRow 11 13, 5293046593336320000⟩, ⟨.privateRow 11 14, 8492445147449062800⟩, ⟨.privateRow 11 15, 8910421231299588000⟩, ⟨.privateRow 12 8, 133428882873686400⟩, ⟨.privateRow 12 9, 593281997063355600⟩, ⟨.privateRow 12 10, 1512621662577656400⟩, ⟨.privateRow 12 11, 3002149864657944000⟩, ⟨.privateRow 12 12, 2288002093822645200⟩, ⟨.privateRow 13 6, 70884094026645900⟩, ⟨.privateRow 13 7, 346915095471584640⟩, ⟨.privateRow 13 8, 934002180115804800⟩, ⟨.privateRow 13 9, 590166212710536000⟩, ⟨.privateRow 14 4, 38262694353483600⟩, ⟨.privateRow 14 5, 216821934669740400⟩, ⟨.privateRow 14 6, 187912343380441680⟩, ⟨.privateRow 15 2, 24091326074415600⟩, ⟨.privateRow 15 3, 63771157255806000⟩, ⟨.hall 6 27, 269130226408815271500⟩, ⟨.hall 5 28, 1244707437373047648000⟩, ⟨.hall 4 29, 3464814516022451592000⟩, ⟨.hall 3 30, 7794762539889081556800⟩, ⟨.hall 2 31, 14812082055995980555800⟩, ⟨.assumptionRow 17, 43310798534718000⟩]
  caps := #[0, 7746488958264810605280, 1211582212225352510400, 6443798131271255040, 0, 316046429314696080, 2574665210604976060, 272393992333480160, 1148438143292110385, 0, 0, 138851071261734832, 1278405995308780800, 107186778802875200, 304128738379134240, 0, 3716434674889794000, 484418771833282000, 32983098148000000, 0, 0, 0] }

theorem case_55_34_17_checked :
    (Witness.linear .conditional case_55_34_17).check 55 34 17 = true := by
  change case_55_34_17.check 55 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_18 : Certificate := {
  objectiveScale := 7865283512380694400000
  eta := 565923232283481430696405267200
  rows := #[⟨.count 2, 110724110664159410353644508800⟩, ⟨.count 3, 20979305178472309330164222720⟩, ⟨.count 4, 4217112626885063762157100800⟩, ⟨.count 5, 808654297142388326786956800⟩, ⟨.count 6, 169202121956423644463575200⟩, ⟨.count 7, 35549536734278907119619840⟩, ⟨.count 8, 7813084996544814751564800⟩, ⟨.count 9, 1893170595316628189802240⟩, ⟨.count 10, 563443629558520294584000⟩, ⟨.count 11, 225377451823408117833600⟩, ⟨.count 12, 135226471094044870700160⟩, ⟨.path 10, 35997071310696886790400⟩, ⟨.privateRow 2 32, 9842143170147503142546178560⟩, ⟨.privateRow 3 29, 1055938437283031713673982720⟩, ⟨.privateRow 3 30, 3177776995219689779830193280⟩, ⟨.privateRow 4 26, 35530004021787545082740928⟩, ⟨.privateRow 4 27, 599776352937885544913091600⟩, ⟨.privateRow 4 28, 1150574429303680782352311360⟩, ⟨.privateRow 4 29, 2149233187205793322878884640⟩, ⟨.privateRow 5 24, 58402810349172490267946880⟩, ⟨.privateRow 5 25, 214312921455224268635422464⟩, ⟨.privateRow 5 26, 412433224255109408698226880⟩, ⟨.privateRow 5 27, 786126568735684110919944960⟩, ⟨.privateRow 5 28, 1069806663151898759858010240⟩, ⟨.privateRow 6 22, 33205611235315462694150400⟩, ⟨.privateRow 6 23, 77113521189856374761538000⟩, ⟨.privateRow 6 24, 145860530529246010393275360⟩, ⟨.privateRow 6 25, 278280113275373519159249400⟩, ⟨.privateRow 6 26, 403676058154815428830848000⟩, ⟨.privateRow 6 27, 472203324478677241547697600⟩, ⟨.privateRow 7 19, 1437824669503038825808800⟩, ⟨.privateRow 7 20, 12824446545109887338310660⟩, ⟨.privateRow 7 21, 29578107486919655845209600⟩, ⟨.privateRow 7 22, 53120839346300006128607760⟩, ⟨.privateRow 7 23, 101159917992763988995885248⟩, ⟨.privateRow 7 24, 148350951371894670095336640⟩, ⟨.privateRow 7 25, 185804927574081375810650400⟩, ⟨.privateRow 7 26, 172962169111010836562765760⟩, ⟨.privateRow 8 17, 1003493104243724644654104⟩, ⟨.privateRow 8 18, 4828920588142281339508800⟩, ⟨.privateRow 8 19, 11393064957852263073277890⟩, ⟨.privateRow 8 20, 20634915553374608959936320⟩, ⟨.privateRow 8 21, 38577107170440022835851200⟩, ⟨.privateRow 8 22, 57543370999552560645274752⟩, ⟨.privateRow 8 23, 72759354030323587373947200⟩, ⟨.privateRow 8 24, 74256861987994676867997120⟩, ⟨.privateRow 8 25, 41494806098837227094638680⟩, ⟨.privateRow 9 15, 472609686853934598608640⟩, ⟨.privateRow 9 16, 1914205824153479614133376⟩, ⟨.privateRow 9 17, 4524243662529155550585600⟩, ⟨.privateRow 9 18, 8410335243876846263823840⟩, ⟨.privateRow 9 19, 15911648098732613119052160⟩, ⟨.privateRow 9 20, 23987673455738070674756160⟩, ⟨.privateRow 9 21, 31129133645849129235176832⟩, ⟨.privateRow 9 22, 27206814725949083291146080⟩, ⟨.privateRow 10 13, 188753615902104298685640⟩, ⟨.privateRow 10 14, 797016625084597798520640⟩, ⟨.privateRow 10 15, 1916835227758086042174768⟩, ⟨.privateRow 10 16, 3643602137811764571643200⟩, ⟨.privateRow 10 17, 7081077814476703802184420⟩, ⟨.privateRow 10 18, 11066032884529338585629760⟩, ⟨.privateRow 10 19, 14790395275911157732830000⟩, ⟨.privateRow 11 11, 68558875205022749131200⟩, ⟨.privateRow 11 12, 342334690080252482012400⟩, ⟨.privateRow 11 13, 877295700899382012393600⟩, ⟨.privateRow 11 14, 1723113063486238428164160⟩, ⟨.privateRow 11 15, 3442128355121142163276800⟩, ⟨.privateRow 11 16, 5662608477063128960569200⟩, ⟨.privateRow 11 17, 1287871153276617816192000⟩, ⟨.privateRow 12 9, 22537745182340811783360⟩, ⟨.privateRow 12 10, 149095852744716139489920⟩, ⟨.privateRow 12 11, 430095303896337158199120⟩, ⟨.privateRow 12 12, 900485364330798798071520⟩, ⟨.privateRow 12 13, 1869505962875170337429712⟩, ⟨.privateRow 12 14, 922795455521398793574240⟩, ⟨.privateRow 13 7, 7011742945617141443712⟩, ⟨.privateRow 13 8, 65466783624894738989760⟩, ⟨.privateRow 13 9, 221910106410740300636160⟩, ⟨.privateRow 13 10, 517116042239264181473760⟩, ⟨.privateRow 13 11, 469877838953044803240960⟩, ⟨.privateRow 14 5, 1525993163387659131165⟩, ⟨.privateRow 14 6, 29299068737043055318368⟩, ⟨.privateRow 14 7, 120335460884283977200440⟩, ⟨.privateRow 14 8, 199083415777343837419680⟩, ⟨.privateRow 15 4, 12207945307101273049320⟩, ⟨.privateRow 15 5, 68364493719767129076192⟩, ⟨.privateRow 15 6, 6975968746915013171040⟩, ⟨.privateRow 16 2, 7181144298294866499600⟩, ⟨.privateRow 16 3, 15259931633876591311650⟩, ⟨.hall 7 26, 4861475108961218067640320⟩, ⟨.hall 6 27, 137444024236093047002415600⟩, ⟨.hall 5 28, 451475075274481838618438400⟩, ⟨.hall 4 29, 1104197258945023519456147968⟩, ⟨.hall 3 30, 2311753231227671986661786880⟩, ⟨.hall 2 31, 4288193388435660924486766500⟩, ⟨.assumptionRow 18, 8435381109367803743152⟩]
  caps := #[0, 411912719394102309171428640, 0, 4592586808330426847253312, 0, 814599375486434417559680, 270980782991088418848600, 320543939183180733150416, 0, 31390470874363528543616, 40630510762001010787552, 0, 56804395753692162424464, 207642433605288085331136, 51788893559316840507009, 27676453881921565985264, 0, 801002640223417773709568, 109543871576342612256848, 7865283512380694400000, 0, 0] }

theorem case_55_34_18_checked :
    (Witness.linear .conditional case_55_34_18).check 55 34 18 = true := by
  change case_55_34_18.check 55 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_19 : Certificate := {
  objectiveScale := 33846532643729300695200000
  eta := 2673339522363523857784178853014400
  rows := #[⟨.count 2, 477020061691879967988503951734560⟩, ⟨.count 3, 82220694214872160554948678617280⟩, ⟨.count 4, 14536992164511055150834397354880⟩, ⟨.count 5, 2458135030516350394276728460800⟩, ⟨.count 6, 446190733597715197897305099600⟩, ⟨.count 7, 85805910307252922672558673000⟩, ⟨.count 8, 18959020182173979104793916320⟩, ⟨.count 9, 5883833849640200411832594720⟩, ⟨.count 10, 2640181855607782236078728400⟩, ⟨.count 11, 754337673030794924593922400⟩, ⟨.count 12, 452602603818476954756353440⟩, ⟨.path 8, 494441161414702069328560800⟩, ⟨.path 9, 245110171127470763453539200⟩, ⟨.privateRow 2 32, 46561719169127725959037238316720⟩, ⟨.privateRow 3 29, 5001258772194170350057705512000⟩, ⟨.privateRow 3 30, 14070208012439599251495678173760⟩, ⟨.privateRow 4 26, 241171811903585547991671576912⟩, ⟨.privateRow 4 27, 2483958523523104607195327070960⟩, ⟨.privateRow 4 28, 4986440227683965400872349347520⟩, ⟨.privateRow 4 29, 9749676128682968754640271467560⟩, ⟨.privateRow 5 24, 240583428518621527950488317440⟩, ⟨.privateRow 5 25, 846749066894887508156175186816⟩, ⟨.privateRow 5 26, 1729520272135905576611458814640⟩, ⟨.privateRow 5 27, 3530736149328538039722655542720⟩, ⟨.privateRow 5 28, 5148354618435175360353520380000⟩, ⟨.privateRow 6 22, 115049965452786061624226628900⟩, ⟨.privateRow 6 23, 292012494759921057476136182400⟩, ⟨.privateRow 6 24, 594185498899081905478261058460⟩, ⟨.privateRow 6 25, 1229884714403958558306674313000⟩, ⟨.privateRow 6 26, 1951335360273035909729758901700⟩, ⟨.privateRow 6 27, 2493070293998589084221984491950⟩, ⟨.privateRow 7 19, 2215517684123779167418446160⟩, ⟨.privateRow 7 20, 40614797545433050065011105220⟩, ⟨.privateRow 7 21, 105652175276277408188660679000⟩, ⟨.privateRow 7 22, 210129140352428268411465905880⟩, ⟨.privateRow 7 23, 439620452465616974104092035496⟩, ⟨.privateRow 7 24, 714272913371946829161427696530⟩, ⟨.privateRow 7 25, 996819518026543953104638755480⟩, ⟨.privateRow 7 26, 1061950289945477838218952338700⟩, ⟨.privateRow 8 17, 1013326940771367848704502424⟩, ⟨.privateRow 8 18, 13674465706108243549722048840⟩, ⟨.privateRow 8 19, 38306209958595054764535121875⟩, ⟨.privateRow 8 20, 78322700986579572545604916620⟩, ⟨.privateRow 8 21, 164107208459061978616136420790⟩, ⟨.privateRow 8 22, 274072249512823668627835502388⟩, ⟨.privateRow 8 23, 390559901748512886364596226605⟩, ⟨.privateRow 8 24, 463787755203583575054915544920⟩, ⟨.privateRow 8 25, 360343963333173107166330922470⟩, ⟨.privateRow 9 15, 187441482389470253990004960⟩, ⟨.privateRow 9 16, 4561228462926206644044584112⟩, ⟨.privateRow 9 17, 14075382210107943815200670560⟩, ⟨.privateRow 9 18, 30336946750388469217418912520⟩, ⟨.privateRow 9 19, 65260984969635629476297057920⟩, ⟨.privateRow 9 20, 111767698554062781327332835600⟩, ⟨.privateRow 9 21, 164375207871230419368512983776⟩, ⟨.privateRow 9 22, 203281430587248718929318854760⟩, ⟨.privateRow 9 23, 149660594329309713039434204160⟩, ⟨.privateRow 10 14, 1381809464688228884597048760⟩, ⟨.privateRow 10 15, 5280363711215564472157456800⟩, ⟨.privateRow 10 16, 12241224127349733192993596280⟩, ⟨.privateRow 10 17, 27580471170188439430465287750⟩, ⟨.privateRow 10 18, 49366012573629593565210835920⟩, ⟨.privateRow 10 19, 75339475093950643093817999700⟩, ⟨.privateRow 10 20, 98290198795912578674588088720⟩, ⟨.privateRow 10 21, 8505157263422212774796475060⟩, ⟨.privateRow 11 12, 345738100139114340438881100⟩, ⟨.privateRow 11 13, 1938834845558489434286858400⟩, ⟨.privateRow 11 14, 5160355445051574370517514600⟩, ⟨.privateRow 11 15, 12423712887643546712630206800⟩, ⟨.privateRow 11 16, 23684488529364617916511449900⟩, ⟨.privateRow 11 17, 38221408199086316861080366800⟩, ⟨.privateRow 11 18, 21790072327775917026338076600⟩, ⟨.privateRow 12 10, 72532468560653358134031000⟩, ⟨.privateRow 12 11, 656902390264317246833874090⟩, ⟨.privateRow 12 12, 2191008059393990712797801880⟩, ⟨.privateRow 12 13, 5974354370403895802783865408⟩, ⟨.privateRow 12 14, 12379519367405378929169148720⟩, ⟨.privateRow 12 15, 15501639180782835700405105320⟩, ⟨.privateRow 13 8, 3592084157289499640923440⟩, ⟨.privateRow 13 9, 205025111131446825658860960⟩, ⟨.privateRow 13 10, 888442148236269577855064160⟩, ⟨.privateRow 13 11, 2967061513921126703402761440⟩, ⟨.privateRow 13 12, 7045513866107624595707235216⟩, ⟨.privateRow 13 13, 1341044752054746532611417600⟩, ⟨.privateRow 14 7, 40859957289168058415504130⟩, ⟨.privateRow 14 8, 345738100139114340438881100⟩, ⟨.privateRow 14 9, 1436908498002410054278561905⟩, ⟨.privateRow 14 10, 2161863194754164545256673060⟩, ⟨.privateRow 15 5, 10895988610444815577467768⟩, ⟨.privateRow 15 6, 93394188089526990664009440⟩, ⟨.privateRow 15 7, 678903905727715432134530160⟩, ⟨.privateRow 15 8, 381359601365568545211371880⟩, ⟨.privateRow 16 4, 27239971526112038943669420⟩, ⟨.privateRow 16 5, 262671154001794661242526550⟩, ⟨.privateRow 16 6, 31430736376283121858080100⟩, ⟨.privateRow 17 3, 87167908883558524619742144⟩, ⟨.hall 7 26, 194874756297805526603011030680⟩, ⟨.hall 6 27, 953496289026514620310371376500⟩, ⟨.hall 5 28, 2561609349941057367036543057600⟩, ⟨.hall 4 29, 5659202148447270093887519214912⟩, ⟨.hall 3 30, 11115700948521881842547609992800⟩, ⟨.hall 2 31, 19895632553134933923823309739925⟩, ⟨.assumptionRow 19, 27884841991121314703303800⟩]
  caps := #[0, 0, 533236583207157809750358588000, 32591205702545146885646137720, 6247107355277614680135625344, 0, 766936148620647938683646610, 51612236075225890128049700, 680200078098027473715132404, 151437413375731064815633400, 0, 157391150022303825441752400, 0, 431747291574610750542345432, 570964793867898869184360615, 1493041971098777722489738872, 27884841991121314703303800, 27884841991121314703303800, 3101766765081027551751243000, 445966615021088895029496200, 33846532643729300695200000, 0] }

theorem case_55_34_19_checked :
    (Witness.linear .conditional case_55_34_19).check 55 34 19 = true := by
  change case_55_34_19.check 55 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_20 : Certificate := {
  objectiveScale := 335833696278400320000
  eta := 28495048891546489722588518400
  rows := #[⟨.count 2, 5213616175867513376939296320⟩, ⟨.count 3, 906460146627368984209278720⟩, ⟨.count 4, 160878909505506282274504320⟩, ⟨.count 5, 26667800061393900112704000⟩, ⟨.count 6, 4446134908884422197844400⟩, ⟨.count 7, 681110028595060421797440⟩, ⟨.count 8, 100905189421490432858880⟩, ⟨.count 9, 17464359707565651840960⟩, ⟨.count 10, 4158180882753726628800⟩, ⟨.count 11, 2079090441376863314400⟩, ⟨.path 9, 4671324395296144185600⟩, ⟨.privateRow 2 32, 529044106258491812864235360⟩, ⟨.privateRow 3 29, 52196812985030979626000640⟩, ⟨.privateRow 3 30, 157876980120216941896952640⟩, ⟨.privateRow 4 26, 1905306201683642566160352⟩, ⟨.privateRow 4 27, 26603833378814205284730960⟩, ⟨.privateRow 4 28, 55249795591158574091605920⟩, ⟨.privateRow 4 29, 111684025905764643026055360⟩, ⟨.privateRow 5 24, 2346045654049652563968960⟩, ⟨.privateRow 5 25, 8915694236741690389031040⟩, ⟨.privateRow 5 26, 18867468543436184329738080⟩, ⟨.privateRow 5 27, 40080982740922021223445120⟩, ⟨.privateRow 5 28, 61054847113531818339112320⟩, ⟨.privateRow 6 21, 26183545246089872365725⟩, ⟨.privateRow 6 22, 1142583952920001680745800⟩, ⟨.privateRow 6 23, 2994121245631725046437600⟩, ⟨.privateRow 6 24, 6342611906493684351129600⟩, ⟨.privateRow 6 25, 13747205884688992342727100⟩, ⟨.privateRow 6 26, 23020497902096277174992400⟩, ⟨.privateRow 6 27, 31095916186453056161823600⟩, ⟨.privateRow 7 19, 46848837945691986684480⟩, ⟨.privateRow 7 20, 397201565948210665952310⟩, ⟨.privateRow 7 21, 1051009919408024074905120⟩, ⟨.privateRow 7 22, 2178921434070309034546440⟩, ⟨.privateRow 7 23, 4810654905669556386547104⟩, ⟨.privateRow 7 24, 8315893970158143463354260⟩, ⟨.privateRow 7 25, 12427254891222308339682480⟩, ⟨.privateRow 7 26, 14347006151272539268403880⟩, ⟨.privateRow 8 17, 23784794649351316316736⟩, ⟨.privateRow 8 18, 132688322002168222970680⟩, ⟨.privateRow 8 19, 367583190035429433985920⟩, ⟨.privateRow 8 20, 784138860395957222184600⟩, ⟨.privateRow 8 21, 1745494604806719548761980⟩, ⟨.privateRow 8 22, 3127880684227950757138032⟩, ⟨.privateRow 8 23, 4812817159728588324394080⟩, ⟨.privateRow 8 24, 6268734892810093141357920⟩, ⟨.privateRow 8 25, 5660375703909544795036860⟩, ⟨.privateRow 9 15, 8139954091693658794560⟩, ⟨.privateRow 9 16, 44963795945510297279424⟩, ⟨.privateRow 9 17, 130382071679233517183040⟩, ⟨.privateRow 9 18, 291488479881036236678880⟩, ⟨.privateRow 9 19, 669665130736814450409600⟩, ⟨.privateRow 9 20, 1239507519139077533304960⟩, ⟨.privateRow 9 21, 1981456354249805813155776⟩, ⟨.privateRow 9 22, 2698035665774755523096880⟩, ⟨.privateRow 9 23, 2906845649103705161973120⟩, ⟨.privateRow 9 24, 996993169654918521365280⟩, ⟨.privateRow 10 13, 2027113180342441731540⟩, ⟨.privateRow 10 14, 15139558577662431953040⟩, ⟨.privateRow 10 15, 47798289247254087598056⟩, ⟨.privateRow 10 16, 112686701922625991640480⟩, ⟨.privateRow 10 17, 270983450402956922240610⟩, ⟨.privateRow 10 18, 526693011384798816489360⟩, ⟨.privateRow 10 19, 877549423797817723953000⟩, ⟨.privateRow 10 20, 1260011971092034243058976⟩, ⟨.privateRow 10 21, 1150932491085197109268980⟩, ⟨.privateRow 11 11, 276242785917205615200⟩, ⟨.privateRow 11 12, 4772457604069618062600⟩, ⟨.privateRow 11 13, 17972963650249578734400⟩, ⟨.privateRow 11 14, 45872295465651338764080⟩, ⟨.privateRow 11 15, 116408063803555084360800⟩, ⟨.privateRow 11 16, 240725596672600685345700⟩, ⟨.privateRow 11 17, 424620471183020162107200⟩, ⟨.privateRow 11 18, 646376617675937247699600⟩, ⟨.privateRow 11 19, 172829118145000346789760⟩, ⟨.privateRow 12 10, 1183482251245291425120⟩, ⟨.privateRow 12 11, 6670415166084103133700⟩, ⟨.privateRow 12 12, 19562350971136850276400⟩, ⟨.privateRow 12 13, 53702906100764379410952⟩, ⟨.privateRow 12 14, 119178084300702642655440⟩, ⟨.privateRow 12 15, 225607301519906880403830⟩, ⟨.privateRow 12 16, 213344380577285845533360⟩, ⟨.privateRow 13 8, 158406890771570538240⟩, ⟨.privateRow 13 9, 2153724457221160971840⟩, ⟨.privateRow 13 10, 8454967794932577478560⟩, ⟨.privateRow 13 11, 26511553264587396445440⟩, ⟨.privateRow 13 12, 64590409712107886967360⟩, ⟨.privateRow 13 13, 130813290437445014759360⟩, ⟨.privateRow 14 7, 482645995319628983700⟩, ⟨.privateRow 14 8, 3291893198846700247800⟩, ⟨.privateRow 14 9, 13551627001918916020110⟩, ⟨.privateRow 14 10, 38208012065848447182360⟩, ⟨.privateRow 14 11, 26983128778336057715388⟩, ⟨.privateRow 15 6, 900939191263307436240⟩, ⟨.privateRow 15 7, 6375877353555714164160⟩, ⟨.privateRow 15 8, 19670505675915545691240⟩, ⟨.privateRow 16 5, 2252347978158268590600⟩, ⟨.privateRow 16 6, 6064013787349184667000⟩, ⟨.privateRow 17 4, 2059289580030416997120⟩, ⟨.hall 7 26, 3922689238760440577388960⟩, ⟨.hall 6 27, 13817672200005658174347300⟩, ⟨.hall 5 28, 33537306060433298054131200⟩, ⟨.hall 4 29, 69959249579076341941609152⟩, ⟨.hall 3 30, 132258803279199351828353280⟩, ⟨.hall 2 31, 230147281373588950769528130⟩, ⟨.assumptionRow 20, 162750606444784101744⟩]
  caps := #[0, 0, 687482638981024943216160, 697374401612296935577050, 160765702919835401003616, 0, 12116069119108206502965, 4912457410745023128704, 9316276733676105336, 0, 0, 0, 2506906317447732525798, 856294900209912581088, 162750606444784101744, 11391406835710064235072, 162750606444784101744, 25218667000565419290624, 130840763292238594218624, 27946524174829051375584, 4203087445174420058256, 335833696278400320000] }

theorem case_55_34_20_checked :
    (Witness.linear .conditional case_55_34_20).check 55 34 20 = true := by
  change case_55_34_20.check 55 34 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_21 : Certificate := {
  objectiveScale := 22760574817359508718160000000
  eta := 2720967263486140276811018733005088000
  rows := #[⟨.count 2, 510749090278050913871810344875158400⟩, ⟨.count 3, 89902097029328027515112087680233600⟩, ⟨.count 4, 16385347150136169385157001235411200⟩, ⟨.count 5, 2744100370491416519488508034432000⟩, ⟨.count 6, 466582283491941162863341040016000⟩, ⟨.count 7, 70839547607794719932447897628000⟩, ⟨.count 8, 9374255924039000532414157881600⟩, ⟨.count 9, 884982202619066483829308611200⟩, ⟨.path 9, 305019081974245844432459232000⟩, ⟨.path 10, 61208384792490467305693920000⟩, ⟨.privateRow 2 32, 54914817305562466891633610241225600⟩, ⟨.privateRow 5 24, 177258657472737464612922258124800⟩, ⟨.privateRow 5 25, 683468477370843493363286783731200⟩, ⟨.privateRow 6 23, 469467352786744832534775321561000⟩, ⟨.privateRow 6 24, 480217564835997890910488906025600⟩, ⟨.privateRow 6 27, 8782639175878414177790349593703000⟩, ⟨.privateRow 7 19, 4332042510351356306645936596800⟩, ⟨.privateRow 7 20, 22436961977280846444769681861500⟩, ⟨.privateRow 7 21, 88933687694941427128942108214400⟩, ⟨.privateRow 7 22, 256229661923732681219320315430400⟩, ⟨.privateRow 7 23, 428254359838881703868311335404640⟩, ⟨.privateRow 7 25, 1814096064027380675001920121261600⟩, ⟨.privateRow 8 17, 2727056268811345609429573201920⟩, ⟨.privateRow 8 19, 49188212192329641998207243202600⟩, ⟨.privateRow 8 20, 58307567488564010616793581044400⟩, ⟨.privateRow 8 21, 183747844101972795473902134461400⟩, ⟨.privateRow 8 22, 280023938040015007949512463901840⟩, ⟨.privateRow 8 23, 200334773263020970184901996205500⟩, ⟨.privateRow 8 24, 487763130683945950051163180835600⟩, ⟨.privateRow 9 14, 46434251371988056250303229600⟩, ⟨.privateRow 9 15, 1102503080703887538777253152000⟩, ⟨.privateRow 9 16, 2428784489410104683398213632960⟩, ⟨.privateRow 9 17, 8241624380769331081916565379200⟩, ⟨.privateRow 9 18, 33547380902985723933307309761600⟩, ⟨.privateRow 9 19, 54728423196887032079348989670400⟩, ⟨.privateRow 9 20, 129617115565077718900111144555200⟩, ⟨.privateRow 9 21, 198531007454210581205708231779200⟩, ⟨.privateRow 9 22, 219614889003644452158419445266400⟩, ⟨.privateRow 9 23, 300467846348480831750491556995200⟩, ⟨.privateRow 9 24, 260512538756160756054642401548800⟩, ⟨.privateRow 10 12, 30255801798942443891600294400⟩, ⟨.privateRow 10 13, 393325423386251770590803827200⟩, ⟨.privateRow 10 14, 1258194394127612197969446333600⟩, ⟨.privateRow 10 15, 3109729128647553061233542758800⟩, ⟨.privateRow 10 16, 7912942719097023468066379773600⟩, ⟨.privateRow 10 17, 29268942638703500897479737922500⟩, ⟨.privateRow 10 18, 45334266879402893808541844690400⟩, ⟨.privateRow 10 20, 320201310610955238290841010675680⟩, ⟨.privateRow 10 21, 63325393165186535065119416179200⟩, ⟨.privateRow 10 22, 152888869782097615326733704331200⟩, ⟨.privateRow 11 10, 12770305954099083460740384000⟩, ⟨.privateRow 11 11, 139245451461041929273842264000⟩, ⟨.privateRow 11 12, 534490513787188722346404822000⟩, ⟨.privateRow 11 13, 1401831312688603934440364880000⟩, ⟨.privateRow 11 15, 14844061748756395736059503024000⟩, ⟨.privateRow 11 16, 22280991313414375868126784984000⟩, ⟨.privateRow 11 18, 95534126746533822574654615188000⟩, ⟨.privateRow 11 19, 117054539921165313863665470801600⟩, ⟨.privateRow 12 8, 4916567792328147132385047840⟩, ⟨.privateRow 12 9, 52677512060658719275554084000⟩, ⟨.privateRow 12 10, 223136538267200523700552171200⟩, ⟨.privateRow 12 11, 647348092656539372430697965600⟩, ⟨.privateRow 12 12, 1512961997911888913011216994400⟩, ⟨.privateRow 12 13, 626862393521838759379093599600⟩, ⟨.privateRow 12 14, 14659566300791758699728084309600⟩, ⟨.privateRow 12 15, 21577586898580155727254878707800⟩, ⟨.privateRow 12 16, 7662822087757155030617267419200⟩, ⟨.privateRow 12 17, 60387743909270467153519350094800⟩, ⟨.privateRow 12 18, 15693684393111445646573072705280⟩, ⟨.privateRow 13 7, 26221694892416784706053588480⟩, ⟨.privateRow 13 8, 95990133088311444013231886400⟩, ⟨.privateRow 13 9, 312643285255738586879869708800⟩, ⟨.privateRow 13 10, 786650846772503541181607654400⟩, ⟨.privateRow 13 11, 2038140830274213720334165286400⟩, ⟨.privateRow 13 12, 1111144321066161251919020811840⟩, ⟨.privateRow 13 13, 15481725692731076636865806198400⟩, ⟨.privateRow 13 14, 23525776886290184028462453914400⟩, ⟨.privateRow 13 15, 14253364152235123686647700595200⟩, ⟨.privateRow 13 16, 26090586417954700782523320537600⟩, ⟨.privateRow 14 5, 9986778328166548862657128425⟩, ⟨.privateRow 14 6, 53262817750221593934171351600⟩, ⟨.privateRow 14 7, 163592940232823467083526294200⟩, ⟨.privateRow 14 8, 446588241136473364524975178800⟩, ⟨.privateRow 14 9, 1238360512692652058969483924700⟩, ⟨.privateRow 14 10, 2939139124944046138003819129200⟩, ⟨.privateRow 14 11, 1901482593682910903449917252120⟩, ⟨.privateRow 14 12, 18067931399047391809002792937200⟩, ⟨.privateRow 14 13, 29707336600186094016784071354900⟩, ⟨.privateRow 14 14, 24234582076350825240047964978000⟩, ⟨.privateRow 15 3, 6266213852967246345196629600⟩, ⟨.privateRow 15 4, 26631408875110796967085675800⟩, ⟨.privateRow 15 5, 92322217433717429485897009440⟩, ⟨.privateRow 15 6, 311967932537012193043003630800⟩, ⟨.privateRow 15 8, 3834922878015954763260337315200⟩, ⟨.privateRow 15 9, 4057658297698699610621417512800⟩, ⟨.privateRow 15 10, 3696439551865378619031491801040⟩, ⟨.privateRow 15 11, 24181319258600603646113793626400⟩, ⟨.privateRow 15 12, 44274717254871699957779936017500⟩, ⟨.privateRow 15 16, 70200393794792060805237841408800⟩, ⟨.privateRow 16 2, 15665534632418115862991574000⟩, ⟨.privateRow 16 3, 66578522187776992417714189500⟩, ⟨.privateRow 16 4, 195296998417479177758628289200⟩, ⟨.privateRow 16 5, 722852526610150203392325486000⟩, ⟨.privateRow 16 7, 7656530051594354128037131792500⟩, ⟨.privateRow 16 8, 8715733813672624461955312080000⟩, ⟨.privateRow 16 9, 8149211115783903871928216794800⟩, ⟨.privateRow 16 11, 34054914099047931621660807929250⟩, ⟨.privateRow 16 14, 31584850925881405202963611498800⟩, ⟨.privateRow 16 18, 1294286471330384732600363843880000⟩, ⟨.privateRow 17 1, 50129710823737970761573036800⟩, ⟨.privateRow 17 2, 213051271000886375736685406400⟩, ⟨.privateRow 17 3, 397695705868321234708479425280⟩, ⟨.privateRow 17 4, 2373999876867019615351637385600⟩, ⟨.privateRow 17 6, 18464443486743485897179401888000⟩, ⟨.privateRow 17 7, 23861742352099274082508765516800⟩, ⟨.privateRow 17 8, 23435639810097501331035394704000⟩, ⟨.privateRow 17 9, 8332671932479111584368140339200⟩, ⟨.privateRow 17 11, 129291685601680760589919943769600⟩, ⟨.privateRow 18 0, 426102542001772751473370812800⟩, ⟨.privateRow 18 1, 679100926315325322660684732900⟩, ⟨.privateRow 18 2, 482916214268675785003153587840⟩, ⟨.privateRow 18 3, 10865614821045205162570955726400⟩, ⟨.privateRow 18 6, 194922544668447316855818357273600⟩, ⟨.privateRow 18 7, 32959031623837122326465232370080⟩, ⟨.privateRow 18 8, 53925643926668795992018817308800⟩, ⟨.privateRow 18 9, 14487486428060273550094607635200⟩, ⟨.privateRow 18 11, 594590588818307060285132855028000⟩, ⟨.privateRow 19 0, 8149211115783903871928216794800⟩, ⟨.privateRow 19 2, 9313384132324461567917962051200⟩, ⟨.privateRow 19 3, 73551854173229081100480315686400⟩, ⟨.privateRow 19 6, 54328074105226025812854778632000⟩, ⟨.privateRow 19 8, 65193688926271230975425734358400⟩, ⟨.privateRow 19 10, 304237214989265744551986760339200⟩, ⟨.privateRow 19 15, 32531650774209344256737441444841600⟩, ⟨.privateRow 20 0, 137631121066572598725898772534400⟩, ⟨.privateRow 20 2, 444654391138157626652903726649600⟩, ⟨.privateRow 20 4, 75071520581766872032308421382400⟩, ⟨.hall 19 3, 42650523231619200923849949290880⟩, ⟨.hall 15 5, 1511586675057888372744801000⟩, ⟨.hall 19 7, 1572010473720759286146629336640⟩, ⟨.hall 16 11, 16468895382798532061093706000⟩, ⟨.hall 11 14, 115515487968159699631411200⟩, ⟨.hall 19 14, 1651573452798871184710785270412800⟩, ⟨.hall 17 15, 8948153382037227780940787068800⟩, ⟨.hall 7 18, 1516640960456567242987193504⟩, ⟨.hall 9 18, 438340021307748860208480000⟩, ⟨.hall 8 19, 2177892395867550211945832880⟩, ⟨.hall 4 25, 1109887894753240077300625022080⟩, ⟨.hall 5 25, 1451602961126623626524740680000⟩, ⟨.hall 7 26, 135906983929028388611140781375200⟩, ⟨.hall 6 27, 4469397172030558707574748479938000⟩, ⟨.hall 3 30, 43313845713725234618382852414374400⟩, ⟨.hall 2 31, 51960049175164486412736970968377700⟩]
  caps := #[0, 3140014798175996856512875379616000, 268142630579624483160373790294400, 24488386044542005498921740431700, 6446024670601566594415699027200, 1501262240442446013939415008000, 188373135358848572027842174800, 0, 1059796615498090483257663524820, 131776922047705459553317660800, 68249577041684174643383741700, 309939972561116977610367084000, 4214200964852697542044326720, 308245699976596442199759776640, 184762658983179928599953321460, 0, 0, 25897792485739745556908884241280, 0, 19452825946186234021864915099200, 0, 273126897808314104617920000000] }

theorem case_55_34_21_checked :
    (Witness.linear .conditional case_55_34_21).check 55 34 21 = true := by
  change case_55_34_21.check 55 34 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_34_22 : Certificate := {
  objectiveScale := 1579504856707367365776000000
  eta := 177504676342715494064248084031904000
  rows := #[⟨.count 2, 30977796834970691148257427941328000⟩, ⟨.count 3, 4975252226578760664237405443337600⟩, ⟨.count 4, 809537086592496373996007265542400⟩, ⟨.count 5, 117284421402827994875863054752000⟩, ⟨.count 6, 16327638932751556142835450348000⟩, ⟨.count 7, 1853407662636663129727267336800⟩, ⟨.count 8, 156902235990405344315535859200⟩, ⟨.path 8, 58644055054984213975643683200⟩, ⟨.path 9, 7798036927336269524951040000⟩, ⟨.privateRow 2 32, 3667923183527204534732321222500800⟩, ⟨.privateRow 3 31, 5689431979248088190225645790451200⟩, ⟨.privateRow 5 24, 7792811054190132101004947673600⟩, ⟨.privateRow 6 22, 4143199669121641123332118782000⟩, ⟨.privateRow 6 23, 10251763283852265856449986217000⟩, ⟨.privateRow 6 27, 604796829807078850248767481021000⟩, ⟨.privateRow 7 19, 142737450796827084064827760800⟩, ⟨.privateRow 7 20, 1354507584135921136473961909500⟩, ⟨.privateRow 7 21, 3946371417722962990507718887200⟩, ⟨.privateRow 7 22, 9249059931976081702933514866800⟩, ⟨.privateRow 8 17, 78451117995202672157767929600⟩, ⟨.privateRow 8 18, 415681965488469714280395349200⟩, ⟨.privateRow 8 19, 1290153151405481444469542904750⟩, ⟨.privateRow 8 20, 3158357955717579006780139237200⟩, ⟨.privateRow 8 21, 8336248486136067277931152602600⟩, ⟨.privateRow 8 22, 9838750835573355121986070470960⟩, ⟨.privateRow 9 14, 1005783564041059899458563200⟩, ⟨.privateRow 9 15, 27430460837483451803415360000⟩, ⟨.privateRow 9 16, 130651284968933680939667359680⟩, ⟨.privateRow 9 17, 412036000068820872144858057600⟩, ⟨.privateRow 9 18, 1057958586425689881742976166000⟩, ⟨.privateRow 9 19, 2915191818689866328587826966400⟩, ⟨.privateRow 9 20, 6673373947412432432907566832000⟩, ⟨.privateRow 9 22, 33125984573474328318617508273600⟩, ⟨.privateRow 9 23, 7818961426855199658390870316800⟩, ⟨.privateRow 9 24, 25273329397223753153594776089600⟩, ⟨.privateRow 10 12, 522233773636704178565023200⟩, ⟨.privateRow 10 13, 8674883239854141632830107600⟩, ⟨.privateRow 10 14, 41762876625068555370699885600⟩, ⟨.privateRow 10 15, 135328178541724609472149678560⟩, ⟨.privateRow 10 16, 358058948798617324207248499200⟩, ⟨.privateRow 10 17, 1029388047059648523973981355100⟩, ⟨.privateRow 10 18, 2467007478384855458389809357600⟩, ⟨.privateRow 10 19, 5152503475636844732438786953200⟩, ⟨.privateRow 10 20, 3882425135554895317899999808320⟩, ⟨.privateRow 10 21, 15008868095875468915914125512200⟩, ⟨.privateRow 10 22, 16638426054040243651768146376800⟩, ⟨.privateRow 11 10, 146948897343661348946868000⟩, ⟨.privateRow 11 11, 2690295197522415465334968000⟩, ⟨.privateRow 11 12, 13715230418741725901707680000⟩, ⟨.privateRow 11 13, 46569441467273042038980168000⟩, ⟨.privateRow 11 14, 128168828263141428551458269600⟩, ⟨.privateRow 11 15, 384712213245705411542900424000⟩, ⟨.privateRow 11 16, 986210787297647228119667865000⟩, ⟨.privateRow 11 17, 2198355504261173780245145280000⟩, ⟨.privateRow 11 18, 4326812316352545978841230348000⟩, ⟨.privateRow 11 19, 5070794990417190900379363449600⟩, ⟨.privateRow 11 21, 35002639551670758673748170128000⟩, ⟨.privateRow 12 9, 969862722468164903049328800⟩, ⟨.privateRow 12 10, 4874181887275905666606883200⟩, ⟨.privateRow 12 11, 16972597643192885803363254000⟩, ⟨.privateRow 12 12, 48963372594907961469096417600⟩, ⟨.privateRow 12 13, 152527077486826733752891109280⟩, ⟨.privateRow 12 14, 414131382493906413602063397600⟩, ⟨.privateRow 12 15, 985542169814733568981959615600⟩, ⟨.privateRow 12 16, 2052552808316792989820062850400⟩, ⟨.privateRow 12 17, 3797713014873537047868102322800⟩, ⟨.privateRow 12 19, 13374406942835994013050244152000⟩, ⟨.privateRow 12 20, 5523260441931480437876699812800⟩, ⟨.privateRow 12 22, 39521259365429407689324782380800⟩, ⟨.privateRow 13 7, 402313425616423959783425280⟩, ⟨.privateRow 13 8, 1939725444936329806098657600⟩, ⟨.privateRow 13 9, 6963116981822722380866976000⟩, ⟨.privateRow 13 10, 20367117171831462964035904800⟩, ⟨.privateRow 13 11, 65833106009960284328196864000⟩, ⟨.privateRow 13 12, 188886153326911049118318168960⟩, ⟨.privateRow 13 13, 479088237671558198775428937600⟩, ⟨.privateRow 13 14, 1068519313848121010687291079600⟩, ⟨.privateRow 13 15, 2100507131816607810026390774400⟩, ⟨.privateRow 13 16, 3694745922504833540661031915200⟩, ⟨.privateRow 13 17, 2360775181517175796009139543040⟩, ⟨.privateRow 13 18, 5944180863482664005800108512000⟩, ⟨.privateRow 13 20, 17557963677464782664848137782400⟩, ⟨.privateRow 14 5, 306449679668760438116280975⟩, ⟨.privateRow 14 6, 980638974940033401972099120⟩, ⟨.privateRow 14 7, 3152053848021535934910318600⟩, ⟨.privateRow 14 8, 9806389749400334019720991200⟩, ⟨.privateRow 14 9, 31870766685551085564093221400⟩, ⟨.privateRow 14 10, 95835172550957809738182414000⟩, ⟨.privateRow 14 11, 258888689384168818120634167680⟩, ⟨.privateRow 14 12, 618892153073265524800169222400⟩, ⟨.privateRow 14 13, 1306701434107594508127822077400⟩, ⟨.privateRow 14 15, 1840332476304129351034306015200⟩, ⟨.privateRow 14 16, 279482107857909519562048249200⟩, ⟨.privateRow 14 18, 33827141440556452201027559144400⟩, ⟨.privateRow 15 4, 612899359337520876232561950⟩, ⟨.privateRow 15 5, 1961277949880066803944198240⟩, ⟨.privateRow 15 6, 5603651285371619439840566400⟩, ⟨.privateRow 15 7, 18104104152739078190254137600⟩, ⟨.privateRow 15 8, 56386741059051920613395699400⟩, ⟨.privateRow 15 9, 159576705922059980866368856800⟩, ⟨.privateRow 15 10, 407945813575053895220393233920⟩, ⟨.privateRow 15 11, 927248630748853805642507056800⟩, ⟨.privateRow 15 12, 1876697838291488923024104690900⟩, ⟨.privateRow 15 13, 963828021083918543652577420800⟩, ⟨.privateRow 15 14, 1577194351361887054838459418000⟩, ⟨.privateRow 15 15, 1943626448331146202708700455840⟩, ⟨.privateRow 15 17, 13771440004741202408361511975200⟩, ⟨.privateRow 15 19, 93758892394016593562552396863200⟩, ⟨.privateRow 16 3, 1532248398343802190581404875⟩, ⟨.privateRow 16 4, 3268796583133444673240330400⟩, ⟨.privateRow 16 5, 12257987186750417524651239000⟩, ⟨.privateRow 16 6, 39602727834116733541180926000⟩, ⟨.privateRow 16 7, 116450878274128966484186770500⟩, ⟨.privateRow 16 8, 314250216969419794722877218000⟩, ⟨.privateRow 16 9, 757543608141175803023446570200⟩, ⟨.privateRow 16 10, 1628950297261499928831431316000⟩, ⟨.privateRow 16 11, 3141109216604794490691879993750⟩, ⟨.privateRow 16 12, 2598693283591088515226062668000⟩, ⟨.privateRow 16 13, 1703860218958308035926522221000⟩, ⟨.privateRow 17 2, 4903194874700167009860495600⟩, ⟨.privateRow 17 3, 10460149066027022954369057280⟩, ⟨.privateRow 17 4, 33621907712229716639043398400⟩, ⟨.privateRow 17 5, 108624624916434469141524825600⟩, ⟨.privateRow 17 6, 294191692482010020591629736000⟩, ⟨.privateRow 17 7, 763115420498789629171015315200⟩, ⟨.privateRow 17 8, 1749459931293019589118224830080⟩, ⟨.privateRow 17 9, 3626185009556034624181273190400⟩, ⟨.privateRow 17 10, 6805634486083831809686367892800⟩, ⟨.privateRow 17 11, 7699416866100605110340938233600⟩, ⟨.privateRow 17 12, 5713856427317261288824097539200⟩, ⟨.privateRow 17 13, 2573196670242647646774788090880⟩, ⟨.privateRow 18 1, 20838578217475709791907106300⟩, ⟨.privateRow 18 2, 44455633530614847556068493440⟩, ⟨.privateRow 18 3, 119077589814146913096612036000⟩, ⟨.privateRow 18 4, 359064732362658384106707062400⟩, ⟨.privateRow 18 5, 972466983482199790288998294000⟩, ⟨.privateRow 18 6, 2394542078808117925179143851200⟩, ⟨.privateRow 18 7, 5334676023673781706728219212800⟩, ⟨.privateRow 18 8, 10891630215000637651236780892800⟩, ⟨.privateRow 18 9, 20380129496691244176485149961400⟩, ⟨.privateRow 18 10, 28388097411692624082232309382400⟩, ⟨.privateRow 18 13, 129282539261219303548991687485200⟩, ⟨.privateRow 19 0, 125031469304854258751442637800⟩, ⟨.privateRow 19 1, 133366900591844542668205480320⟩, ⟨.privateRow 19 2, 571572431107905182863737772800⟩, ⟨.privateRow 19 3, 1692733738281103810788761865600⟩, ⟨.privateRow 19 7, 6223788694286078657849589081600⟩, ⟨.privateRow 19 9, 407245357164382442790413163120000⟩, ⟨.privateRow 19 11, 116029203514904752121338767878400⟩, ⟨.privateRow 20 0, 3800956666867569466043856189120⟩, ⟨.privateRow 20 5, 26606696668072986262306993323840⟩, ⟨.privateRow 20 7, 23755979167922309162774101182000⟩, ⟨.privateRow 20 8, 1422643781027576000147843316499200⟩, ⟨.privateRow 20 9, 2236229505673753369189135391265600⟩, ⟨.hall 19 2, 3438960793832562850230155599680⟩, ⟨.hall 16 8, 3759586691255084864821046400⟩, ⟨.hall 15 9, 1216536691941023055987384000⟩, ⟨.hall 18 11, 469898489035825895527399803600⟩, ⟨.hall 19 12, 23098121283272152909035741456960⟩, ⟨.hall 17 14, 336686048062744801343754031200⟩, ⟨.hall 9 15, 24154054938420194170118736⟩, ⟨.hall 16 15, 79156152552349101401015844000⟩, ⟨.hall 13 17, 1515607438294955550249276000⟩, ⟨.hall 15 17, 143655007732443489587140836000⟩, ⟨.hall 10 20, 2716424906693334066401886000⟩, ⟨.hall 5 25, 170405169355922102505968064000⟩, ⟨.hall 7 26, 396891106730516933496013685432800⟩, ⟨.hall 6 27, 740244085938617606634013771617000⟩, ⟨.hall 4 29, 1949423985950991680181159505837440⟩, ⟨.hall 3 30, 2713650743606929772777762251420800⟩]
  caps := #[0, 9309939193698233058635402736000, 11037108439488520701079303536000, 4083463894091134093188138691200, 0, 127689246256766672996534016000, 0, 156754057478267319321993627600, 10066939219830389647020510240, 39457142775194948057172272640, 0, 33419782029946052767442066400, 6033526374195556529763581760, 4327329803744519725312286160, 19549620289199460224056760325, 0, 378870201728593782880218159900, 51693683107553189332529225040, 5305888917217336821810954496980, 13659106845543699934129045184160, 0, 102667815685978878775440000000] }

theorem case_55_34_22_checked :
    (Witness.linear .conditional case_55_34_22).check 55 34 22 = true := by
  change case_55_34_22.check 55 34 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_35_1_checked :
    (Witness.rising).check 55 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_35_2_checked :
    (Witness.rising).check 55 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_35_3_checked :
    (Witness.rising).check 55 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_35_4_checked :
    (Witness.rising).check 55 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_35_5_checked :
    (Witness.rising).check 55 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_35_6_checked :
    (Witness.rising).check 55 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_35_7_checked :
    (Witness.rising).check 55 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_35_8_checked :
    (Witness.rising).check 55 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_35_9_checked :
    (Witness.rising).check 55 35 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_35_10_checked :
    (Witness.rising).check 55 35 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_35_11_checked :
    (Witness.linear .positive case_55_35_11).check 55 35 11 = true := by
  change case_55_35_11.check 55 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_35_12_checked :
    (Witness.linear .positive case_55_35_12).check 55 35 12 = true := by
  change case_55_35_12.check 55 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_35_13_checked :
    (Witness.linear .positive case_55_35_13).check 55 35 13 = true := by
  change case_55_35_13.check 55 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_35_14_checked :
    (Witness.linear .positive case_55_35_14).check 55 35 14 = true := by
  change case_55_35_14.check 55 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_55_35_15_checked :
    (Witness.linear .positive case_55_35_15).check 55 35 15 = true := by
  change case_55_35_15.check 55 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_16 : Certificate := {
  objectiveScale := 36919638044901637513488000000
  eta := 25947224091177545358537417735704251200
  rows := #[⟨.count 2, 1887235415518429584356185967084755200⟩, ⟨.count 3, 241373034758552145081526582520832000⟩, ⟨.count 4, 43453062262293272196662077171948800⟩, ⟨.count 5, 7644588685099671567954292422822000⟩, ⟨.count 6, 1423538884528838478192214066644000⟩, ⟨.count 7, 255127748136337285701981222333600⟩, ⟨.count 8, 47783123396772200666591800838400⟩, ⟨.count 9, 8532700606566464404748535864000⟩, ⟨.count 10, 1551400110284811709954279248000⟩, ⟨.count 11, 853270060656646440474853586400⟩, ⟨.path 2, 577203840931850193529474434195768000⟩, ⟨.path 9, 183686052223885018579265894400⟩, ⟨.path 10, 321806368636734658242219413760⟩, ⟨.privateRow 2 33, 170469705798227452463828148905337600⟩, ⟨.privateRow 4 30, 95258785148354456399132496101167200⟩, ⟨.privateRow 5 25, 1786202362254042566684040031241400⟩, ⟨.privateRow 5 29, 65504973709903642804294193258870400⟩, ⟨.privateRow 6 22, 191499873752093747661571654203300⟩, ⟨.privateRow 6 23, 639492050539114576721598205324800⟩, ⟨.privateRow 6 25, 3352403260535446459465646979456000⟩, ⟨.privateRow 6 28, 21870117520798246213230945892263600⟩, ⟨.privateRow 7 19, 19781644239556586645008688978040⟩, ⟨.privateRow 7 20, 103295338559915717238437301888000⟩, ⟨.privateRow 7 21, 241757311025155013353469007653850⟩, ⟨.privateRow 7 22, 360846167284225051826937061579200⟩, ⟨.privateRow 7 25, 4641753577052962609248183724449900⟩, ⟨.privateRow 7 27, 1819699984119424325555538946044000⟩, ⟨.privateRow 8 16, 865121033721322085481448775100⟩, ⟨.privateRow 8 17, 15423502763081503083128792857200⟩, ⟨.privateRow 8 18, 46531660641142452553895348911680⟩, ⟨.privateRow 8 19, 98220864760031745814660923945600⟩, ⟨.privateRow 8 20, 167703119838225052488328515293700⟩, ⟨.privateRow 8 22, 673514501211646257014817764198400⟩, ⟨.privateRow 8 23, 30888376195770601145189699827680⟩, ⟨.privateRow 8 24, 1880109472818532377716300306500200⟩, ⟨.privateRow 9 14, 1290844450736977948410675938400⟩, ⟨.privateRow 9 15, 8335184388821870321305282719000⟩, ⟨.privateRow 9 16, 21616174869968376492029624188800⟩, ⟨.privateRow 9 17, 43052214949353683179959001509360⟩, ⟨.privateRow 9 18, 73918469328736889787803056984800⟩, ⟨.privateRow 9 19, 114551505643154784633749093974200⟩, ⟨.privateRow 9 20, 47430980197136124357824400945600⟩, ⟨.privateRow 9 21, 406646389092570298992969574926000⟩, ⟨.privateRow 9 22, 164738006377443206107678399080960⟩, ⟨.privateRow 9 23, 742581972232575916113254523942000⟩, ⟨.privateRow 10 12, 997328642325950384970608088000⟩, ⟨.privateRow 10 13, 4379721849804045365794003723200⟩, ⟨.privateRow 10 14, 10846872437741308538763669075600⟩, ⟨.privateRow 10 15, 21014419675676085889380691632000⟩, ⟨.privateRow 10 16, 35697716537653517446047965496480⟩, ⟨.privateRow 10 17, 55591837285205752940028339720000⟩, ⟨.privateRow 10 18, 96099540581454805358480385168300⟩, ⟨.privateRow 10 19, 48702882033583910466064694964000⟩, ⟨.privateRow 10 20, 252425726277591238640477519310000⟩, ⟨.privateRow 10 21, 186431751252925823185205737232160⟩, ⟨.privateRow 10 22, 371986961443540727754287306689200⟩, ⟨.privateRow 10 24, 923470915647034170350284722372000⟩, ⟨.privateRow 11 10, 656759380020570290547311548320⟩, ⟨.privateRow 11 11, 2482240176455698735926846796800⟩, ⟨.privateRow 11 12, 6032559659607479379860678152800⟩, ⟨.privateRow 11 13, 11641964994262274540115237190200⟩, ⟨.privateRow 11 14, 8575011518665141087747288934400⟩, ⟨.privateRow 11 15, 52142557706672521571563325525280⟩, ⟨.privateRow 11 17, 157854961221479591487847913484000⟩, ⟨.privateRow 11 19, 150343599020850628125485944791600⟩, ⟨.privateRow 11 22, 611122360109692079412823167108000⟩, ⟨.privateRow 12 8, 420709543795985397734129198850⟩, ⟨.privateRow 12 9, 1580129741956752667546025160000⟩, ⟨.privateRow 12 10, 3860031226780067230719575748000⟩, ⟨.privateRow 12 11, 7591915667893751662686517807200⟩, ⟨.privateRow 12 12, 11779867226287591136555617567800⟩, ⟨.privateRow 12 14, 74139687492610835161259500507200⟩, ⟨.privateRow 12 16, 26392117015032661429687485234900⟩, ⟨.privateRow 12 17, 270689768766408504116355932980800⟩, ⟨.privateRow 12 19, 92930590383960537883716831709920⟩, ⟨.privateRow 12 20, 48067546750324416146750085367200⟩, ⟨.privateRow 13 6, 284423353552215480158284528800⟩, ⟨.privateRow 13 7, 1146581644007368654388084506725⟩, ⟨.privateRow 13 8, 2891637427780857381609226042800⟩, ⟨.privateRow 13 9, 5850994701645575591827567449600⟩, ⟨.privateRow 13 10, 10140786490111682696412683007600⟩, ⟨.privateRow 13 12, 3089871886317249988992272835600⟩, ⟨.privateRow 13 13, 123155312088109302908537200970400⟩, ⟨.privateRow 13 15, 18096435869759709925070853144900⟩, ⟨.privateRow 13 17, 535877300038503315908221242636600⟩, ⟨.privateRow 14 4, 220089499772547692979624933000⟩, ⟨.privateRow 14 5, 963215222533973432804946765600⟩, ⟨.privateRow 14 6, 2575047147338808007861611716100⟩, ⟨.privateRow 14 7, 5423005274395575155017958349120⟩, ⟨.privateRow 14 9, 30738038137464430105677463719600⟩, ⟨.privateRow 14 12, 176423743017674230692467346292800⟩, ⟨.privateRow 14 14, 726295349249407386832762278900⟩, ⟨.privateRow 14 16, 294391714895759794129546310380800⟩, ⟨.privateRow 14 17, 789364196304228653733003599700480⟩, ⟨.privateRow 15 2, 194605452430463223266194677600⟩, ⟨.privateRow 15 3, 924375899044700310514424718600⟩, ⟨.privateRow 15 4, 2718752644249118560336543290000⟩, ⟨.privateRow 15 5, 6085474668710943710886629397450⟩, ⟨.privateRow 15 6, 9942176336391887784199590306720⟩, ⟨.privateRow 15 8, 66602468623477124937064960494000⟩, ⟨.privateRow 15 11, 294013160956151012097621355496040⟩, ⟨.privateRow 15 12, 88123835708928096269041823173200⟩, ⟨.privateRow 15 13, 693281924283525232885818538950⟩, ⟨.privateRow 15 15, 293129868430397187356463127431600⟩, ⟨.privateRow 15 17, 524737385357708209602021765258600⟩, ⟨.privateRow 15 19, 3514477168167950580575842780117200⟩, ⟨.privateRow 16 1, 1459540893228474174496460082000⟩, ⟨.privateRow 16 2, 3286669863270045548495732332800⟩, ⟨.privateRow 16 3, 8482508250057249908250015064800⟩, ⟨.privateRow 16 4, 16638766182804605589259644934800⟩, ⟨.privateRow 16 5, 25882525173251608694403892120800⟩, ⟨.privateRow 16 9, 545549848781654037805422297559200⟩, ⟨.privateRow 16 10, 227581346344805216448651365719320⟩, ⟨.privateRow 16 14, 1361605699292843557387747610497800⟩, ⟨.privateRow 16 19, 5904913243097545583566145102416800⟩, ⟨.privateRow 17 0, 9341061716662234716777344524800⟩, ⟨.privateRow 17 1, 12735845720171426500420962789600⟩, ⟨.privateRow 17 2, 31755030884829704784730825627200⟩, ⟨.privateRow 17 3, 58235681639816119562408757271800⟩, ⟨.privateRow 17 5, 67611494330126651283340779417600⟩, ⟨.privateRow 17 7, 185491430408303195643227893532400⟩, ⟨.privateRow 17 9, 140505136654794447198192557227200⟩, ⟨.privateRow 17 12, 8070065706059960768022503343297600⟩, ⟨.privateRow 18 0, 197884914684383992399013884204000⟩, ⟨.privateRow 18 1, 88740086308291229809384772985600⟩, ⟨.privateRow 18 3, 620194603199057595001144691199360⟩, ⟨.privateRow 18 5, 25787717388734203534351130611200⟩, ⟨.privateRow 18 6, 691433172485435832264789689512800⟩, ⟨.privateRow 18 7, 144762868068576097113289301385600⟩, ⟨.privateRow 18 12, 28774794652929248777080136573664000⟩, ⟨.privateRow 19 4, 18393089427514670670875943908438400⟩, ⟨.privateRow 19 12, 358212669396363792810053043872322240⟩, ⟨.hall 17 5, 5037604105904980528200304022000⟩, ⟨.hall 15 6, 3434213866419939234109317840⟩, ⟨.hall 17 8, 2782943654622014092053787342400⟩, ⟨.hall 14 9, 354323652884596905106516920⟩, ⟨.hall 15 10, 58337607346236147246087771000⟩, ⟨.hall 10 11, 393384029849106751733257980⟩, ⟨.hall 16 11, 282368695683417225915655022400⟩, ⟨.hall 18 13, 157355188757380698572712642097680⟩, ⟨.hall 16 18, 49818995822198585156145837465600⟩, ⟨.hall 8 19, 2151935889380567512457329248⟩, ⟨.hall 10 20, 16185602882192191432856333280⟩, ⟨.hall 12 20, 253748672282608954630203024000⟩, ⟨.hall 6 21, 8995562108735396234255134920⟩, ⟨.hall 9 21, 18051240748096521534886078608⟩, ⟨.hall 11 23, 24922596355012881448869681836100⟩, ⟨.hall 5 24, 93097923269540628020063922440⟩, ⟨.hall 3 30, 729071671794118831198558483095150⟩, ⟨.hall 4 30, 5108757226823561767735979296396800⟩, ⟨.hall 2 32, 160503925196453897988871180157318400⟩]
  caps := #[0, 599951669987623001675833739332800, 0, 44058442880327545859255295989760, 0, 3210132849193828813536805764240, 5086895054463360738937266389460, 0, 826978764707740237603200470280, 386054091225252664517778995520, 1189493117435954070169722555480, 0, 794002771046740893494984281770, 922072702298456641646457221940, 67185215720040874699043400600, 8602644199222804396319247113520, 22695217303686241992614242225920, 69896972743450989679458610094400, 0, 0, 0] }

theorem case_55_35_16_checked :
    (Witness.linear .positive case_55_35_16).check 55 35 16 = true := by
  change case_55_35_16.check 55 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_17 : Certificate := {
  objectiveScale := 3925940394026851200000
  eta := 3906370729958742437644312220160
  rows := #[⟨.count 2, 311584188242204984475175847040⟩, ⟨.count 3, 40870313708959746740852323200⟩, ⟨.count 4, 7046699485612601066518506240⟩, ⟨.count 5, 1183391851742478542637673200⟩, ⟨.count 6, 211889961402383532455066880⟩, ⟨.count 7, 37012829796249687560260080⟩, ⟨.count 8, 7104791605208126334785280⟩, ⟨.count 9, 1567233442325321985614400⟩, ⟨.count 10, 427427302452360541531200⟩, ⟨.count 11, 156723344232532198561440⟩, ⟨.path 2, 78780835824204380851781596800⟩, ⟨.path 9, 173520055528449109159680⟩, ⟨.privateRow 2 33, 27777958978462471937426748480⟩, ⟨.privateRow 4 28, 2403796533281206772835606480⟩, ⟨.privateRow 5 24, 46326674253497315360482800⟩, ⟨.privateRow 5 25, 211267421451682085110781160⟩, ⟨.privateRow 5 26, 574615693405630470545615664⟩, ⟨.privateRow 5 27, 1081351894368414037024295640⟩, ⟨.privateRow 6 22, 40153826820243353706428940⟩, ⟨.privateRow 6 23, 97779196932250703659629840⟩, ⟨.privateRow 6 24, 194383383394779195015759360⟩, ⟨.privateRow 6 25, 342306421620239465197977168⟩, ⟨.privateRow 6 26, 668579609782868018338123020⟩, ⟨.privateRow 6 27, 590469710816827329580092000⟩, ⟨.privateRow 7 19, 2590412989671996481936944⟩, ⟨.privateRow 7 20, 18568399395380832043846800⟩, ⟨.privateRow 7 21, 40250846033339683162681260⟩, ⟨.privateRow 7 22, 73020817742573105752192560⟩, ⟨.privateRow 7 24, 471435760277684093821273344⟩, ⟨.privateRow 7 25, 233488863717953877653239620⟩, ⟨.privateRow 7 26, 407771752643872704628500960⟩, ⟨.privateRow 8 17, 2037403475022918581298720⟩, ⟨.privateRow 8 18, 7849227490312654277952120⟩, ⟨.privateRow 8 19, 16801322958557942545781040⟩, ⟨.privateRow 8 20, 29392157182942809405210060⟩, ⟨.privateRow 8 21, 47076707400895862310741120⟩, ⟨.privateRow 8 22, 29712134010750895977273000⟩, ⟨.privateRow 8 23, 225253238553944111252405664⟩, ⟨.privateRow 8 24, 169718321525146326692159400⟩, ⟨.privateRow 9 14, 9376610338698507606240⟩, ⟨.privateRow 9 15, 1123183966999814089690320⟩, ⟨.privateRow 9 16, 3485907111111473749821120⟩, ⟨.privateRow 9 17, 7381669513352266552243824⟩, ⟨.privateRow 9 18, 12870662788084002281860480⟩, ⟨.privateRow 9 19, 20186837422395883464705480⟩, ⟨.privateRow 9 20, 35695607403057214558065120⟩, ⟨.privateRow 9 21, 26465929186230761457069840⟩, ⟨.privateRow 9 22, 37530016832217043815512832⟩, ⟨.privateRow 9 24, 360260531844152255693176800⟩, ⟨.privateRow 10 12, 8141472427664010314880⟩, ⟨.privateRow 10 13, 560039362956810863390880⟩, ⟨.privateRow 10 14, 1690712440811559475390080⟩, ⟨.privateRow 10 15, 3546351376104736856704320⟩, ⟨.privateRow 10 16, 6233314827430257897330000⟩, ⟨.privateRow 10 17, 9778586841660115055697120⟩, ⟨.privateRow 10 18, 16940368753861889462686560⟩, ⟨.privateRow 10 20, 72750501473516499504952080⟩, ⟨.privateRow 10 22, 12178116225705172429126440⟩, ⟨.privateRow 10 23, 89579264209515828159572160⟩, ⟨.privateRow 11 10, 3799353799576538146944⟩, ⟨.privateRow 11 11, 279863114700950354574000⟩, ⟨.privateRow 11 12, 899789270034328216915680⟩, ⟨.privateRow 11 13, 1924610159097990105061320⟩, ⟨.privateRow 11 14, 3424599356618306884268160⟩, ⟨.privateRow 11 15, 5443999075568232097302384⟩, ⟨.privateRow 11 16, 9406566782118245695475520⟩, ⟨.privateRow 11 17, 14290319478657254105193120⟩, ⟨.privateRow 11 18, 2501467403399767169246880⟩, ⟨.privateRow 11 19, 44412071320924995601433520⟩, ⟨.privateRow 11 21, 50133660683474788517097000⟩, ⟨.privateRow 12 8, 1088356557170362490010⟩, ⟨.privateRow 12 9, 145114207622714998668000⟩, ⟨.privateRow 12 11, 2246367933999628179380640⟩, ⟨.privateRow 12 12, 1663008819356313884735280⟩, ⟨.privateRow 12 13, 3553978866687220058287200⟩, ⟨.privateRow 12 14, 6204503061116802483049008⟩, ⟨.privateRow 12 15, 9571733134794281312141280⟩, ⟨.privateRow 12 16, 5086978548214274278306740⟩, ⟨.privateRow 12 17, 22809465766160122676346720⟩, ⟨.privateRow 12 19, 62619682873353976225215360⟩, ⟨.privateRow 12 21, 8375992063983109723116960⟩, ⟨.privateRow 12 22, 35445596353924365574645680⟩, ⟨.privateRow 13 7, 81626741787777186750750⟩, ⟨.privateRow 13 8, 142792380300751558689312⟩, ⟨.privateRow 13 9, 583981032675983073211080⟩, ⟨.privateRow 13 10, 2764760534153388528468480⟩, ⟨.privateRow 13 11, 2115765147139184680579440⟩, ⟨.privateRow 13 12, 4922537766576352236634320⟩, ⟨.privateRow 13 13, 7783926096882432528551520⟩, ⟨.privateRow 13 14, 11553993210920568193946160⟩, ⟨.privateRow 13 15, 7457419129731323781548520⟩, ⟨.privateRow 13 16, 21792007864714000942828800⟩, ⟨.privateRow 13 17, 11253606801141548146703400⟩, ⟨.privateRow 13 18, 38867389369667985243237120⟩, ⟨.privateRow 13 19, 46266037245312109450325100⟩, ⟨.privateRow 13 21, 3225888835452954420389640⟩, ⟨.privateRow 14 5, 48509606548164728126160⟩, ⟨.privateRow 14 6, 160688071690795661917905⟩, ⟨.privateRow 14 7, 358971088456418988133584⟩, ⟨.privateRow 14 8, 1240459938874498047797520⟩, ⟨.privateRow 14 9, 4354670064746787517171440⟩, ⟨.privateRow 14 10, 3630135556687660488107640⟩, ⟨.privateRow 14 11, 7735077262316448466662240⟩, ⟨.privateRow 14 12, 11816940155132927771532576⟩, ⟨.privateRow 14 13, 17059211636104596057699600⟩, ⟨.privateRow 14 14, 13437161013841629690946320⟩, ⟨.privateRow 14 15, 25994219166023699314460880⟩, ⟨.privateRow 14 16, 25127976191949329169350880⟩, ⟨.privateRow 15 3, 31441411651588249711400⟩, ⟨.privateRow 15 4, 153138169691265122123760⟩, ⟨.privateRow 15 5, 389087469188404590178575⟩, ⟨.privateRow 15 6, 867782961583835692034640⟩, ⟨.privateRow 15 7, 2482074868381095255788520⟩, ⟨.privateRow 15 8, 9429521211324020613446640⟩, ⟨.privateRow 15 9, 7244101244525932733506560⟩, ⟨.privateRow 15 11, 51568945734468983646649824⟩, ⟨.privateRow 15 12, 16437570011450336949119920⟩, ⟨.privateRow 15 14, 97601328374907432989833920⟩, ⟨.privateRow 15 15, 20392899597220138762814040⟩, ⟨.privateRow 16 1, 35743920614437168092960⟩, ⟨.privateRow 16 2, 169783622918576548441560⟩, ⟨.privateRow 16 3, 499363596819342789534000⟩, ⟨.privateRow 16 4, 1103593548970747564870140⟩, ⟨.privateRow 16 5, 2241143822525210439428592⟩, ⟨.privateRow 16 6, 6936873736387556122040880⟩, ⟨.privateRow 16 7, 24501082815019200375105120⟩, ⟨.privateRow 16 9, 41488943491375796564628480⟩, ⟨.privateRow 16 11, 57235945770551249774632560⟩, ⟨.privateRow 16 12, 275813495431227602943314220⟩, ⟨.privateRow 16 14, 142844621415495736088832480⟩, ⟨.privateRow 17 0, 285951364915497344743680⟩, ⟨.privateRow 17 1, 679134491674306193766240⟩, ⟨.privateRow 17 2, 1917556211786276311810560⟩, ⟨.privateRow 17 3, 3905023327127260614155880⟩, ⟨.privateRow 17 4, 8421267696761396802701376⟩, ⟨.privateRow 17 5, 24254803274082364063080000⟩, ⟨.privateRow 17 7, 174990320688079562593767840⟩, ⟨.privateRow 17 8, 32721934598852934790555200⟩, ⟨.privateRow 17 9, 41563030890467539058493888⟩, ⟨.privateRow 17 10, 128733715866262929618356160⟩, ⟨.privateRow 17 13, 1352609529251326502584428000⟩, ⟨.privateRow 17 15, 74025659592499375120520160⟩, ⟨.privateRow 17 16, 170236379246359419237404160⟩, ⟨.privateRow 18 0, 8124460770770403725425760⟩, ⟨.privateRow 18 1, 7244101244525932733506560⟩, ⟨.privateRow 18 2, 9140018367116704191103980⟩, ⟨.privateRow 18 3, 65679851283701790117126144⟩, ⟨.privateRow 18 4, 104457352767048047898331200⟩, ⟨.privateRow 18 5, 15985781111718284253266880⟩, ⟨.privateRow 18 6, 700414039080101121170915520⟩, ⟨.privateRow 18 12, 8476805806302762286991592960⟩, ⟨.privateRow 18 13, 144700922359405506351793536⟩, ⟨.privateRow 18 15, 366883544280052968232384320⟩, ⟨.privateRow 19 0, 199665540552246020967274560⟩, ⟨.privateRow 19 11, 79731747591546895760544108480⟩, ⟨.privateRow 20 15, 7871968778936401118446978230720⟩, ⟨.hall 14 8, 683617778324669772584⟩, ⟨.hall 18 10, 1032949314259871308700400⟩, ⟨.hall 17 15, 7036587927625450285411320⟩, ⟨.hall 14 17, 140791331753533067655048⟩, ⟨.hall 15 17, 1249051448137832151692880⟩, ⟨.hall 16 18, 695147768109574045071886080⟩, ⟨.hall 12 19, 33374137335721236486432⟩, ⟨.hall 13 19, 1069783823194753966479180⟩, ⟨.hall 9 20, 2944816866394189684128⟩, ⟨.hall 11 21, 193942557405014318180280⟩, ⟨.hall 10 23, 4648984293006841490054352⟩, ⟨.hall 6 27, 44311016464168401657309600⟩, ⟨.hall 5 28, 101846755320398539196185440⟩, ⟨.hall 4 30, 8097912048467436821411385600⟩, ⟨.hall 3 31, 15112058262830931779549262090⟩, ⟨.hall 2 32, 26264476894016659025246238720⟩, ⟨.assumptionRow 17, 8502328138823324840034⟩]
  caps := #[0, 643739724820075550480753940, 0, 0, 0, 0, 644350404616889380446036, 159966700020504971301708, 152851723155013006252128, 51844462076270521035378, 139995062056969930790280, 2823035773983872959512, 303188257743439906539702, 306484500256779917275434, 13078715883619798480068, 497416942464955628319204, 269605221674827579332792, 23079375752906147013969630, 0, 0, 0] }

theorem case_55_35_17_checked :
    (Witness.linear .conditional case_55_35_17).check 55 35 17 = true := by
  change case_55_35_17.check 55 35 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_18 : Certificate := {
  objectiveScale := 35300167832709461647680000
  eta := 11703716095303068780695544146914560
  rows := #[⟨.count 2, 1176557233540156551065297490215040⟩, ⟨.count 3, 170104660270866007382934576898560⟩, ⟨.count 4, 28653993575038926377339246910720⟩, ⟨.count 5, 4690385853056967115338269583600⟩, ⟨.count 6, 821212337908963939385824977600⟩, ⟨.count 7, 145291413630047466199030572960⟩, ⟨.count 8, 29155467618069725658668342400⟩, ⟨.count 9, 7288866904517431414667085600⟩, ⟨.count 10, 2650497056188156878060758400⟩, ⟨.count 11, 1457773380903486282933417120⟩, ⟨.path 2, 173384915427604470335222571494400⟩, ⟨.path 8, 701713508540361049039507200⟩, ⟨.path 9, 545014727334154488436945920⟩, ⟨.privateRow 2 33, 96650375153901140558485555056000⟩, ⟨.privateRow 3 30, 16728867403181407291727993603520⟩, ⟨.privateRow 3 31, 29961616297709353573130522067360⟩, ⟨.privateRow 4 27, 2241277980693080043800697708096⟩, ⟨.privateRow 4 28, 6509687032424517996439174149360⟩, ⟨.privateRow 4 29, 10941075148140965715509606624640⟩, ⟨.privateRow 4 30, 18590983926662160566249868531360⟩, ⟨.privateRow 5 24, 216132258163952597233961628720⟩, ⟨.privateRow 5 25, 1171280417850926131495808061000⟩, ⟨.privateRow 5 26, 2288023913774051837273429283744⟩, ⟨.privateRow 5 27, 3836798797980438251418964967460⟩, ⟨.privateRow 5 28, 6757103570127859696125929110560⟩, ⟨.privateRow 5 29, 8346360011247835422411701935800⟩, ⟨.privateRow 6 22, 172928367309676060312976605860⟩, ⟨.privateRow 6 23, 454223674081514852920364731200⟩, ⟨.privateRow 6 24, 845778518957522689709332562400⟩, ⟨.privateRow 6 25, 1364475884525663160825678424320⟩, ⟨.privateRow 6 26, 2390464888746541826122455912360⟩, ⟨.privateRow 6 27, 3145874955989723398570314144960⟩, ⟨.privateRow 6 28, 3275900242825309355639736433080⟩, ⟨.privateRow 7 19, 8573095835313359806775095920⟩, ⟨.privateRow 7 20, 78611779355388001035224271360⟩, ⟨.privateRow 7 21, 178455758045601779135765812440⟩, ⟨.privateRow 7 22, 322619132749950119044431241200⟩, ⟨.privateRow 7 23, 513257711193102462116140611000⟩, ⟨.privateRow 7 24, 883480086607555710613980937440⟩, ⟨.privateRow 7 25, 1176544599504188720850845400600⟩, ⟨.privateRow 7 26, 1302659351397351040113668522160⟩, ⟨.privateRow 7 27, 970339083886388434972097040840⟩, ⟨.privateRow 8 17, 6317017983915107226044807520⟩, ⟨.privateRow 8 18, 32629827509223034632992986536⟩, ⟨.privateRow 8 19, 73536568325575863605752374720⟩, ⟨.privateRow 8 20, 130683309542243780738801955570⟩, ⟨.privateRow 8 21, 205927844497628193253427708880⟩, ⟨.privateRow 8 22, 351809309258041356281264664960⟩, ⟨.privateRow 8 23, 473922126131723390581653905712⟩, ⟨.privateRow 8 24, 534759868561428884789408513520⟩, ⟨.privateRow 8 25, 232757816484256643175035600160⟩, ⟨.privateRow 9 15, 3239496402007747295407593600⟩, ⟨.privateRow 9 16, 13944559512278803130686323360⟩, ⟨.privateRow 9 17, 32038619415856620751581100704⟩, ⟨.privateRow 9 18, 57519058337870890867348161920⟩, ⟨.privateRow 9 19, 90300962205965955859486671600⟩, ⟨.privateRow 9 20, 153575268715181562854429990880⟩, ⟨.privateRow 9 21, 211755081477906414876476368320⟩, ⟨.privateRow 9 22, 149891498520898467358509355872⟩, ⟨.privateRow 10 13, 1478161819797241335841576800⟩, ⟨.privateRow 10 14, 6361192934851576507345820160⟩, ⟨.privateRow 10 15, 15071690078597201156609130720⟩, ⟨.privateRow 10 16, 27830219089975647219637963200⟩, ⟨.privateRow 10 17, 44322200772924178905349348800⟩, ⟨.privateRow 10 18, 75439772461755415141804335960⟩, ⟨.privateRow 10 19, 70522153816434888362688036000⟩, ⟨.privateRow 11 11, 653158203132081516379258320⟩, ⟨.privateRow 11 12, 3109236931297645568494351200⟩, ⟨.privateRow 11 13, 7818966315755062790279237280⟩, ⟨.privateRow 11 14, 15035546936921908108271938560⟩, ⟨.privateRow 11 15, 24702632563673622103526268288⟩, ⟨.privateRow 11 16, 26814195218436853749714672480⟩, ⟨.privateRow 12 9, 291554676180697256586683424⟩, ⟨.privateRow 12 10, 1631317831011044173758823920⟩, ⟨.privateRow 12 11, 4510375759718478926682880320⟩, ⟨.privateRow 12 12, 9192071040696982950719046840⟩, ⟨.privateRow 12 13, 8334340743347204405457718080⟩, ⟨.privateRow 13 7, 136666254459701839025007855⟩, ⟨.privateRow 13 8, 939453956582246715668202144⟩, ⟨.privateRow 13 9, 2898192316796216776784293560⟩, ⟨.privateRow 13 10, 2915546761806972565866834240⟩, ⟨.privateRow 14 5, 79626277108173620496363120⟩, ⟨.privateRow 14 6, 592220435992041302441700705⟩, ⟨.privateRow 14 7, 1143079444708447974236679456⟩, ⟨.privateRow 15 3, 58490907258473215055970440⟩, ⟨.privateRow 15 4, 371589293171476895649694560⟩, ⟨.hall 6 28, 343515081401176692947333153760⟩, ⟨.hall 5 29, 2317819181931518093022940625880⟩, ⟨.hall 4 30, 6931602701317944754875489438720⟩, ⟨.hall 3 31, 16397004618123644887804181319570⟩, ⟨.hall 2 32, 34208375205986827931003372213760⟩, ⟨.assumptionRow 18, 39470578350352423252890912⟩]
  caps := #[0, 6332751458825334399667488300480, 0, 94146251775840678539582595138, 2503529015683504076724758016, 0, 9280610030470648983767330820, 5978612689768821371068182240, 1007665585037142067956731526, 813185820713620139117122560, 1502866244444195606226395160, 0, 1993576142665269745937488728, 313674737603751695109209271, 115551902336492616461362896, 0, 22170006021248582060409221376, 4094522825459786127137654496, 525332106972998963109989088, 35300167832709461647680000, 0] }

theorem case_55_35_18_checked :
    (Witness.linear .conditional case_55_35_18).check 55 35 18 = true := by
  change case_55_35_18.check 55 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_19 : Certificate := {
  objectiveScale := 1249012356924388672000000
  eta := 330610442779739366678719262577600
  rows := #[⟨.count 2, 42502686869087486207757845654400⟩, ⟨.count 3, 5824175691487997333860128158400⟩, ⟨.count 4, 797397289802076329710055712000⟩, ⟨.count 5, 102320891169292980361024848000⟩, ⟨.count 6, 14289641697780571395246573600⟩, ⟨.count 7, 2646229944033439147267884000⟩, ⟨.count 8, 759942958286526114087187200⟩, ⟨.count 9, 325689839265654048894508800⟩, ⟨.count 10, 111030627022382062123128000⟩, ⟨.count 11, 40711229908206756111813600⟩, ⟨.path 2, 1177812891453428915002141824000⟩, ⟨.path 7, 354000682086097198454552250⟩, ⟨.path 8, 6822142625785860605232000⟩, ⟨.privateRow 2 33, 3634861451124332012687165462400⟩, ⟨.privateRow 3 30, 591814625705611812846755212800⟩, ⟨.privateRow 3 31, 1104653988859292319587271132000⟩, ⟨.privateRow 4 27, 77269914365776423100222212800⟩, ⟨.privateRow 4 28, 222812561287615576199955832800⟩, ⟨.privateRow 4 29, 396228830286606954984244497600⟩, ⟨.privateRow 4 30, 711659439615392901338576270400⟩, ⟨.privateRow 5 24, 7081815374032346670307384800⟩, ⟨.privateRow 5 25, 36385661730459788274933405000⟩, ⟨.privateRow 5 26, 76070290124481264020127438720⟩, ⟨.privateRow 5 27, 136501361279724902679901683000⟩, ⟨.privateRow 5 28, 258477860422199594929244091600⟩, ⟨.privateRow 5 29, 345597630690767152633185650400⟩, ⟨.privateRow 6 22, 4575772611557821858817382750⟩, ⟨.privateRow 6 23, 13378162494835720133409858000⟩, ⟨.privateRow 6 24, 27207164165321581751169059200⟩, ⟨.privateRow 6 25, 47843837388124579782603342720⟩, ⟨.privateRow 6 26, 91162621571951978623378603800⟩, ⟨.privateRow 6 27, 132262492943449115897704054000⟩, ⟨.privateRow 6 28, 153128506094735011988568220800⟩, ⟨.privateRow 7 19, 49144270389192441306403560⟩, ⟨.privateRow 7 20, 1901365219046248868777664800⟩, ⟨.privateRow 7 21, 4983733061262977060687848200⟩, ⟨.privateRow 7 22, 10053873630902556215980362000⟩, ⟨.privateRow 7 23, 17664634967670838625135057400⟩, ⟨.privateRow 7 24, 33523953062412197654245136160⟩, ⟨.privateRow 7 25, 49758573769057346822733604500⟩, ⟨.privateRow 7 26, 62505631424066044365862510800⟩, ⟨.privateRow 7 27, 57019954746434819720891310000⟩, ⟨.privateRow 8 16, 7350638733426219853521900⟩, ⟨.privateRow 8 18, 711768002895148119354874440⟩, ⟨.privateRow 8 19, 1938306890629621665990236400⟩, ⟨.privateRow 8 20, 3920152179911075557266717900⟩, ⟨.privateRow 8 21, 6910246619419189626693313200⟩, ⟨.privateRow 8 22, 13155381597838033162464655800⟩, ⟨.privateRow 8 23, 19945788573027430044381209760⟩, ⟨.privateRow 8 24, 25721015795755793455142900700⟩, ⟨.privateRow 8 25, 26326595340640368952306128000⟩, ⟨.privateRow 8 26, 7568896160434106073788011800⟩, ⟨.privateRow 9 16, 244678603993767877641708000⟩, ⟨.privateRow 9 17, 785726737228390392958002480⟩, ⟨.privateRow 9 18, 1640511782967738912950118400⟩, ⟨.privateRow 9 19, 2914810974677858718838876500⟩, ⟨.privateRow 9 20, 5579377127419954480466644800⟩, ⟨.privateRow 9 21, 8700894525381743931230384400⟩, ⟨.privateRow 9 22, 11626222567785889395398146080⟩, ⟨.privateRow 9 23, 8006541881947328701990008000⟩, ⟨.privateRow 10 14, 79571949366040477854908400⟩, ⟨.privateRow 10 15, 324680469929086939238844000⟩, ⟨.privateRow 10 16, 740204180149213747487520000⟩, ⟨.privateRow 10 17, 1350050179683260407223071200⟩, ⟨.privateRow 10 18, 2608757107413385201301328300⟩, ⟨.privateRow 10 19, 4199072570532182558961345600⟩, ⟨.privateRow 10 20, 5169092524708676003287848000⟩, ⟨.privateRow 11 12, 25337758474338470587072800⟩, ⟨.privateRow 11 13, 135087262877231508916472400⟩, ⟨.privateRow 11 14, 354961550026100228908788000⟩, ⟨.privateRow 11 15, 693201214709738674522062480⟩, ⟨.privateRow 11 16, 1373078754176791501589349600⟩, ⟨.privateRow 11 17, 2288156171886256996920796200⟩, ⟨.privateRow 11 18, 307713452033458857884097600⟩, ⟨.privateRow 12 10, 7754519982515572592726400⟩, ⟨.privateRow 12 11, 57065313717486393182371200⟩, ⟨.privateRow 12 12, 177923152932162860044222400⟩, ⟨.privateRow 12 13, 389429643667391899372600800⟩, ⟨.privateRow 12 14, 822819191144756548526543760⟩, ⟨.privateRow 12 15, 330213309255454799573599200⟩, ⟨.privateRow 13 8, 2261734994900375339545200⟩, ⟨.privateRow 13 9, 24717532444268387639315400⟩, ⟨.privateRow 13 10, 92905114405907725485933600⟩, ⟨.privateRow 13 11, 234655005720913941477814500⟩, ⟨.privateRow 13 12, 228846459029465250264891600⟩, ⟨.privateRow 14 6, 787568435724237841448775⟩, ⟨.privateRow 14 7, 10920948975376098068089680⟩, ⟨.privateRow 14 8, 50404379886351221852721600⟩, ⟨.privateRow 14 9, 114379169742104695742714400⟩, ⟨.privateRow 15 5, 3675319366713109926760950⟩, ⟨.privateRow 15 6, 29402554933704879414087600⟩, ⟨.privateRow 15 7, 14701277466852439707043800⟩, ⟨.privateRow 16 4, 11025958100139329780282850⟩, ⟨.hall 6 28, 31201180190683929623763165600⟩, ⟨.hall 5 29, 120035930516850170208012627000⟩, ⟨.hall 4 30, 307987020582988659462662112000⟩, ⟨.hall 3 31, 668790514522051187152836549600⟩, ⟨.hall 2 32, 1320677232916761496358883100800⟩, ⟨.assumptionRow 19, 1106354893920407640212704⟩]
  caps := #[0, 194551158499282892548694486880, 15162669576114326226166476270, 441256328852189732708700720, 2248982390104818501751688070, 119161732858488339587600340, 114545207472407632707204880, 10247204397531636955254450, 65255681744033414913339060, 0, 869065839374183447365600, 13026785636955595418408432, 29276626831424711995915120, 17149533148258376730217584, 1106354893920407640212704, 180242827101124347881516580, 90751814097134095566095358, 678737281961614658107284960, 130930792171275729724596736, 17628830459945422439787296, 1249012356924388672000000] }

theorem case_55_35_19_checked :
    (Witness.linear .conditional case_55_35_19).check 55 35 19 = true := by
  change case_55_35_19.check 55 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_20 : Certificate := {
  objectiveScale := 608893524000639477600000
  eta := 227598109367603408891440964940960
  rows := #[⟨.count 2, 21938728124805869256773228375040⟩, ⟨.count 3, 2765733688305989259158501641440⟩, ⟨.count 4, 386137873433359440369329633280⟩, ⟨.count 5, 49484499953425312053909430800⟩, ⟨.count 6, 6192178069038247604606848560⟩, ⟨.count 7, 767406683769697352707686360⟩, ⟨.count 8, 130275935706261619557803520⟩, ⟨.count 9, 48853475889848107334176320⟩, ⟨.count 10, 22206125404476412424625600⟩, ⟨.count 11, 12213368972462026833544080⟩, ⟨.path 2, 3062313517778915179005568742400⟩, ⟨.path 7, 101407075117222573902253050⟩, ⟨.path 8, 19927227369540512379758400⟩, ⟨.privateRow 2 33, 1948789579983985925613960492960⟩, ⟨.privateRow 3 30, 299106310829592997303630337280⟩, ⟨.privateRow 3 31, 580618132786856994765870654720⟩, ⟨.privateRow 4 27, 34612687667957384046263922720⟩, ⟨.privateRow 4 28, 111009346152202772227887733800⟩, ⟨.privateRow 4 29, 206229520305006024210410426400⟩, ⟨.privateRow 4 30, 386402496427762784284056421680⟩, ⟨.privateRow 5 24, 2767200455760682079714415840⟩, ⟨.privateRow 5 25, 16653607114450443700139216640⟩, ⟨.privateRow 5 26, 37063096596132348696633983304⟩, ⟨.privateRow 5 27, 70072168918005468619653568320⟩, ⟨.privateRow 5 28, 139835611009207036005459216840⟩, ⟨.privateRow 5 29, 198070311310902920173001117400⟩, ⟨.privateRow 6 22, 1884336239313811459450339065⟩, ⟨.privateRow 6 23, 5993080768487160278288598240⟩, ⟨.privateRow 6 24, 12922422893363294502491500200⟩, ⟨.privateRow 6 25, 24085984950592363118432280168⟩, ⟨.privateRow 6 26, 48800890551216673607531894100⟩, ⟨.privateRow 6 27, 75940918882772962550705453280⟩, ⟨.privateRow 6 28, 94673286631036341225420663240⟩, ⟨.privateRow 7 19, 41205580557092123864599908⟩, ⟨.privateRow 7 20, 764886464775379791615050280⟩, ⟨.privateRow 7 21, 2149589288465734764450286485⟩, ⟨.privateRow 7 22, 4624961885857627113714726240⟩, ⟨.privateRow 7 23, 8667033121458092597575479120⟩, ⟨.privateRow 7 24, 17647329463909858038965622984⟩, ⟨.privateRow 7 25, 28346793193335347779697468820⟩, ⟨.privateRow 7 26, 38892019520308602781559986560⟩, ⟨.privateRow 7 27, 39958072154904931123745048400⟩, ⟨.privateRow 8 17, 17764900323581129939700480⟩, ⟨.privateRow 8 18, 276429251076723873999214344⟩, ⟨.privateRow 8 19, 797261585702382307189683000⟩, ⟨.privateRow 8 20, 1731499497033418595880572175⟩, ⟨.privateRow 8 21, 3279871158104742872751039960⟩, ⟨.privateRow 8 22, 6753653781522265782648944460⟩, ⟨.privateRow 8 23, 11171568599111015944642769976⟩, ⟨.privateRow 8 24, 15849390693638742738780432150⟩, ⟨.privateRow 8 25, 18429295258946728379216153160⟩, ⟨.privateRow 8 26, 13190438490258988980227606400⟩, ⟨.privateRow 9 15, 2940255493370487941408760⟩, ⟨.privateRow 9 16, 96596645509472394047121360⟩, ⟨.privateRow 9 17, 306691265308490896042329120⟩, ⟨.privateRow 9 18, 689226044112641045137407280⟩, ⟨.privateRow 9 19, 1325150533512129911439532680⟩, ⟨.privateRow 9 20, 2765455688764616075881052400⟩, ⟨.privateRow 9 21, 4733585170826995548134149080⟩, ⟨.privateRow 9 22, 6984147194852563033501995792⟩, ⟨.privateRow 9 23, 8646047451755409829246413300⟩, ⟨.privateRow 9 24, 2712724952883510182250512880⟩, ⟨.privateRow 10 14, 30903524521229673957603960⟩, ⟨.privateRow 10 15, 122234626658276979301007280⟩, ⟨.privateRow 10 16, 293898069728245318439919816⟩, ⟨.privateRow 10 17, 581677118233923803233942800⟩, ⟨.privateRow 10 18, 1232856324799774822299682530⟩, ⟨.privateRow 10 19, 2188413658611150444446852880⟩, ⟨.privateRow 10 20, 3384028460597167950076069560⟩, ⟨.privateRow 10 21, 3212116039757513057222093040⟩, ⟨.privateRow 11 12, 8711633812525361797353120⟩, ⟨.privateRow 11 13, 49038526934885410771048200⟩, ⟨.privateRow 11 14, 134347058697082295168984880⟩, ⟨.privateRow 11 15, 280574394485559470985144456⟩, ⟨.privateRow 11 16, 610545081259743139385956080⟩, ⟨.privateRow 11 17, 1124879040020508266884940550⟩, ⟨.privateRow 11 18, 1830419194054698567001281600⟩, ⟨.privateRow 11 19, 171357267704542982543360880⟩, ⟨.privateRow 12 10, 2229424494973227120408840⟩, ⟨.privateRow 12 11, 19102961726158554790927920⟩, ⟨.privateRow 12 12, 64346360604915678410060940⟩, ⟨.privateRow 12 13, 149151142300066570118735280⟩, ⟨.privateRow 12 14, 340752994331690548655879832⟩, ⟨.privateRow 12 15, 656807842519068998603926080⟩, ⟨.privateRow 12 16, 340617290231996526135507120⟩, ⟨.privateRow 13 8, 542816398776090081490848⟩, ⟨.privateRow 13 9, 7269862483608349305681000⟩, ⟨.privateRow 13 10, 31316330698620581624472000⟩, ⟨.privateRow 13 11, 67682419722393732035890110⟩, ⟨.privateRow 13 12, 250559114980508853524525520⟩, ⟨.privateRow 13 13, 202945481092410679217390796⟩, ⟨.privateRow 14 7, 2772240893749317201899688⟩, ⟨.privateRow 14 8, 15391337429582248101456060⟩, ⟨.privateRow 14 9, 50889037385258445139767000⟩, ⟨.privateRow 14 10, 119710402230084151900213800⟩, ⟨.privateRow 15 5, 1102595810013932978028285⟩, ⟨.privateRow 15 6, 7644664282763268647662776⟩, ⟨.privateRow 15 7, 31502737428969513657951000⟩, ⟨.privateRow 15 8, 20355614954103378055906800⟩, ⟨.privateRow 16 4, 3307787430041798934084855⟩, ⟨.privateRow 16 5, 14113226368178342118762048⟩, ⟨.hall 7 27, 1379819899388864698218253800⟩, ⟨.hall 6 28, 25936703423864301490324943040⟩, ⟨.hall 5 29, 79607417483005961013642177000⟩, ⟨.hall 4 30, 186089718644932172291741520000⟩, ⟨.hall 3 31, 381368043959239166306379272370⟩, ⟨.hall 2 32, 722391906758103067867980318720⟩, ⟨.assumptionRow 20, 360584871394643312051712⟩]
  caps := #[0, 90852765433848161579215472400, 2616034276747861947453001680, 0, 131142038752699107284015172, 25605740608821688037353092, 67330404562367427411593355, 27963736235417096281146969, 17992342454584993229703969, 2850133162883153292329184, 476039119546155182100384, 0, 21178041448402866187616148, 360584871394643312051712, 41635895283976629922307604, 0, 0, 1127289298122786471844114944, 288328477360385321680246272, 57916153425146855989624320, 8163924464614309374348288] }

theorem case_55_35_20_checked :
    (Witness.linear .conditional case_55_35_20).check 55 35 20 = true := by
  change case_55_35_20.check 55 35 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_21 : Certificate := {
  objectiveScale := 1292310741921605003998400000
  eta := 954318072239607549783241691778539520
  rows := #[⟨.count 2, 74096043607986770397757365928131840⟩, ⟨.count 3, 9029722382711803891910777123698560⟩, ⟨.count 4, 1411474498325991558587451792268800⟩, ⟨.count 5, 206613865708903369595860541960400⟩, ⟨.count 6, 29449937841012229887820892658240⟩, ⟨.count 7, 3581749196879865797167405863840⟩, ⟨.count 8, 367358891987678543299221114240⟩, ⟨.count 9, 30613240998973211941601759520⟩, ⟨.path 2, 19035730706447892819996268638984000⟩, ⟨.path 8, 72488251077500728959359270400⟩, ⟨.path 9, 21509699800439222952029049600⟩, ⟨.privateRow 2 33, 6643746788079164401990297054549440⟩, ⟨.privateRow 3 30, 988267984166260255014321927402240⟩, ⟨.privateRow 4 27, 108036168368109729822708716130048⟩, ⟨.privateRow 4 28, 373231532052648237790018385107920⟩, ⟨.privateRow 4 29, 698396874265686424697061829796160⟩, ⟨.privateRow 5 24, 7997344767636525748172726320320⟩, ⟨.privateRow 5 25, 55738208181074948609006359152720⟩, ⟨.privateRow 5 27, 485973720893325124618449831720180⟩, ⟨.privateRow 5 28, 351829475123143854508178577230160⟩, ⟨.privateRow 5 29, 510996218754860853729216569907840⟩, ⟨.privateRow 6 22, 6538903240600125367359631384140⟩, ⟨.privateRow 6 23, 20385017034094051018446593867040⟩, ⟨.privateRow 6 24, 35121040736072017400002618609320⟩, ⟨.privateRow 6 25, 55813380695083538384996292362208⟩, ⟨.privateRow 6 26, 231448432285417624266652447124340⟩, ⟨.privateRow 6 27, 236181721218948681485234271025680⟩, ⟨.privateRow 6 28, 301220685545007972966720601783680⟩, ⟨.privateRow 7 19, 354384708897637515381113701872⟩, ⟨.privateRow 7 20, 2798438966874392501137849731360⟩, ⟨.privateRow 7 21, 7388542159436707289262657995580⟩, ⟨.privateRow 7 22, 14888760172517628081271465266960⟩, ⟨.privateRow 7 23, 26394080391293296767221717020440⟩, ⟨.privateRow 7 24, 50064894329720790809295517519008⟩, ⟨.privateRow 7 25, 115461665082752340489243736249620⟩, ⟨.privateRow 7 26, 135673753749536715447377353510800⟩, ⟨.privateRow 7 27, 138115281200319904390243671617280⟩, ⟨.privateRow 8 16, 11479965374614954478100659820⟩, ⟨.privateRow 8 17, 232846166386129581737637625440⟩, ⟨.privateRow 8 18, 1077075862480540840145355239112⟩, ⟨.privateRow 8 19, 2774466693499535171151833538720⟩, ⟨.privateRow 8 20, 5728502721932862284572229250180⟩, ⟨.privateRow 8 21, 10541159317313109311891539194720⟩, ⟨.privateRow 8 22, 21170756886401030124947705694720⟩, ⟨.privateRow 8 23, 34088864293723303937371612617504⟩, ⟨.privateRow 8 24, 60054249978027407975939684998380⟩, ⟨.privateRow 8 25, 69748868144938355274279431093040⟩, ⟨.privateRow 8 26, 51677701909683362858418903549720⟩, ⟨.privateRow 9 14, 11251020196203830029819450080⟩, ⟨.privateRow 9 15, 108847079107460309125695144960⟩, ⟨.privateRow 9 16, 425493127420072117491353748480⟩, ⟨.privateRow 9 17, 1095954027763240987509342990816⟩, ⟨.privateRow 9 18, 2299772487391999934131440823200⟩, ⟨.privateRow 9 19, 4292231498397702424312080032700⟩, ⟨.privateRow 9 20, 8862290306972594276046553811520⟩, ⟨.privateRow 9 21, 15107067521122928737403771994240⟩, ⟨.privateRow 9 22, 22298684743652087578262721634368⟩, ⟨.privateRow 9 23, 32029953762981250027565885391120⟩, ⟨.privateRow 9 24, 21803430533713143171740808724800⟩, ⟨.privateRow 10 11, 185534793933170981464253088⟩, ⟨.privateRow 10 12, 6361192934851576507345820160⟩, ⟨.privateRow 10 13, 49024001320034024717669950560⟩, ⟨.privateRow 10 14, 179968750115175852020325495360⟩, ⟨.privateRow 10 15, 467547680711590873289917781760⟩, ⟨.privateRow 10 16, 999104865330125735185002878880⟩, ⟨.privateRow 10 17, 1891217999492122871058953143680⟩, ⟨.privateRow 10 18, 3952586866253791296369081723480⟩, ⟨.privateRow 10 19, 7041840578880695193631822917120⟩, ⟨.privateRow 10 20, 11019375248675857516615651529040⟩, ⟨.privateRow 10 21, 14855770950229000485842744756160⟩, ⟨.privateRow 10 22, 1374117067567547581469624433000⟩, ⟨.privateRow 10 25, 5585524971358112396981339214240⟩, ⟨.privateRow 11 10, 3339626290797077666356555584⟩, ⟨.privateRow 11 11, 23258111668051076604983154960⟩, ⟨.privateRow 11 12, 84132893095080225825520919520⟩, ⟨.privateRow 11 13, 221482160257722859122952123800⟩, ⟨.privateRow 11 14, 482474798223486902253178143840⟩, ⟨.privateRow 11 15, 928694411032487347719318831984⟩, ⟨.privateRow 11 16, 1960793547217061989108048051680⟩, ⟨.privateRow 11 17, 3605752760844969792894343607100⟩, ⟨.privateRow 11 18, 5952883863345790940280560328480⟩, ⟨.privateRow 11 19, 3643439515862645148504270015600⟩, ⟨.privateRow 12 8, 1913327562435825746350109970⟩, ⟨.privateRow 12 9, 12472061147729827087319235360⟩, ⟨.privateRow 12 10, 44705050347706912676624791680⟩, ⟨.privateRow 12 11, 119836447671194282643193212480⟩, ⟨.privateRow 12 12, 266165123129961537158926409160⟩, ⟨.privateRow 12 13, 521971220265321027852765354240⟩, ⟨.privateRow 12 14, 1113981825240414101208286249200⟩, ⟨.privateRow 12 15, 2104376862744232643096772802560⟩, ⟨.privateRow 12 16, 2543450106331357692148079520120⟩, ⟨.privateRow 13 6, 1200519254861694585945167040⟩, ⟨.privateRow 13 7, 7653310249743302985400439880⟩, ⟨.privateRow 13 8, 27892064021286704213459380896⟩, ⟨.privateRow 13 9, 75804215806981286712537690240⟩, ⟨.privateRow 13 10, 172297599981400513363630415760⟩, ⟨.privateRow 13 11, 344824145141212151175542041260⟩, ⟨.privateRow 13 12, 744458360656848563125315515600⟩, ⟨.privateRow 13 13, 1440352989001689621852362785416⟩, ⟨.privateRow 14 4, 1052836330652517871007467920⟩, ⟨.privateRow 14 5, 5573839397572153434745418400⟩, ⟨.privateRow 14 6, 20727715259721445585459524675⟩, ⟨.privateRow 14 7, 57484863653627475757007748432⟩, ⟨.privateRow 14 8, 134011024373056203295379130960⟩, ⟨.privateRow 14 9, 274790282300307164332949127120⟩, ⟨.privateRow 14 10, 600116708471935186474256714400⟩, ⟨.privateRow 14 12, 524944194463345410484323504912⟩, ⟨.privateRow 15 2, 1163661207563309225850359280⟩, ⟨.privateRow 15 3, 4913236209711750064701516960⟩, ⟨.privateRow 15 4, 18207875365402367886835033440⟩, ⟨.privateRow 15 5, 53892059675275758522194764155⟩, ⟨.privateRow 15 6, 128235465073476676688709592656⟩, ⟨.privateRow 15 7, 268473264316392057106904319600⟩, ⟨.privateRow 15 8, 598658935091031700191323297280⟩, ⟨.privateRow 15 10, 705496053930882657017822367120⟩, ⟨.privateRow 16 1, 6981967245379855355102155680⟩, ⟨.privateRow 16 2, 18424635786419062742630688600⟩, ⟨.privateRow 16 3, 62427001252808118469148686080⟩, ⟨.privateRow 16 4, 153385092921938697332400482595⟩, ⟨.privateRow 16 5, 331643444155543129367352394800⟩, ⟨.privateRow 16 6, 748566631093940206286309691120⟩, ⟨.privateRow 16 7, 1540866463614985001060621895840⟩, ⟨.privateRow 17 0, 41891803472279132130612934080⟩, ⟨.privateRow 17 1, 88438251774811501164627305280⟩, ⟨.privateRow 17 2, 234101254698030444259307572800⟩, ⟨.privateRow 17 3, 530629510648869006987763831680⟩, ⟨.privateRow 17 4, 1238135524847361016304782273920⟩, ⟨.privateRow 17 5, 2634196499292599713260684735840⟩, ⟨.privateRow 17 15, 27659063242572296989237189726320⟩, ⟨.privateRow 18 0, 1169350217911396515398961036480⟩, ⟨.privateRow 18 1, 795944265973303510481645747520⟩, ⟨.privateRow 18 2, 2818969275322116599622495355800⟩, ⟨.privateRow 18 3, 6214261158043421481834478651008⟩, ⟨.privateRow 18 6, 17790828315366246984284192912160⟩, ⟨.privateRow 18 14, 33075906163779501435570612174720⟩, ⟨.privateRow 18 15, 110253020545931671451902040582400⟩, ⟨.hall 15 5, 847076908446820686464599770⟩, ⟨.hall 16 18, 55855737963038842840817245440⟩, ⟨.hall 7 27, 11408534478950683650236922381120⟩, ⟨.hall 6 28, 100604610583625655781740430604640⟩, ⟨.hall 5 29, 302226670658946453792468237381240⟩, ⟨.hall 4 30, 798854169741377953423191549177600⟩, ⟨.hall 2 31, 145458814606621216540520760359280⟩, ⟨.hall 3 31, 2686477719381977119440238074077400⟩]
  caps := #[0, 3443389645225800112745471849280, 3891141753770555833007132113440, 1532842067725199395362547789440, 1895953806955705643871697596624, 250792679971584745675966565280, 45903152593914961118865875784, 24826479253005700009994814560, 0, 36265093379734075000586701952, 0, 14399125095402442712106976480, 18642305860844787768360556150, 94235781071278924681750240864, 2196940206996275681297316960, 376757134060513721184472676874, 0, 1129985115858678162995465698144, 0, 568616726445506201759296000000, 116307966772944450359856000000] }

theorem case_55_35_21_checked :
    (Witness.linear .conditional case_55_35_21).check 55 35 21 = true := by
  change case_55_35_21.check 55 35 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_35_22 : Certificate := {
  objectiveScale := 58940842812852000000
  eta := 51308560046638211209114622400
  rows := #[⟨.count 2, 3223644818916143342754633600⟩, ⟨.count 3, 322876476303989342152017600⟩, ⟨.count 4, 47359483144688228581267200⟩, ⟨.count 5, 6541105084570413128772000⟩, ⟨.count 6, 799991269335949807116000⟩, ⟨.count 7, 79999126933594980711600⟩, ⟨.count 8, 5791791995192396793600⟩, ⟨.path 2, 1199114186255558219975328000⟩, ⟨.path 8, 4970650433490325584000⟩, ⟨.privateRow 2 33, 324476458842661241766249600⟩, ⟨.privateRow 5 24, 150586591875002316633600⟩, ⟨.privateRow 5 25, 1348220580380880116110200⟩, ⟨.privateRow 5 29, 95408370530304202143372600⟩, ⟨.privateRow 6 22, 143135692797853764508500⟩, ⟨.privateRow 6 23, 559545714154584500943600⟩, ⟨.privateRow 6 24, 1135412445335303925589800⟩, ⟨.privateRow 7 19, 5512544881138477662480⟩, ⟨.privateRow 7 20, 62893804741444419943200⟩, ⟨.privateRow 7 21, 197308771050505267553400⟩, ⟨.privateRow 7 22, 457041830824704097486800⟩, ⟨.privateRow 7 23, 926600531849902647738000⟩, ⟨.privateRow 7 24, 1257263589842095234679280⟩, ⟨.privateRow 7 25, 2277790267502127675597300⟩, ⟨.privateRow 7 26, 3310215974966568781713600⟩, ⟨.privateRow 8 16, 90496749924881199900⟩, ⟨.privateRow 8 17, 3685685815122434323200⟩, ⟨.privateRow 8 18, 23058571880859729734520⟩, ⟨.privateRow 8 19, 69823270164263894678400⟩, ⟨.privateRow 8 20, 166197281237044323616350⟩, ⟨.privateRow 8 21, 352058213422052119382400⟩, ⟨.privateRow 8 22, 826959300813564404686200⟩, ⟨.privateRow 8 24, 5000126426849536056874800⟩, ⟨.privateRow 8 25, 2626095020486819246164800⟩, ⟨.privateRow 8 27, 19080334754161952186916000⟩, ⟨.privateRow 9 14, 92817179410134564000⟩, ⟨.privateRow 9 15, 1628941498647861598200⟩, ⟨.privateRow 9 16, 8402486114237454439200⟩, ⟨.privateRow 9 17, 25508017245493180878480⟩, ⟨.privateRow 9 18, 61645045356237593650400⟩, ⟨.privateRow 9 19, 132155420473634845587300⟩, ⟨.privateRow 9 21, 1286180030710156004623200⟩, ⟨.privateRow 9 22, 175877416920675782632320⟩, ⟨.privateRow 9 23, 2319733356407788090770000⟩, ⟨.privateRow 9 24, 2621831618045913731858400⟩, ⟨.privateRow 10 12, 56413558394731137600⟩, ⟨.privateRow 10 13, 668283691752968860800⟩, ⟨.privateRow 10 14, 3224975088232130032800⟩, ⟨.privateRow 10 15, 9926222024818374256800⟩, ⟨.privateRow 10 16, 24404505361560690125760⟩, ⟨.privateRow 10 17, 52893979168215411626400⟩, ⟨.privateRow 10 18, 129278720756325743202600⟩, ⟨.privateRow 10 19, 71109290356558598944800⟩, ⟨.privateRow 10 20, 837177206577810081984000⟩, ⟨.privateRow 10 21, 542980499549287199400000⟩, ⟨.privateRow 10 23, 4412753157973461679778400⟩, ⟨.privateRow 11 10, 26326327250874530880⟩, ⟨.privateRow 11 11, 296171181572338472400⟩, ⟨.privateRow 11 12, 1366943914949254488000⟩, ⟨.privateRow 11 13, 4245120269203518104400⟩, ⟨.privateRow 11 14, 10608313230863759829600⟩, ⟨.privateRow 11 15, 23279054871585803930640⟩, ⟨.privateRow 11 16, 57259761770652104664000⟩, ⟨.privateRow 11 17, 124860833964538360989300⟩, ⟨.privateRow 11 18, 104393289809449970128800⟩, ⟨.privateRow 11 19, 586879650240120479642400⟩, ⟨.privateRow 11 20, 621643565374900297669440⟩, ⟨.privateRow 11 22, 1959995063827608824016000⟩, ⟨.privateRow 11 23, 1557169348980164908388400⟩, ⟨.privateRow 12 8, 15082791654146866650⟩, ⟨.privateRow 12 9, 144794799879809919840⟩, ⟨.privateRow 12 10, 655024094694378208800⟩, ⟨.privateRow 12 11, 2060541382904987320800⟩, ⟨.privateRow 12 13, 22092176284692210496800⟩, ⟨.privateRow 12 14, 23432625113882572027440⟩, ⟨.privateRow 12 15, 63816967354434742448000⟩, ⟨.privateRow 12 16, 130466147808370396522500⟩, ⟨.privateRow 12 17, 131418518367103670102400⟩, ⟨.privateRow 12 19, 1497516085290287460958560⟩, ⟨.privateRow 12 21, 487073618484582813684000⟩, ⟨.privateRow 12 23, 3377821356529499080000800⟩, ⟨.privateRow 13 7, 90496749924881199900⟩, ⟨.privateRow 13 8, 386119466346159786240⟩, ⟨.privateRow 13 9, 1189385856155581484400⟩, ⟨.privateRow 13 11, 5007486829176759727800⟩, ⟨.privateRow 13 12, 28827328339707611313600⟩, ⟨.privateRow 13 13, 31311875474008895165400⟩, ⟨.privateRow 13 14, 78913165934496406312800⟩, ⟨.privateRow 13 15, 153799226497335599230050⟩, ⟨.privateRow 13 16, 174426021426642449864400⟩, ⟨.privateRow 13 17, 76258594603366557782400⟩, ⟨.privateRow 13 18, 935953586423091321845760⟩, ⟨.privateRow 14 5, 39544798286502709200⟩, ⟨.privateRow 14 6, 252098089076454771150⟩, ⟨.privateRow 14 7, 806713885044655267680⟩, ⟨.privateRow 14 8, 1680653927176365141000⟩, ⟨.privateRow 14 9, 51712428528503542800⟩, ⟨.privateRow 14 10, 8851444016462189742600⟩, ⟨.privateRow 14 11, 45897130883980008032400⟩, ⟨.privateRow 14 13, 213405700886350009237200⟩, ⟨.privateRow 14 14, 162939398239748600419950⟩, ⟨.privateRow 14 15, 265927469962934575738800⟩, ⟨.privateRow 14 16, 189913893770929260933000⟩, ⟨.privateRow 14 17, 721874474800792355362320⟩, ⟨.privateRow 14 18, 611589964099479274809900⟩, ⟨.privateRow 15 3, 87145018446181896200⟩, ⟨.privateRow 15 4, 184542392003679309600⟩, ⟨.privateRow 15 5, 686267020263682432575⟩, ⟨.privateRow 15 6, 1777758376302110682480⟩, ⟨.privateRow 15 7, 3361307854352730282000⟩, ⟨.privateRow 15 8, 241324666466349866400⟩, ⟨.privateRow 15 9, 17908301290690379669100⟩, ⟨.privateRow 15 10, 86130967322444506862400⟩, ⟨.privateRow 15 11, 16156686419922123555480⟩, ⟨.privateRow 15 12, 321390828029518833185600⟩, ⟨.privateRow 15 13, 360780376367193050268000⟩, ⟨.privateRow 15 15, 1343776184440124839404000⟩, ⟨.privateRow 15 20, 9215585700683735523150000⟩, ⟨.privateRow 16 2, 261435055338545688600⟩, ⟨.privateRow 16 3, 830440764016556893200⟩, ⟨.privateRow 16 4, 2058801060791047297725⟩, ⟨.privateRow 16 5, 4705830996093822394800⟩, ⟨.privateRow 16 6, 9411661992187644789600⟩, ⟨.privateRow 16 8, 41960326381836583020300⟩, ⟨.privateRow 16 9, 194222479293326851567200⟩, ⟨.privateRow 16 10, 79999126933594980711600⟩, ⟨.privateRow 16 13, 79999126933594980711600⟩, ⟨.privateRow 16 15, 6977806201007919847009440⟩, ⟨.privateRow 17 0, 990701262335541556800⟩, ⟨.privateRow 17 1, 1045740221354182754400⟩, ⟨.privateRow 17 2, 2214508704044151715200⟩, ⟨.privateRow 17 3, 5882288745117277993500⟩, ⟨.privateRow 17 4, 15058659187500231663360⟩, ⟨.privateRow 17 5, 30924032260045118594400⟩, ⟨.privateRow 17 7, 123920216230470656396400⟩, ⟨.privateRow 17 8, 564699719531258687376000⟩, ⟨.privateRow 17 9, 395289803671881081163200⟩, ⟨.privateRow 17 10, 100391061250001544422400⟩, ⟨.privateRow 17 12, 134452314174109211280000⟩, ⟨.privateRow 17 13, 144312150546877220107200⟩, ⟨.privateRow 17 14, 8688846351187633669758720⟩, ⟨.privateRow 17 15, 17232753107695577609757600⟩, ⟨.privateRow 18 0, 11851722508680737883200⟩, ⟨.privateRow 18 1, 6274441328125096526400⟩, ⟨.privateRow 18 2, 33332969555664575296500⟩, ⟨.privateRow 18 3, 85332402062501312759040⟩, ⟨.privateRow 18 4, 159998253867189961423200⟩, ⟨.privateRow 18 5, 32820154639423581830400⟩, ⟨.privateRow 18 7, 19393727741477571081600⟩, ⟨.privateRow 18 8, 7007923519382920310336160⟩, ⟨.privateRow 18 12, 977767106966160875364000⟩, ⟨.privateRow 18 13, 15423831672797112281196480⟩, ⟨.privateRow 18 17, 438075219088366114376721600⟩, ⟨.privateRow 19 0, 282349859765629343688000⟩, ⟨.privateRow 19 1, 179998035600588706601100⟩, ⟨.privateRow 19 2, 639993015468759845692800⟩, ⟨.privateRow 19 3, 1165701563889526861797600⟩, ⟨.privateRow 19 4, 443072087632218354710400⟩, ⟨.privateRow 19 7, 34943618644594287574826880⟩, ⟨.privateRow 19 16, 1024308821257750133031326400⟩, ⟨.hall 16 3, 602190963380427220800⟩, ⟨.hall 18 4, 11293994390625173747520⟩, ⟨.hall 15 6, 36301431058618495770⟩, ⟨.hall 16 7, 94512601572734545200⟩, ⟨.hall 8 19, 4553055630827575872⟩, ⟨.hall 15 19, 118822232651369015468700⟩, ⟨.hall 6 20, 5480761964538180320⟩, ⟨.hall 9 22, 166017649728414166452⟩, ⟨.hall 4 28, 107671925758900432849920⟩, ⟨.hall 3 31, 230337486223553348213874300⟩, ⟨.hall 2 32, 294338605932405096305443200⟩]
  caps := #[0, 0, 0, 0, 43346135719496642432400, 0, 18087228724673487479100, 0, 382049204564591503170, 1734193649183179861600, 410112762015402953640, 4113488632949145450, 1175047030810916648000, 0, 11799417654312249218400, 33924407073808438877690, 7216578803091248791200, 145355329961966604480, 603791980815614869538260, 0, 20629294984498200000000] }

theorem case_55_35_22_checked :
    (Witness.linear .conditional case_55_35_22).check 55 35 22 = true := by
  change case_55_35_22.check 55 35 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_36_1_checked :
    (Witness.rising).check 55 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_36_2_checked :
    (Witness.rising).check 55 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_36_3_checked :
    (Witness.rising).check 55 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_36_4_checked :
    (Witness.rising).check 55 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_36_5_checked :
    (Witness.rising).check 55 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_36_6_checked :
    (Witness.rising).check 55 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_36_7_checked :
    (Witness.rising).check 55 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_36_8_checked :
    (Witness.rising).check 55 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_36_9_checked :
    (Witness.rising).check 55 36 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_36_10_checked :
    (Witness.rising).check 55 36 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_36_11_checked :
    (Witness.linear .positive case_55_36_11).check 55 36 11 = true := by
  change case_55_36_11.check 55 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_36_12_checked :
    (Witness.linear .positive case_55_36_12).check 55 36 12 = true := by
  change case_55_36_12.check 55 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_36_13_checked :
    (Witness.linear .positive case_55_36_13).check 55 36 13 = true := by
  change case_55_36_13.check 55 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_55_36_14_checked :
    (Witness.linear .positive case_55_36_14).check 55 36 14 = true := by
  change case_55_36_14.check 55 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_55_36_15_checked :
    (Witness.linear .positive case_55_36_15).check 55 36 15 = true := by
  change case_55_36_15.check 55 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_55_36_16_checked :
    (Witness.linear .positive case_55_36_16).check 55 36 16 = true := by
  change case_55_36_16.check 55 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_17 : Certificate := {
  objectiveScale := 210051249340975328000000
  eta := 187877663065294213785888085171200
  rows := #[⟨.count 2, 25569779627890425659591693433600⟩, ⟨.count 3, 3388934360090571898868175513600⟩, ⟨.count 4, 442412079431619027753268646400⟩, ⟨.count 5, 56626818445768230676480464000⟩, ⟨.count 6, 7332226339786403121027561600⟩, ⟨.count 7, 1223361707830017422143276800⟩, ⟨.count 8, 296572535231519375065036800⟩, ⟨.count 9, 90993846036943444622227200⟩, ⟨.count 10, 30331282012314481540742400⟩, ⟨.path 6, 22708288556439972985699200⟩, ⟨.path 7, 189336342337211042343770400⟩, ⟨.privateRow 2 34, 2429170028731019291274891734400⟩, ⟨.privateRow 4 31, 1371829857820899564917534304600⟩, ⟨.privateRow 5 25, 6578349547104139138161347520⟩, ⟨.privateRow 5 26, 16329407361737136590820536640⟩, ⟨.privateRow 6 23, 4801016161160023052985036300⟩, ⟨.privateRow 6 24, 7110931782247578077133369600⟩, ⟨.privateRow 6 25, 12127146655495703910071994000⟩, ⟨.privateRow 6 26, 18377037706549161061786684320⟩, ⟨.privateRow 6 27, 32775568092812812542762286800⟩, ⟨.privateRow 6 29, 194540660239485370601395004400⟩, ⟨.privateRow 7 20, 256985397716240672768409120⟩, ⟨.privateRow 7 21, 1786496462227961949796531200⟩, ⟨.privateRow 7 22, 3292749531789235204405118400⟩, ⟨.privateRow 7 23, 5433632520491765693155852800⟩, ⟨.privateRow 7 24, 8932261647051095820876208800⟩, ⟨.privateRow 7 25, 15825057520572582510724816320⟩, ⟨.privateRow 7 27, 63654528343129413010610889600⟩, ⟨.privateRow 8 18, 170613461319268958666676000⟩, ⟨.privateRow 8 19, 698335641552968278473453840⟩, ⟨.privateRow 8 20, 1436265776090839056847083600⟩, ⟨.privateRow 8 22, 8588687660923509759137918400⟩, ⟨.privateRow 8 23, 4689553213348400118215894400⟩, ⟨.privateRow 8 25, 30519167453668540690286443200⟩, ⟨.privateRow 9 16, 89449197415945947877096800⟩, ⟨.privateRow 9 17, 302546878658187379004880000⟩, ⟨.privateRow 9 18, 206084210561447838468488640⟩, ⟨.privateRow 9 19, 1794226392123516522252681600⟩, ⟨.privateRow 9 21, 6205635865043293806657129600⟩, ⟨.privateRow 9 22, 3742262340871208023429560000⟩, ⟨.privateRow 9 23, 2258332452939103786716831360⟩, ⟨.privateRow 9 24, 13851706720096006493627095200⟩, ⟨.privateRow 10 14, 44796970356649080429404160⟩, ⟨.privateRow 10 16, 529556610042272379990870720⟩, ⟨.privateRow 10 17, 232034307394205783786679360⟩, ⟨.privateRow 10 19, 2981944162835667466474237200⟩, ⟨.privateRow 10 20, 693719750024506927810408320⟩, ⟨.privateRow 10 21, 8534211715531551289513553280⟩, ⟨.privateRow 10 23, 7232115054811234192370766000⟩, ⟨.privateRow 10 25, 13668033956799213244297044000⟩, ⟨.privateRow 11 12, 22989185969651055453499200⟩, ⟨.privateRow 11 13, 31757111508619863151632000⟩, ⟨.privateRow 11 14, 131014287580969496655151200⟩, ⟨.privateRow 11 15, 461096761904376714331488000⟩, ⟨.privateRow 11 16, 244503834443712848420095680⟩, ⟨.privateRow 11 17, 59539183209358056357753600⟩, ⟨.privateRow 11 18, 2739293906737151614148298000⟩, ⟨.privateRow 11 19, 997321439500149976375363200⟩, ⟨.privateRow 11 20, 6011491587718439605366584000⟩, ⟨.privateRow 11 21, 3028410001807310345834568960⟩, ⟨.privateRow 11 23, 8530392220759630206652867200⟩, ⟨.privateRow 12 10, 12666118692179473310069280⟩, ⟨.privateRow 12 11, 31444632641734755168726000⟩, ⟨.privateRow 12 12, 64875242081894863295476800⟩, ⟨.privateRow 12 13, 195977293789057399538419500⟩, ⟨.privateRow 12 15, 1162657017024815800059652080⟩, ⟨.privateRow 12 17, 2560255089303350855053638000⟩, ⟨.privateRow 12 18, 1602352280196188944966342800⟩, ⟨.privateRow 12 19, 4944806397968236455348693000⟩, ⟨.privateRow 13 8, 7695660093898242712346100⟩, ⟨.privateRow 13 9, 27009284458584800229137280⟩, ⟨.privateRow 13 10, 55891061327113504675840800⟩, ⟨.privateRow 13 11, 113658979848343276982342400⟩, ⟨.privateRow 13 12, 283001693775612796518534000⟩, ⟨.privateRow 13 13, 3971953596850705916049600⟩, ⟨.privateRow 13 14, 1664645752440130849416387360⟩, ⟨.privateRow 13 15, 168146035600013217112766400⟩, ⟨.privateRow 13 16, 2920875376284087863014974600⟩, ⟨.privateRow 13 17, 2677096724277375787417430400⟩, ⟨.privateRow 13 18, 5094030487961030337333612000⟩, ⟨.privateRow 14 6, 5062293799907762442024000⟩, ⟨.privateRow 14 7, 23666223514568789416462200⟩, ⟨.privateRow 14 8, 59667569588246159983322880⟩, ⟨.privateRow 14 9, 112491400082236063979547600⟩, ⟨.privateRow 14 10, 207865571568520276273262400⟩, ⟨.privateRow 14 11, 562969256331409081573419000⟩, ⟨.privateRow 14 13, 2760772546717697325382208640⟩, ⟨.privateRow 14 14, 780268217692449784397299200⟩, ⟨.privateRow 14 15, 3935047528013301440246305800⟩, ⟨.privateRow 14 17, 17264868633022092012482151600⟩, ⟨.privateRow 15 4, 4016086414593491537339040⟩, ⟨.privateRow 15 5, 24096518487560949224034240⟩, ⟨.privateRow 15 6, 72289555462682847672102720⟩, ⟨.privateRow 15 7, 154217718320390075033819136⟩, ⟨.privateRow 15 8, 270225243039076359155241120⟩, ⟨.privateRow 15 10, 674702517651706578272958720⟩, ⟨.privateRow 15 12, 10007284127884062212741419872⟩, ⟨.privateRow 15 14, 7015098944691181342846968120⟩, ⟨.privateRow 15 15, 4103292862453235925006973440⟩, ⟨.privateRow 15 16, 20996099775494773757208501120⟩, ⟨.privateRow 15 20, 70289544428215288886507878080⟩, ⟨.privateRow 16 2, 4755891806755450504743600⟩, ⟨.privateRow 16 3, 30120648109451186530042800⟩, ⟨.privateRow 16 4, 100992761308159860718378800⟩, ⟨.privateRow 16 5, 254142968423494386347236125⟩, ⟨.privateRow 16 6, 500002758616889696398710480⟩, ⟨.privateRow 16 7, 948800415447712375696348200⟩, ⟨.privateRow 16 9, 2025613585360592294145378300⟩, ⟨.privateRow 16 10, 336803610678408722108660400⟩, ⟨.privateRow 16 12, 251005400912093221083690000⟩, ⟨.privateRow 16 13, 756781283749961061567325350⟩, ⟨.privateRow 16 15, 165091272287901953371164586800⟩, ⟨.privateRow 16 19, 3343391940149081704834750800⟩, ⟨.privateRow 17 1, 50729512605391472050598400⟩, ⟨.privateRow 17 2, 187417366014362938409155200⟩, ⟨.privateRow 17 3, 538628060310185923831353600⟩, ⟨.privateRow 17 5, 4851432388828937777105560320⟩, ⟨.privateRow 17 6, 3201394599061668968335977600⟩, ⟨.privateRow 17 7, 259500968327579453181907200⟩, ⟨.privateRow 17 8, 7992011965041048159304689600⟩, ⟨.privateRow 17 9, 3023017773894009993560659200⟩, ⟨.privateRow 17 12, 1325308516815852207321883200⟩, ⟨.privateRow 17 14, 327632329702537039616118883200⟩, ⟨.privateRow 17 16, 665063910256682198583345024000⟩, ⟨.privateRow 18 12, 1180350746314253411347014364800⟩, ⟨.privateRow 18 15, 4410807467851812853086407546400⟩, ⟨.hall 16 6, 3568473068075331489833760⟩, ⟨.hall 13 8, 19745789213286986850000⟩, ⟨.hall 12 11, 3137916920253636034800⟩, ⟨.hall 17 12, 170968213155670297632064800⟩, ⟨.hall 15 16, 14445299764122764231494800⟩, ⟨.hall 10 18, 15136276096622347327584⟩, ⟨.hall 16 18, 974006642023516263371489280⟩, ⟨.hall 12 19, 366973973622076090069800⟩, ⟨.hall 13 20, 10117155660865914391473600⟩, ⟨.hall 6 22, 74389492415669406679704⟩, ⟨.hall 5 28, 120956124317612210083416960⟩, ⟨.hall 3 31, 9038932673572578794151934800⟩, ⟨.hall 2 33, 2109409228401085495071957369600⟩]
  caps := #[0, 0, 0, 624942098436388993148803200, 0, 0, 74746866741864815770915500, 0, 24957728800814629287902720, 0, 8169576973277145973771360, 10679392356650766327037760, 27273510682053460694529660, 1050256246704876640000000, 101179152245770565345081560, 45190862458969560910652504, 23106487994944887520981565, 1776596998880826065021203840, 0, 0] }

theorem case_55_36_17_checked :
    (Witness.linear .positive case_55_36_17).check 55 36 17 = true := by
  change case_55_36_17.check 55 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_18 : Certificate := {
  objectiveScale := 17567429955245326195079040000
  eta := 7702769137776149354604808449305577600
  rows := #[⟨.count 2, 1145169120639646617664251647392848000⟩, ⟨.count 3, 170343565789836455678278537499779200⟩, ⟨.count 4, 25076994675593118955519871154506400⟩, ⟨.count 5, 3763594633204840039001350972617600⟩, ⟨.count 6, 549344558262818266562308992897600⟩, ⟨.count 7, 84964092890075820278458592191200⟩, ⟨.count 8, 16783030694335964499448610803200⟩, ⟨.count 9, 3432892642023265465796306755200⟩, ⟨.count 10, 1716446321011632732898153377600⟩, ⟨.path 8, 2008242011718555995795039827200⟩, ⟨.path 9, 100874138048724729498929159040⟩, ⟨.privateRow 2 34, 89017194802757955705075431700172800⟩, ⟨.privateRow 3 30, 1336348819036501173268595635204800⟩, ⟨.privateRow 3 31, 16817995341615831092155795409040000⟩, ⟨.privateRow 3 32, 28117870049523116523263716324411200⟩, ⟨.privateRow 4 27, 224997505245941524070732938580400⟩, ⟨.privateRow 4 28, 3113147299857481814869595750176080⟩, ⟨.privateRow 4 29, 6560722709785067622335235459060300⟩, ⟨.privateRow 4 30, 10237386488690339345218348705408200⟩, ⟨.privateRow 4 31, 16491294418594577616548039248222500⟩, ⟨.privateRow 5 25, 522072133384522324250705000342400⟩, ⟨.privateRow 5 26, 1373621133036838961094454425030240⟩, ⟨.privateRow 5 27, 2350883024509110227260264158258240⟩, ⟨.privateRow 5 28, 3609505432642467964940788414680720⟩, ⟨.privateRow 5 29, 5969024725029705240599727170581440⟩, ⟨.privateRow 5 30, 6745834293646501330775247558528720⟩, ⟨.privateRow 6 22, 57033999646277625389743270145200⟩, ⟨.privateRow 6 23, 266758405840832185735376552180550⟩, ⟨.privateRow 6 24, 532647155276106465147041242353600⟩, ⟨.privateRow 6 25, 880185045774527376270933616870800⟩, ⟨.privateRow 6 26, 1304595924356770897577228129586960⟩, ⟨.privateRow 6 27, 2133580239139545058341733774720200⟩, ⟨.privateRow 6 28, 2550945741294895461217530589359600⟩, ⟨.privateRow 6 29, 2299162818757770422376472300948200⟩, ⟨.privateRow 7 19, 3310289333379577413446438656800⟩, ⟨.privateRow 7 20, 39919637294384829845117052839040⟩, ⟨.privateRow 7 21, 114783942070190614344443177457600⟩, ⟨.privateRow 7 22, 215276084564735758919824647278100⟩, ⟨.privateRow 7 23, 345957345728524900861720662232800⟩, ⟨.privateRow 7 24, 504390011760132647367357356817600⟩, ⟨.privateRow 7 25, 808552473397303546840400126534880⟩, ⟨.privateRow 7 26, 980908204688600210833844699265600⟩, ⟨.privateRow 7 27, 935354264232545450049627041371200⟩, ⟨.privateRow 7 28, 189708186241333313002695904257600⟩, ⟨.privateRow 8 17, 3124965350638076723204624146950⟩, ⟨.privateRow 8 18, 20692713981084683502161071274400⟩, ⟨.privateRow 8 19, 50768667850366292610832047679680⟩, ⟨.privateRow 8 20, 93239059412977580552492282240000⟩, ⟨.privateRow 8 21, 147671002496061562636749983727375⟩, ⟨.privateRow 8 22, 212447694347275122045475606841400⟩, ⟨.privateRow 8 23, 336928082350614453974607658025700⟩, ⟨.privateRow 8 24, 416219161219531919586325547919360⟩, ⟨.privateRow 8 25, 157275354045749917321004755144050⟩, ⟨.privateRow 9 15, 1951174023030317551072259822400⟩, ⟨.privateRow 9 16, 10378143033524038653541612551600⟩, ⟨.privateRow 9 17, 24429018851569601218722203121600⟩, ⟨.privateRow 9 18, 44455959714201287782062172479840⟩, ⟨.privateRow 9 19, 70268345684871285707287365433600⟩, ⟨.privateRow 9 20, 100626665569306968966154241761800⟩, ⟨.privateRow 9 21, 158321739228549171601129671067200⟩, ⟨.privateRow 9 22, 77907591348139107932099517194400⟩, ⟨.privateRow 10 13, 1103429777793192471148812885600⟩, ⟨.privateRow 10 14, 5492628227237224745274090808320⟩, ⟨.privateRow 10 15, 13116510636397226800563388727160⟩, ⟨.privateRow 10 16, 24045852551626600376327766862560⟩, ⟨.privateRow 10 17, 38225259568929060961641875719152⟩, ⟨.privateRow 10 18, 55116998530262428867507369569600⟩, ⟨.privateRow 10 19, 22099246383024771436063724736600⟩, ⟨.privateRow 11 11, 635720859633938049221538288000⟩, ⟨.privateRow 11 12, 3187686024735889361096570558400⟩, ⟨.privateRow 11 13, 7980741868635283817919619123200⟩, ⟨.privateRow 11 14, 15066584373324331766550457425600⟩, ⟨.privateRow 11 15, 22591207639173307585518119707200⟩, ⟨.privateRow 12 9, 393352281898499167955826815700⟩, ⟨.privateRow 12 10, 2080396513152062266077484047480⟩, ⟨.privateRow 12 11, 5581856190750131050039828146600⟩, ⟨.privateRow 12 12, 6737418572005062671653649048400⟩, ⟨.privateRow 13 7, 264438508839327171735009624000⟩, ⟨.privateRow 13 8, 1573409127593996671823307262800⟩, ⟨.privateRow 13 9, 2277697022802738039210882894720⟩, ⟨.privateRow 14 5, 216447816494412240568285655200⟩, ⟨.privateRow 14 6, 802130143479292420929529192800⟩, ⟨.privateRow 15 3, 287078156613641498016884132160⟩, ⟨.hall 5 30, 1023595688577333189662943397999200⟩, ⟨.hall 4 31, 4368275428553307884941445745052425⟩, ⟨.hall 3 32, 11905653115052464998211124750006400⟩, ⟨.hall 2 33, 27545149127078901734720032480752000⟩, ⟨.assumptionRow 18, 20480225671033497401253002496⟩]
  caps := #[0, 0, 1034618682583891666823916315012480, 117635419997722400501943979695360, 20379680730644040151797165858000, 2479925250315480807871322843552, 0, 5921116035817655599890668785080, 0, 3927283269371268700576404848960, 0, 508730223417984067993010039808, 374336079075130377273760393548, 72979236032912430370547633664, 10903761521883033518611824928000, 0, 13207420093407365327112077575680, 2301605291118686628429460035072, 278166083568137047915090677504, 17567429955245326195079040000] }

theorem case_55_36_18_checked :
    (Witness.linear .conditional case_55_36_18).check 55 36 18 = true := by
  change case_55_36_18.check 55 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_19 : Certificate := {
  objectiveScale := 7867548228540000000
  eta := 4008007641835186568731152000
  rows := #[⟨.count 2, 541582634155802895543888000⟩, ⟨.count 3, 71533068762889007754480000⟩, ⟨.count 4, 9080453477663536144176000⟩, ⟨.count 5, 1137778643184459864588000⟩, ⟨.count 6, 142319543200790263308000⟩, ⟨.count 7, 23869482024848808348000⟩, ⟨.count 8, 6700205480659314624000⟩, ⟨.count 9, 2740993151178810528000⟩, ⟨.count 10, 685248287794702632000⟩, ⟨.path 7, 4297509300579104610000⟩, ⟨.privateRow 2 34, 43867082807561615257656000⟩, ⟨.privateRow 3 30, 707709203894640107160000⟩, ⟨.privateRow 3 31, 7701327849561160550736000⟩, ⟨.privateRow 3 32, 13511801877434590353624000⟩, ⟨.privateRow 4 27, 108197849441584400998500⟩, ⟨.privateRow 4 28, 1308989831357432413589400⟩, ⟨.privateRow 4 29, 2938694420210580098817750⟩, ⟨.privateRow 4 30, 4879110569158239969555000⟩, ⟨.privateRow 4 31, 8333275875859387261809000⟩, ⟨.privateRow 5 25, 190692633840621707995200⟩, ⟨.privateRow 5 26, 557094168193985930508000⟩, ⟨.privateRow 5 27, 1033690951042417411904160⟩, ⟨.privateRow 5 28, 1710206510796162997417800⟩, ⟨.privateRow 5 29, 3046778854715642922876000⟩, ⟨.privateRow 5 30, 3759569047766449676959200⟩, ⟨.privateRow 6 22, 13782615143003064358000⟩, ⟨.privateRow 6 23, 93178471419369854768250⟩, ⟨.privateRow 6 24, 209813003383834826118000⟩, ⟨.privateRow 6 25, 380555718431257024656000⟩, ⟨.privateRow 6 26, 615940318114895565792000⟩, ⟨.privateRow 6 27, 1097143691642157726567000⟩, ⟨.privateRow 6 28, 1458710509272945012084000⟩, ⟨.privateRow 6 29, 1504659760697972469591000⟩, ⟨.privateRow 7 20, 9206800209584540362800⟩, ⟨.privateRow 7 21, 38366652811870599216000⟩, ⟨.privateRow 7 22, 82197163664516949048000⟩, ⟨.privateRow 7 23, 146908842107823492840000⟩, ⟨.privateRow 7 24, 236122419930020668044000⟩, ⟨.privateRow 7 25, 417087791171042335344000⟩, ⟨.privateRow 7 26, 568111619170367690418000⟩, ⟨.privateRow 7 27, 633588180764846439132000⟩, ⟨.privateRow 7 28, 455584061053223308206000⟩, ⟨.privateRow 8 18, 4368457834691229279000⟩, ⟨.privateRow 8 19, 15933926158692932590200⟩, ⟨.privateRow 8 20, 34303656184833886851000⟩, ⟨.privateRow 8 21, 61060856978039769600750⟩, ⟨.privateRow 8 22, 97646521391126484777000⟩, ⟨.privateRow 8 23, 172024286025573392911500⟩, ⟨.privateRow 8 24, 240034861344619946404800⟩, ⟨.privateRow 8 25, 278686671711173367642000⟩, ⟨.privateRow 8 26, 66234322928600933106000⟩, ⟨.privateRow 9 16, 1871743008328122930000⟩, ⟨.privateRow 9 17, 7025525374864880520000⟩, ⟨.privateRow 9 18, 15509452913753436237600⟩, ⟨.privateRow 9 19, 27909062980675604728000⟩, ⟨.privateRow 9 20, 44664864091951936833000⟩, ⟨.privateRow 9 21, 78520752215713623816000⟩, ⟨.privateRow 9 22, 112939069655052841200000⟩, ⟨.privateRow 9 23, 69362354464552677528000⟩, ⟨.privateRow 10 14, 790671101301579960000⟩, ⟨.privateRow 10 15, 3323454195804307765200⟩, ⟨.privateRow 10 16, 7737076122191096990400⟩, ⟨.privateRow 10 17, 14287426800519549877200⟩, ⟨.privateRow 10 18, 23153778257596563376800⟩, ⟨.privateRow 10 19, 40780838727382240386900⟩, ⟨.privateRow 10 20, 37659288044946014647200⟩, ⟨.privateRow 11 12, 348062622371912448000⟩, ⟨.privateRow 11 13, 1698478662055245840000⟩, ⟨.privateRow 11 14, 4308181364931510066000⟩, ⟨.privateRow 11 15, 8333726651563858272000⟩, ⟨.privateRow 11 16, 13880084762774921090400⟩, ⟨.privateRow 11 17, 15388476981463754168000⟩, ⟨.privateRow 12 10, 160525756307462746200⟩, ⟨.privateRow 12 11, 949694303620237675500⟩, ⟨.privateRow 12 12, 2689745950168522938000⟩, ⟨.privateRow 12 13, 5600953018988645818500⟩, ⟨.privateRow 12 14, 5082258134477377854000⟩, ⟨.privateRow 13 8, 89734894830258678000⟩, ⟨.privateRow 13 9, 586267979557690029600⟩, ⟨.privateRow 13 10, 1897252062125469192000⟩, ⟨.privateRow 13 11, 1974167686265690916000⟩, ⟨.privateRow 14 6, 45747201286014228000⟩, ⟨.privateRow 14 7, 413154411614315996625⟩, ⟨.privateRow 14 8, 855472664048466063600⟩, ⟨.privateRow 15 4, 60487966144841034800⟩, ⟨.privateRow 15 5, 320230409002099596000⟩, ⟨.hall 6 29, 41762620054002388741200⟩, ⟨.hall 5 30, 821504629235515241016000⟩, ⟨.hall 4 31, 2651868045747512016925500⟩, ⟨.hall 3 32, 6449556884723741172384000⟩, ⟨.hall 2 33, 13925539565865303031656000⟩, ⟨.assumptionRow 19, 7438647263351496192⟩]
  caps := #[0, 0, 25470308751023030534640, 24058338164179219860960, 1912555245348180112680, 5069280277914554241540, 1033137684584800759250, 494861596253092980912, 619214375923451618310, 0, 194757928011862449360, 282534356752462214400, 1094646281979243272664, 29325688088217480960, 5028414384693021599277, 0, 22082551286556778617600, 5147629102345492578816, 935662007375924564736, 118442124393288503808] }

theorem case_55_36_19_checked :
    (Witness.linear .conditional case_55_36_19).check 55 36 19 = true := by
  change case_55_36_19.check 55 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_20 : Certificate := {
  objectiveScale := 7157926231456000000
  eta := 3642189487991875275924268800
  rows := #[⟨.count 2, 491977662879741659725104000⟩, ⟨.count 3, 64320967583507321493206400⟩, ⟨.count 4, 8113613826804397043932800⟩, ⟨.count 5, 947241549828210604968000⟩, ⟨.count 6, 102190098232698582506400⟩, ⟨.count 7, 13567916098335112113600⟩, ⟨.count 8, 3517607877346140177600⟩, ⟨.count 9, 1233446918030464737600⟩, ⟨.count 10, 411148972676821579200⟩, ⟨.path 7, 3910121282714936889600⟩, ⟨.privateRow 2 34, 42645467843300405718835200⟩, ⟨.privateRow 3 30, 310303266323034508524000⟩, ⟨.privateRow 3 31, 7077092038946401071600000⟩, ⟨.privateRow 3 32, 13026204485223806526249600⟩, ⟨.privateRow 4 27, 13473694458763340501700⟩, ⟨.privateRow 4 28, 1078875461752613664899760⟩, ⟨.privateRow 4 29, 2672078587435657027678050⟩, ⟨.privateRow 4 30, 4680679796220088954893600⟩, ⟨.privateRow 4 31, 8396561410438427194468500⟩, ⟨.privateRow 5 25, 121414902101133201681120⟩, ⟨.privateRow 5 26, 461970792634608919181520⟩, ⟨.privateRow 5 27, 922417288522367844286080⟩, ⟨.privateRow 5 28, 1625499163006927612283880⟩, ⟨.privateRow 5 29, 3078208401924502324558080⟩, ⟨.privateRow 5 30, 4072485394226941318186560⟩, ⟨.privateRow 6 22, 8010334945181091322800⟩, ⟨.privateRow 6 23, 64364596689373793262450⟩, ⟨.privateRow 6 24, 168750315509508455065200⟩, ⟨.privateRow 6 25, 332312244861735953614800⟩, ⟨.privateRow 6 26, 577210737506155920367200⟩, ⟨.privateRow 6 27, 1103851375030719562747500⟩, ⟨.privateRow 6 28, 1594834356512899415113200⟩, ⟨.privateRow 6 29, 1810141272005461078483800⟩, ⟨.privateRow 7 20, 5254875441259948183680⟩, ⟨.privateRow 7 21, 26334200469519913370400⟩, ⟨.privateRow 7 22, 63518845305598605222300⟩, ⟨.privateRow 7 23, 124526395483018971156000⟩, ⟨.privateRow 7 24, 216781558930938914312400⟩, ⟨.privateRow 7 25, 414898259737184023600800⟩, ⟨.privateRow 7 26, 619493819950173809440800⟩, ⟨.privateRow 7 27, 771504731792632009972800⟩, ⟨.privateRow 7 28, 672796347479347464172800⟩, ⟨.privateRow 8 18, 2301292166510543005800⟩, ⟨.privateRow 8 19, 10496290648295357565660⟩, ⟨.privateRow 8 20, 25342131354452053541400⟩, ⟨.privateRow 8 21, 49741173890597763448875⟩, ⟨.privateRow 8 22, 86953113090520658982000⟩, ⟨.privateRow 8 23, 167452791661165214704500⟩, ⟨.privateRow 8 24, 257765280097814657728560⟩, ⟨.privateRow 8 25, 335272000809553985677500⟩, ⟨.privateRow 8 26, 306178452324003617958600⟩, ⟨.privateRow 9 16, 875595034404342252000⟩, ⟨.privateRow 9 17, 4331599782847726334400⟩, ⟨.privateRow 9 18, 10863469522505352392640⟩, ⟨.privateRow 9 19, 21643694067826755724800⟩, ⟨.privateRow 9 20, 38059831984597442019000⟩, ⟨.privateRow 9 21, 73739241940879476561600⟩, ⟨.privateRow 9 22, 117504853617062730218400⟩, ⟨.privateRow 9 23, 160567378796054720730240⟩, ⟨.privateRow 9 24, 59833596329274118150800⟩, ⟨.privateRow 10 14, 316268440520631984000⟩, ⟨.privateRow 10 15, 1874154067118511698520⟩, ⟨.privateRow 10 16, 5072083235658608027040⟩, ⟨.privateRow 10 17, 10439072416264499895888⟩, ⟨.privateRow 10 18, 18629616784178648888640⟩, ⟨.privateRow 10 19, 36309593649521805713100⟩, ⟨.privateRow 10 20, 59845669751487643863840⟩, ⟨.privateRow 10 21, 54244254461828660349120⟩, ⟨.privateRow 11 12, 114208047965783772000⟩, ⟨.privateRow 11 13, 857438883189268934400⟩, ⟨.privateRow 11 14, 2600136558687677209200⟩, ⟨.privateRow 11 15, 5664719179102875091200⟩, ⟨.privateRow 11 16, 9515814556509103883040⟩, ⟨.privateRow 11 17, 22344170095350229526400⟩, ⟨.privateRow 11 18, 28038075775599916026000⟩, ⟨.privateRow 12 10, 41876284254120716400⟩, ⟨.privateRow 12 11, 417267260960702852700⟩, ⟨.privateRow 12 12, 1468891201529157436800⟩, ⟨.privateRow 12 13, 3491435199687314729850⟩, ⟨.privateRow 12 14, 6761116439574399302400⟩, ⟨.privateRow 12 15, 12537759505683742490160⟩, ⟨.privateRow 13 8, 20190351336808202550⟩, ⟨.privateRow 13 9, 222542539179041521440⟩, ⟨.privateRow 13 10, 915295927268638515600⟩, ⟨.privateRow 13 11, 2451833434131375571200⟩, ⟨.privateRow 13 12, 4872604789283046215400⟩, ⟨.privateRow 14 6, 13724160385804268400⟩, ⟨.privateRow 14 7, 131237283689253316575⟩, ⟨.privateRow 14 8, 637715985927038338320⟩, ⟨.privateRow 14 9, 1966476123851668743600⟩, ⟨.privateRow 14 10, 17946978966051735600⟩, ⟨.privateRow 15 5, 76855298160503903040⟩, ⟨.privateRow 15 6, 530781902920980080370⟩, ⟨.privateRow 15 7, 217756678121427725280⟩, ⟨.privateRow 16 3, 136097923825892328300⟩, ⟨.privateRow 16 4, 144103684050944818200⟩, ⟨.hall 6 29, 202747021379486457073200⟩, ⟨.hall 5 30, 1113509310187378161657600⟩, ⟨.hall 4 31, 3070165014626392087955550⟩, ⟨.hall 3 32, 6886653925898388824582400⟩, ⟨.hall 2 33, 14045305738832088280560000⟩, ⟨.assumptionRow 20, 4897076719372437600⟩]
  caps := #[0, 0, 53355007316716839333600, 48656210709933176750400, 3781417967495900361630, 100615694205653827200, 239212963600847700750, 0, 388718140114422983865, 0, 0, 106976349094931316000, 903843510213965669810, 23808091052371425800, 0, 7592063173248852758460, 0, 16900224332783386795200, 4084599734340048924000, 773439994033304998400] }

theorem case_55_36_20_checked :
    (Witness.linear .conditional case_55_36_20).check 55 36 20 = true := by
  change case_55_36_20.check 55 36 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_21 : Certificate := {
  objectiveScale := 10796004864476463632000000
  eta := 7706912839431937660457063642707200
  rows := #[⟨.count 2, 1050482511912062635541737784582400⟩, ⟨.count 3, 138473319387352956318086308934400⟩, ⟨.count 4, 17257632510481384814038708862400⟩, ⟨.count 5, 1984952202046078324109738688000⟩, ⟨.count 6, 194678004431442297172301294400⟩, ⟨.count 7, 14094335162457360881252582400⟩, ⟨.count 8, 587263965102390036718857600⟩, ⟨.path 7, 6770203138848972731972263200⟩, ⟨.path 8, 459226266647813033742172800⟩, ⟨.privateRow 2 34, 91758232755353136067211343427200⟩, ⟨.privateRow 3 30, 664195544530803131529027945600⟩, ⟨.privateRow 3 31, 15060188630395758361642863532800⟩, ⟨.privateRow 3 32, 27888578438747400453741828566400⟩, ⟨.privateRow 4 27, 82070139123059007631460349600⟩, ⟨.privateRow 4 28, 2288039134435421822060341095360⟩, ⟨.privateRow 4 29, 5646377856469295155853988645300⟩, ⟨.privateRow 4 30, 9950527216699258983409733317200⟩, ⟨.privateRow 4 31, 18069268014250706744161464994200⟩, ⟨.privateRow 5 25, 301669109387882013433381165440⟩, ⟨.privateRow 5 26, 972117616899489640781948947200⟩, ⟨.privateRow 5 27, 1928610097234155023986931489856⟩, ⟨.privateRow 5 28, 3419843611179003020326759404960⟩, ⟨.privateRow 5 29, 6580625511885838382455606760640⟩, ⟨.privateRow 5 30, 8902510626176661283632178015680⟩, ⟨.privateRow 6 22, 29568274560393352324955814400⟩, ⟨.privateRow 6 23, 147337712387451864614120885100⟩, ⟨.privateRow 6 24, 353910433826347481414071540800⟩, ⟨.privateRow 6 25, 685644661732399948584426220800⟩, ⟨.privateRow 6 26, 1198224031196661511419321104160⟩, ⟨.privateRow 6 27, 2334840926397126402325923052200⟩, ⟨.privateRow 6 28, 3471121543065193377032927654400⟩, ⟨.privateRow 6 29, 4084966193826146353270893547200⟩, ⟨.privateRow 7 19, 2310921836701612741893686400⟩, ⟨.privateRow 7 20, 17542413586129965239701874880⟩, ⟨.privateRow 7 21, 59271713049262651563124699200⟩, ⟨.privateRow 7 22, 132401806989289739439177439800⟩, ⟨.privateRow 7 23, 253698032924232495862546483200⟩, ⟨.privateRow 7 24, 443069687956713911631638100000⟩, ⟨.privateRow 7 25, 865694200442648901556363971840⟩, ⟨.privateRow 7 26, 1335343874934157773671352366000⟩, ⟨.privateRow 7 27, 1737965757294444571523979148800⟩, ⟨.privateRow 7 28, 1622987862412612350763522814400⟩, ⟨.privateRow 8 16, 101641840113875198662879200⟩, ⟨.privateRow 8 17, 1578271906212673223681929800⟩, ⟨.privateRow 8 18, 8201675148986788126448590800⟩, ⟨.privateRow 8 19, 24019096172687752501801275840⟩, ⟨.privateRow 8 20, 52649845760221217875280914000⟩, ⟨.privateRow 8 21, 100266146041778373925421203050⟩, ⟨.privateRow 8 22, 175036122170071287551329503600⟩, ⟨.privateRow 8 23, 343757408905871934618536291400⟩, ⟨.privateRow 8 24, 547843871444892105504104283600⟩, ⟨.privateRow 8 25, 746981411611330677017739402900⟩, ⟨.privateRow 8 26, 809151866583576405592465963200⟩, ⟨.privateRow 8 27, 114883513173155050933126518000⟩, ⟨.privateRow 9 14, 68641242674305328967139200⟩, ⟨.privateRow 9 15, 850095390043319843362262400⟩, ⟨.privateRow 9 16, 3794970926002565919099890400⟩, ⟨.privateRow 9 17, 10473682947859154539167724800⟩, ⟨.privateRow 9 18, 22801858135930071334784007360⟩, ⟨.privateRow 9 19, 43398213825142277865001638400⟩, ⟨.privateRow 9 20, 75670296594272734390399162800⟩, ⟨.privateRow 9 21, 148844721336860311124743180800⟩, ⟨.privateRow 9 22, 245200501307978215785781195200⟩, ⟨.privateRow 9 23, 351098430918123439770717738240⟩, ⟨.privateRow 9 24, 272210194733255563610934108000⟩, ⟨.privateRow 10 12, 38439095897610984221597952⟩, ⟨.privateRow 10 13, 459896325917845704079832640⟩, ⟨.privateRow 10 14, 1892386259574694607832514560⟩, ⟨.privateRow 10 15, 5101188351412124364407894880⟩, ⟨.privateRow 10 16, 11073080465959527841108046400⟩, ⟨.privateRow 10 17, 21107868534775631710684975392⟩, ⟨.privateRow 10 18, 36816111848600742665574927360⟩, ⟨.privateRow 10 19, 72223457526370638322611777000⟩, ⟨.privateRow 10 20, 122325558569879526752338768320⟩, ⟨.privateRow 10 21, 184259407814193986657239016160⟩, ⟨.privateRow 10 22, 4593471959764512614480955264⟩, ⟨.privateRow 11 10, 26693816595563183487220800⟩, ⟨.privateRow 11 11, 270497341501706926003837440⟩, ⟨.privateRow 11 12, 1067752663822527339488832000⟩, ⟨.privateRow 11 13, 2862398487247313675475830400⟩, ⟨.privateRow 11 14, 6219659266766221752522446400⟩, ⟨.privateRow 11 15, 11886028516824406610946134400⟩, ⟨.privateRow 11 16, 20773128074667269389755226560⟩, ⟨.privateRow 11 17, 40544941429038746474478704000⟩, ⟨.privateRow 11 18, 70031227838460011878723768800⟩, ⟨.privateRow 11 19, 25137948428278929363965644800⟩, ⟨.privateRow 12 8, 17272469561835001079966400⟩, ⟨.privateRow 12 9, 178931989367134464312776925⟩, ⟨.privateRow 12 10, 704716758122868044062629120⟩, ⟨.privateRow 12 11, 1898121030063082082966307600⟩, ⟨.privateRow 12 12, 4156021906878452567548838400⟩, ⟨.privateRow 12 13, 7989236858580431124529458600⟩, ⟨.privateRow 12 14, 14014253712670671330790920000⟩, ⟨.privateRow 12 15, 27182980784676878824624121160⟩, ⟨.privateRow 12 16, 10285275833251581059756658800⟩, ⟨.privateRow 13 6, 13982475359580715159972800⟩, ⟨.privateRow 13 7, 140647252146370723079726400⟩, ⟨.privateRow 13 8, 558425109673254811701413700⟩, ⟨.privateRow 13 9, 1526886309266214095469029760⟩, ⟨.privateRow 13 10, 3379764044058652864381996800⟩, ⟨.privateRow 13 11, 6572838994030596180199521600⟩, ⟨.privateRow 13 12, 11325805041260379279577968000⟩, ⟨.privateRow 14 4, 14350435237464418190498400⟩, ⟨.privateRow 14 5, 136329134755911972809734800⟩, ⟨.privateRow 14 6, 529277817287658247378970400⟩, ⟨.privateRow 14 7, 1397373631248097721299781700⟩, ⟨.privateRow 14 8, 3617266375523531011884963360⟩, ⟨.privateRow 14 9, 2395497653568167522228197200⟩, ⟨.privateRow 15 2, 38172157731655352386725744⟩, ⟨.privateRow 15 3, 160724874659601483733582080⟩, ⟨.privateRow 15 4, 636202628860922539778762400⟩, ⟨.privateRow 15 5, 1796336834430840112316505600⟩, ⟨.privateRow 16 1, 286291182987415142900443080⟩, ⟨.privateRow 16 2, 602718279973505564000932800⟩, ⟨.hall 6 29, 584252139909936350673399458880⟩, ⟨.hall 5 30, 2621442148223260635358078593600⟩, ⟨.hall 4 31, 6883513630953662842112528304750⟩, ⟨.hall 3 32, 15087024814013164548775349510400⟩, ⟨.hall 2 33, 30400306417490322640788382521600⟩, ⟨.assumptionRow 21, 2457081101012335121484160⟩]
  caps := #[0, 0, 71811117023080624784907312000, 6982893830910455000854190880, 0, 4615399257226366713454117768, 146853357478755588604463520, 868014626276011500126742440, 167903601045368178003620530, 16231887246659222704325760, 910764656036803714075169352, 0, 183759911966318174479895595, 35259214180738366866247200, 3243106209159105662746650420, 4644287821284587127037722336, 0, 76547894948778687877109546880, 22597190145914006204664001920, 5580633995254728336351384960] }

theorem case_55_36_21_checked :
    (Witness.linear .conditional case_55_36_21).check 55 36 21 = true := by
  change case_55_36_21.check 55 36 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_22 : Certificate := {
  objectiveScale := 1006034931054144992000000
  eta := 931277427203558053420630500672000
  rows := #[⟨.count 2, 120229578993685356153318840480000⟩, ⟨.count 3, 14754298269933569209876165152000⟩, ⟨.count 4, 1680732164507376208376388240000⟩, ⟨.count 5, 168675629412926644568239680000⟩, ⟨.count 6, 13425203157355385996247648000⟩, ⟨.count 7, 695091879448873535308680000⟩, ⟨.path 6, 1471517194287891169803384000⟩, ⟨.path 7, 671826979440976878615096000⟩, ⟨.privateRow 2 34, 11756691370080987126406305696000⟩, ⟨.privateRow 3 30, 20482040714426806840429104000⟩, ⟨.privateRow 4 28, 221025315827152806757454066400⟩, ⟨.privateRow 5 25, 24406330868115304285486108800⟩, ⟨.privateRow 5 26, 92731435312963719597158433600⟩, ⟨.privateRow 5 27, 160073172312867385695259456320⟩, ⟨.privateRow 5 30, 2783027402720851830629834548800⟩, ⟨.privateRow 6 22, 2309249688391257633969948000⟩, ⟨.privateRow 6 24, 56712877440366662637994872000⟩, ⟨.privateRow 6 25, 53664954715005530667692922000⟩, ⟨.privateRow 7 19, 173321611498939894518528000⟩, ⟨.privateRow 7 20, 1310744686960732952296368000⟩, ⟨.privateRow 7 21, 1977150234876795833766912000⟩, ⟨.privateRow 7 22, 13524501997276653644148888000⟩, ⟨.privateRow 7 23, 28762618260623183269222032000⟩, ⟨.privateRow 7 24, 41808121568184388688018748000⟩, ⟨.privateRow 7 25, 50582829055893739840891656000⟩, ⟨.privateRow 7 26, 91732268319267053131165512000⟩, ⟨.privateRow 7 27, 146194372054751649083398944000⟩, ⟨.privateRow 7 28, 177397377519344652975565260000⟩, ⟨.privateRow 8 15, 827490332677230399177000⟩, ⟨.privateRow 8 16, 7129147481526908054448000⟩, ⟨.privateRow 8 17, 109090808857948207624834500⟩, ⟨.privateRow 8 18, 592934436560175455119374000⟩, ⟨.privateRow 8 19, 1171229816871351906995125800⟩, ⟨.privateRow 8 20, 4025096864882643601685634000⟩, ⟨.privateRow 8 21, 10036837117625296819217627250⟩, ⟨.privateRow 8 22, 18798925377761320208503086000⟩, ⟨.privateRow 8 23, 33974546418839940909143148000⟩, ⟨.privateRow 8 24, 42486332644846646723184217200⟩, ⟨.privateRow 8 25, 61674923220265674726659752500⟩, ⟨.privateRow 9 13, 561690407635453361865600⟩, ⟨.privateRow 9 14, 5416300359341871703704000⟩, ⟨.privateRow 9 15, 57033179852215264435584000⟩, ⟨.privateRow 9 16, 267505056636384663588492000⟩, ⟨.privateRow 9 17, 596668401201842957581776000⟩, ⟨.privateRow 9 18, 1506453673278285916523539200⟩, ⟨.privateRow 9 19, 3658476855065586230284608000⟩, ⟨.privateRow 9 20, 7619681436079697012058030000⟩, ⟨.privateRow 9 21, 16488421916138733437564688000⟩, ⟨.privateRow 9 22, 27194241085670474514723024000⟩, ⟨.privateRow 9 23, 37460818356431291062902460800⟩, ⟨.privateRow 9 24, 53661093093453036925830096000⟩, ⟨.privateRow 9 25, 48490732891168688729857248000⟩, ⟨.privateRow 9 26, 31527682580577997201516128000⟩, ⟨.privateRow 10 11, 473926281442413774074100⟩, ⟨.privateRow 10 12, 3538649568103356179753280⟩, ⟨.privateRow 10 13, 30872912048248668711112800⟩, ⟨.privateRow 10 14, 130657830206893151252428800⟩, ⟨.privateRow 10 15, 312791345751993090888906000⟩, ⟨.privateRow 10 16, 687968623824769376765020800⟩, ⟨.privateRow 10 17, 1514289254464800490921564320⟩, ⟨.privateRow 10 18, 3145185437554721099766427200⟩, ⟨.privateRow 10 19, 7314578227782214189059659400⟩, ⟨.privateRow 10 20, 13761735953015827624771123200⟩, ⟨.privateRow 10 21, 21403774673356585807250553600⟩, ⟨.privateRow 10 22, 28255105758571555279278582720⟩, ⟨.privateRow 10 23, 34640219763188907574624117200⟩, ⟨.privateRow 11 9, 495609183207752966352000⟩, ⟨.privateRow 11 10, 2106339028632950106996000⟩, ⟨.privateRow 11 11, 18535783451969960941564800⟩, ⟨.privateRow 11 12, 72819149275596275127576000⟩, ⟨.privateRow 11 13, 182765417253689824668576000⟩, ⟨.privateRow 11 15, 1544903934819149223931248000⟩, ⟨.privateRow 11 16, 1147533502799231218291420800⟩, ⟨.privateRow 11 17, 3564861787126344003307008000⟩, ⟨.privateRow 11 18, 7335325667214248747613570000⟩, ⟨.privateRow 11 19, 12978659283285200573564496000⟩, ⟨.privateRow 11 20, 19553847315809220159946200000⟩, ⟨.privateRow 11 21, 25582751306164358819530617600⟩, ⟨.privateRow 11 22, 25657315707777965253318276000⟩, ⟨.privateRow 12 7, 643603592082290310471000⟩, ⟨.privateRow 12 8, 2044387880731980986202000⟩, ⟨.privateRow 12 9, 12308918698573802187757875⟩, ⟨.privateRow 12 10, 47884107250922399099042400⟩, ⟨.privateRow 12 11, 124123549901584559876550000⟩, ⟨.privateRow 12 12, 165752678945500612265916000⟩, ⟨.privateRow 12 13, 212389185387155802455430000⟩, ⟨.privateRow 12 14, 1792494513366640541053596000⟩, ⟨.privateRow 12 15, 1560481269362721086767986600⟩, ⟨.privateRow 12 16, 4261942986768926435938962000⟩, ⟨.privateRow 12 17, 8212220934072003789032342250⟩, ⟨.privateRow 12 18, 13802538749056203058272360000⟩, ⟨.privateRow 12 19, 20144148828583604427431829000⟩, ⟨.privateRow 12 21, 48140905084163232932920329000⟩, ⟨.privateRow 13 6, 2206640887139281064472000⟩, ⟨.privateRow 13 7, 10513994815193045071896000⟩, ⟨.privateRow 13 8, 38478300469491213561730500⟩, ⟨.privateRow 13 9, 101946808985834785178606400⟩, ⟨.privateRow 13 10, 190086350706426640268088000⟩, ⟨.privateRow 13 11, 249010937033332717044648000⟩, ⟨.privateRow 13 12, 319411268413410934082322000⟩, ⟨.privateRow 13 13, 2856195722826280345086576000⟩, ⟨.privateRow 13 14, 2311676993367110843140867200⟩, ⟨.privateRow 13 15, 5845391710031955539786328000⟩, ⟨.privateRow 13 16, 10808678725429983474049974000⟩, ⟨.privateRow 13 18, 11124780032512685486535588000⟩, ⟨.privateRow 14 4, 2264710384169262145116000⟩, ⟨.privateRow 14 5, 9562110510936884612712000⟩, ⟨.privateRow 14 6, 37967203499308218315180000⟩, ⟨.privateRow 14 7, 102195056085637954298359500⟩, ⟨.privateRow 14 8, 215147486496079903786020000⟩, ⟨.privateRow 14 9, 359603656000590696328062000⟩, ⟨.privateRow 14 10, 460084624968540101942412000⟩, ⟨.privateRow 14 11, 652614042371442374817594000⟩, ⟨.privateRow 14 12, 5261333987949590374403580000⟩, ⟨.privateRow 14 13, 4376099875330265243007646800⟩, ⟨.privateRow 14 14, 9609921063491569035775560000⟩, ⟨.privateRow 14 15, 17405431657532864216289018000⟩, ⟨.privateRow 14 16, 7204367262097304206777584000⟩, ⟨.privateRow 14 17, 10886462816701643131572612000⟩, ⟨.privateRow 15 2, 6024129621890237306008560⟩, ⟨.privateRow 15 3, 12682378151347868012649600⟩, ⟨.privateRow 15 4, 46854341503590734602288800⟩, ⟨.privateRow 15 6, 549701827997484154173281100⟩, ⟨.privateRow 15 7, 417672987117723119883260160⟩, ⟨.privateRow 15 8, 869195845444162811295520800⟩, ⟨.privateRow 15 9, 1195558032652062480730929600⟩, ⟨.privateRow 15 10, 1576313917727945428405573200⟩, ⟨.privateRow 15 11, 11730623318262625735882123200⟩, ⟨.privateRow 15 12, 10891626356377549049263476480⟩, ⟨.privateRow 15 13, 19959949480529652940575028800⟩, ⟨.privateRow 15 14, 35542364769152400105450504000⟩, ⟨.privateRow 15 15, 27401183880140736546187507200⟩, ⟨.privateRow 15 17, 34072477141411182202784415360⟩, ⟨.privateRow 16 1, 45180972164176779795064200⟩, ⟨.privateRow 16 2, 71338377101331757571154000⟩, ⟨.privateRow 16 3, 125502700456046610541845000⟩, ⟨.privateRow 16 4, 265770424495157528206260000⟩, ⟨.privateRow 16 5, 1750762671361850217058737750⟩, ⟨.privateRow 16 7, 5744437889445333431086734000⟩, ⟨.privateRow 16 8, 2537085359988388403876682000⟩, ⟨.privateRow 16 9, 5007557748196259760619615500⟩, ⟨.privateRow 16 11, 102108997091039522336845092000⟩, ⟨.privateRow 16 12, 22741089322635645830182314000⟩, ⟨.privateRow 16 13, 96009565848875657064511425000⟩, ⟨.privateRow 16 16, 298917311838193575124144747200⟩, ⟨.privateRow 17 0, 361447777313414238360513600⟩, ⟨.privateRow 17 1, 253647563026957360252992000⟩, ⟨.privateRow 17 2, 669347735765581922889840000⟩, ⟨.privateRow 17 5, 21526223182221114640137254400⟩, ⟨.privateRow 17 6, 15146383049324025226535808000⟩, ⟨.privateRow 17 7, 12975048416378972659095360000⟩, ⟨.privateRow 17 9, 48631155493077552070323648000⟩, ⟨.privateRow 17 12, 160844260904469336070428552000⟩, ⟨.privateRow 17 17, 4828942304907214224496461696000⟩, ⟨.privateRow 18 1, 13654693809617871226952736000⟩, ⟨.privateRow 18 2, 1204825924378047461201712000⟩, ⟨.privateRow 18 5, 400862796839496076734112464000⟩, ⟨.privateRow 18 10, 1024102035721340342021455200000⟩, ⟨.privateRow 18 12, 643721279596271072127771840000⟩, ⟨.privateRow 18 17, 42254449993862502511805241552000⟩, ⟨.privateRow 19 0, 245784488573121682085149248000⟩, ⟨.privateRow 19 13, 77864525979964948884575281766400⟩, ⟨.privateRow 19 17, 498082266093431088745554951072000⟩, ⟨.hall 9 14, 6239156338414000729728⟩, ⟨.hall 18 14, 74699207311438942594506144000⟩, ⟨.hall 7 18, 26667610286179042857600⟩, ⟨.hall 8 22, 279294643686227844875200⟩, ⟨.hall 6 26, 32852679684004582133674800⟩, ⟨.hall 4 28, 338982933534340800575871000⟩, ⟨.hall 3 32, 7244727812914688297611458048000⟩, ⟨.hall 2 33, 10065115772254208490879102048000⟩]
  caps := #[0, 0, 11375049598354871372431488000, 369212811638115625027848000, 492841425199543808147760000, 0, 32690516193977851599390000, 0, 18135444159390940898808600, 49436237595631323794380800, 1142998678772880278649300, 67376196065944429120436000, 49740615046392189137010100, 348416982179886483864000, 1646189979857146821432091900, 80619101047542775037600280, 0, 49564870899591939042479328000, 176224913020469620952845200000, 0] }

theorem case_55_36_22_checked :
    (Witness.linear .conditional case_55_36_22).check 55 36 22 = true := by
  change case_55_36_22.check 55 36 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_36_23 : Certificate := {
  objectiveScale := 71451475188982674888960000
  eta := 62217221819280875174493050735750400
  rows := #[⟨.count 2, 7199653055283214566776215909228800⟩, ⟨.count 3, 767374354242277730455703042246400⟩, ⟨.count 4, 72211723707968025806109089404800⟩, ⟨.count 5, 5546215338553611813065214240000⟩, ⟨.count 6, 285233931697042893243353875200⟩, ⟨.path 5, 456198730366287827987876808000⟩, ⟨.path 6, 185801929905920283213551092800⟩, ⟨.path 7, 6028950143325195619713180000⟩, ⟨.privateRow 2 34, 782570984269914626823501729264000⟩, ⟨.privateRow 3 30, 388235073698752826914564996800⟩, ⟨.privateRow 3 33, 1297592540608003019784737523590400⟩, ⟨.privateRow 4 28, 10590498188968121757048026591280⟩, ⟨.privateRow 5 25, 985641697308670442207589502080⟩, ⟨.privateRow 5 26, 4252098426224435723349997584000⟩, ⟨.privateRow 5 30, 217494834501379887249352376421600⟩, ⟨.privateRow 6 21, 1584632953872460518018632640⟩, ⟨.privateRow 6 22, 73069186206341234997525838400⟩, ⟨.privateRow 6 23, 457067567632587830665999352100⟩, ⟨.privateRow 6 24, 1413153030649833540533044893600⟩, ⟨.privateRow 6 25, 2594176198235373906373003184400⟩, ⟨.privateRow 7 18, 304737106513934715003583200⟩, ⟨.privateRow 7 19, 4155505997917291568230680000⟩, ⟨.privateRow 7 20, 38396875420755774090451483200⟩, ⟨.privateRow 7 21, 169636989292756991351994648000⟩, ⟨.privateRow 7 22, 474247122012310900224326355000⟩, ⟨.privateRow 7 23, 1052910236878003573868094753600⟩, ⟨.privateRow 7 24, 2145653966964614328340229311200⟩, ⟨.privateRow 7 25, 3144155570168172815520970024320⟩, ⟨.privateRow 8 16, 246133816799716500579817200⟩, ⟨.privateRow 8 17, 2399804713797235880653217700⟩, ⟨.privateRow 8 18, 16386545318453853084056314800⟩, ⟨.privateRow 8 19, 62181606584168378596481151960⟩, ⟨.privateRow 8 20, 167571548904162544950303695200⟩, ⟨.privateRow 8 21, 384235399175757433780142967300⟩, ⟨.privateRow 8 22, 808010437921697896832000854800⟩, ⟨.privateRow 8 24, 7179149123808530983411914817200⟩, ⟨.privateRow 8 25, 2193154863442473902041412842500⟩, ⟨.privateRow 8 28, 122383640924422237284299027452800⟩, ⟨.privateRow 9 14, 110813493277794441819484800⟩, ⟨.privateRow 9 15, 1193376081453170911902144000⟩, ⟨.privateRow 9 16, 6981250076501049834627542400⟩, ⟨.privateRow 9 17, 24258081073902637809210854400⟩, ⟨.privateRow 9 18, 64149931258515202369299750720⟩, ⟨.privateRow 9 19, 146864816424170233558090521600⟩, ⟨.privateRow 9 20, 310277781177824437094557440000⟩, ⟨.privateRow 9 21, 765499611563004004089000998400⟩, ⟨.privateRow 9 22, 561344219114214044110236835200⟩, ⟨.privateRow 9 23, 4379726020215580841808225544320⟩, ⟨.privateRow 9 24, 4011309939789561550813075404000⟩, ⟨.privateRow 9 25, 3041756514813272231650311436800⟩, ⟨.privateRow 9 26, 530962853040552067978061419200⟩, ⟨.privateRow 10 12, 93083334353347331128367232⟩, ⟨.privateRow 10 13, 598392863700089985825217920⟩, ⟨.privateRow 10 14, 3222115419923561462135788800⟩, ⟨.privateRow 10 15, 10646406366664100997807002160⟩, ⟨.privateRow 10 16, 27480738937499587076306598720⟩, ⟨.privateRow 10 17, 62202938181624354026531402784⟩, ⟨.privateRow 10 18, 130006390313508439142619567360⟩, ⟨.privateRow 10 20, 1341297603983751703227225967680⟩, ⟨.privateRow 10 21, 440633233995157928728908384480⟩, ⟨.privateRow 10 22, 1412725765480752444535229480064⟩, ⟨.privateRow 10 23, 7121573203038720936303556002240⟩, ⟨.privateRow 10 25, 9586652605051241632910541223680⟩, ⟨.privateRow 11 10, 48480903309035068296024600⟩, ⟨.privateRow 11 11, 361990744707461843276983680⟩, ⟨.privateRow 11 12, 1717609145805813848202014400⟩, ⟨.privateRow 11 13, 5429861170611927649154755200⟩, ⟨.privateRow 11 14, 13703935335353912638342953600⟩, ⟨.privateRow 11 15, 30463636697459126551102003200⟩, ⟨.privateRow 11 16, 62520972907331624074553324160⟩, ⟨.privateRow 11 17, 150226159053596664959948227200⟩, ⟨.privateRow 11 20, 3232835915055282447494376393600⟩, ⟨.privateRow 11 23, 10548668865593086300122216566400⟩, ⟨.privateRow 12 8, 62739992517574794265443600⟩, ⟨.privateRow 12 9, 266644968199692875628135300⟩, ⟨.privateRow 12 10, 1066579872798771502512541200⟩, ⟨.privateRow 12 11, 3352108171653281865039415200⟩, ⟨.privateRow 12 12, 8286505165590455519520512400⟩, ⟨.privateRow 12 13, 17954094525445986958961110200⟩, ⟨.privateRow 12 14, 36069792061922090812242302400⟩, ⟨.privateRow 12 15, 83833178001983440097485738320⟩, ⟨.privateRow 12 16, 183688755870899536543826540000⟩, ⟨.privateRow 12 18, 165776985943580484961949260800⟩, ⟨.privateRow 12 19, 2480509257505676257676666650800⟩, ⟨.privateRow 12 20, 1771375852744199711372828424960⟩, ⟨.privateRow 12 21, 182918448184989312680900815800⟩, ⟨.privateRow 12 22, 4128730687604044486226046985200⟩, ⟨.privateRow 13 7, 322662818661813227650852800⟩, ⟨.privateRow 13 8, 799934904599078626884405900⟩, ⟨.privateRow 13 9, 2559791694717051606030098880⟩, ⟨.privateRow 13 10, 6138276002637827830786461600⟩, ⟨.privateRow 13 11, 13220902159527629174001609600⟩, ⟨.privateRow 13 12, 26207391160198385490308155200⟩, ⟨.privateRow 13 13, 58343304210758773617958747200⟩, ⟨.privateRow 13 14, 124149897193777002892459795680⟩, ⟨.privateRow 13 15, 258417066323816638323038553600⟩, ⟨.privateRow 13 17, 346094285255111569182640920000⟩, ⟨.privateRow 13 18, 2192583481367760274450781124000⟩, ⟨.privateRow 13 19, 3056391283492159617599938062720⟩, ⟨.privateRow 13 20, 1479193915018639106627392852800⟩, ⟨.privateRow 14 5, 220087910260063960835921200⟩, ⟨.privateRow 14 6, 932137031689682657658019200⟩, ⟨.privateRow 14 8, 10564219692483070120124217600⟩, ⟨.privateRow 14 9, 10186926132037246187262638400⟩, ⟨.privateRow 14 10, 9751587408445910880114662400⟩, ⟨.privateRow 14 11, 82202834482133889372216568200⟩, ⟨.privateRow 14 12, 93277257966583471401551330400⟩, ⟨.privateRow 14 13, 219867822349803896875085278800⟩, ⟨.privateRow 14 14, 435774062314926642455123976000⟩, ⟨.privateRow 14 16, 702897903110569986921122049600⟩, ⟨.privateRow 14 17, 2357801782616065212435223815600⟩, ⟨.privateRow 14 18, 4750729595709636633019860654720⟩, ⟨.privateRow 14 20, 9226525373922401366163488546400⟩, ⟨.privateRow 15 4, 1232492297456358180681158720⟩, ⟨.privateRow 15 5, 1304991844365555720721226880⟩, ⟨.privateRow 15 6, 4159661503915208859798910680⟩, ⟨.privateRow 15 7, 25142842868109706885895637888⟩, ⟨.privateRow 15 8, 24561810785023138029288805920⟩, ⟨.privateRow 15 9, 24744653048931498858290955840⟩, ⟨.privateRow 15 10, 197815013741745487999325974560⟩, ⟨.privateRow 15 11, 222857016330972401943165881280⟩, ⟨.privateRow 15 12, 479193005251032060648834510336⟩, ⟨.privateRow 15 13, 920671746199899560968825563840⟩, ⟨.privateRow 15 15, 1700311159505150135833992822720⟩, ⟨.privateRow 15 16, 3318485510901244401484019853600⟩, ⟨.privateRow 15 18, 2454200287309973227281357301200⟩, ⟨.privateRow 15 21, 113209347490556324328287153066880⟩, ⟨.privateRow 16 2, 2189295528376425715683637200⟩, ⟨.privateRow 16 3, 4621846115461343177554345200⟩, ⟨.privateRow 16 4, 7340579124556250929056901200⟩, ⟨.privateRow 16 5, 18198519079629038761620234225⟩, ⟨.privateRow 16 7, 249579690234912531587934640800⟩, ⟨.privateRow 16 9, 599684533481109277287676289700⟩, ⟨.privateRow 16 11, 2795292530631020353784867976960⟩, ⟨.privateRow 16 12, 1839494753953614584666629389600⟩, ⟨.privateRow 16 15, 17338855702153228930595126017800⟩, ⟨.privateRow 16 16, 1239579128166732240220075382640⟩, ⟨.privateRow 16 17, 1892645984281420031208504359400⟩, ⟨.privateRow 17 1, 23352485636015207633958796800⟩, ⟨.privateRow 17 3, 65249592218277786036061344000⟩, ⟨.privateRow 17 6, 31692659077449210360372652800⟩, ⟨.privateRow 17 7, 2628052806576172982190901516800⟩, ⟨.privateRow 17 8, 1053780914325186244482390705600⟩, ⟨.privateRow 17 9, 605041673296757652334387008000⟩, ⟨.privateRow 17 10, 9317641768770067845949559923200⟩, ⟨.privateRow 17 13, 37872727597551806380645320096000⟩, ⟨.privateRow 17 14, 10648733450022934681085211340800⟩, ⟨.privateRow 17 16, 88018437422845819473344949988800⟩, ⟨.privateRow 18 3, 707142455665585506165814815600⟩, ⟨.privateRow 18 7, 628571071702742672147390947200⟩, ⟨.privateRow 18 15, 1468970594569309624808452643606400⟩, ⟨.privateRow 19 3, 22628558581298736197306074099200⟩, ⟨.privateRow 19 7, 3085712533813464026905373740800⟩, ⟨.privateRow 19 14, 5872110951847022043200926228742400⟩, ⟨.privateRow 19 16, 28647755163924200025789489809587200⟩, ⟨.hall 17 1, 198496127906129264888649772800⟩, ⟨.hall 15 15, 883843747975496796282644850⟩, ⟨.hall 12 17, 37032922763031037240398000⟩, ⟨.hall 16 18, 297744191859193897332974659200⟩, ⟨.hall 10 19, 21027441539111553697704336⟩, ⟨.hall 8 21, 38106293698230780973134800⟩, ⟨.hall 13 21, 18649188221957514594468295200⟩, ⟨.hall 9 24, 5311319146520912671905808896⟩, ⟨.hall 4 28, 25367457391785464487038406900⟩, ⟨.hall 6 29, 106671151922878552230942274794240⟩, ⟨.hall 5 30, 201597771149535333131613356702400⟩, ⟨.hall 3 32, 464288812032155263812997443705600⟩]
  caps := #[0, 10528021590865240545057261830400, 2380671123918431374105703971200, 0, 10954522673691312195468228240, 7623348779140531603350624440, 8219009088011891456672299200, 8841858010673923781558873520, 0, 12748124961017060880590337120, 927933471212199624188634480, 2972275606893650024602619040, 14893855171116721922035277980, 1228261129285483274301283920, 0, 230688789511021490851022300480, 14595303522509504771224248000, 1612692169132059548457094684800, 0, 0] }

theorem case_55_36_23_checked :
    (Witness.linear .conditional case_55_36_23).check 55 36 23 = true := by
  change case_55_36_23.check 55 36 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_37_1_checked :
    (Witness.rising).check 55 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_37_2_checked :
    (Witness.rising).check 55 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_37_3_checked :
    (Witness.rising).check 55 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_37_4_checked :
    (Witness.rising).check 55 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_37_5_checked :
    (Witness.rising).check 55 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_37_6_checked :
    (Witness.rising).check 55 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_37_7_checked :
    (Witness.rising).check 55 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_37_8_checked :
    (Witness.rising).check 55 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_37_9_checked :
    (Witness.rising).check 55 37 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_37_10_checked :
    (Witness.rising).check 55 37 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_37_11_checked :
    (Witness.linear .positive case_55_37_11).check 55 37 11 = true := by
  change case_55_37_11.check 55 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_37_12_checked :
    (Witness.linear .positive case_55_37_12).check 55 37 12 = true := by
  change case_55_37_12.check 55 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_55_37_13_checked :
    (Witness.linear .positive case_55_37_13).check 55 37 13 = true := by
  change case_55_37_13.check 55 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_55_37_14_checked :
    (Witness.linear .positive case_55_37_14).check 55 37 14 = true := by
  change case_55_37_14.check 55 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_55_37_15_checked :
    (Witness.linear .positive case_55_37_15).check 55 37 15 = true := by
  change case_55_37_15.check 55 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_55_37_16_checked :
    (Witness.linear .positive case_55_37_16).check 55 37 16 = true := by
  change case_55_37_16.check 55 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_55_37_17_checked :
    (Witness.linear .positive case_55_37_17).check 55 37 17 = true := by
  change case_55_37_17.check 55 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_18 : Certificate := {
  objectiveScale := 1928118350631158400000
  eta := 2226417981388525621684818230400
  rows := #[⟨.count 2, 277930835167687830404346470400⟩, ⟨.count 3, 33712827456606870875527224000⟩, ⟨.count 4, 3976970832169217310062194560⟩, ⟨.count 5, 446239201201253173816502400⟩, ⟨.count 6, 48977473302576567857908800⟩, ⟨.count 7, 6593121406116076442410800⟩, ⟨.count 8, 1598332462088745804220800⟩, ⟨.count 9, 479499738626623741266240⟩, ⟨.path 6, 1309511078833464108201600⟩, ⟨.path 7, 1794630948229981029168000⟩, ⟨.privateRow 2 35, 18742046450452633300293100800⟩, ⟨.privateRow 3 31, 1247565083846186464602843600⟩, ⟨.privateRow 3 32, 3771265444298395725058977600⟩, ⟨.privateRow 3 33, 5790225732660163133423884800⟩, ⟨.privateRow 4 28, 333953808703864671949667040⟩, ⟨.privateRow 4 29, 864343564960915141430183856⟩, ⟨.privateRow 4 30, 1431842827147130801168225460⟩, ⟨.privateRow 4 31, 2060228344570419886837774800⟩, ⟨.privateRow 4 32, 3126531427684755849840561480⟩, ⟨.privateRow 5 24, 1451184394150416825419520⟩, ⟨.privateRow 5 25, 60065429064132096414629820⟩, ⟨.privateRow 5 26, 191789566091200623659461920⟩, ⟨.privateRow 5 27, 338851556034122328735457920⟩, ⟨.privateRow 5 28, 514698824995299087555668256⟩, ⟨.privateRow 5 29, 721737488528246368017239400⟩, ⟨.privateRow 5 30, 1114872410806057726128546240⟩, ⟨.privateRow 5 31, 1122672526924616216565176160⟩, ⟨.privateRow 6 22, 8916411806366503379260320⟩, ⟨.privateRow 6 23, 37581954822869769068556800⟩, ⟨.privateRow 6 24, 81367490369130943396419000⟩, ⟨.privateRow 6 25, 131683023458209526768150400⟩, ⟨.privateRow 6 26, 194235449678594252017689600⟩, ⟨.privateRow 6 27, 264478355833913466432707520⟩, ⟨.privateRow 6 28, 401343184007224653280086000⟩, ⟨.privateRow 6 29, 425378425535340931951096800⟩, ⟨.privateRow 6 30, 299516086734987472669519200⟩, ⟨.privateRow 7 19, 636637384453007381343900⟩, ⟨.privateRow 7 20, 6412357615760801619314400⟩, ⟨.privateRow 7 21, 18481670481271414281424560⟩, ⟨.privateRow 7 22, 34872612163919070989047600⟩, ⟨.privateRow 7 23, 55008086334758137778447250⟩, ⟨.privateRow 7 24, 79087556096040916962252000⟩, ⟨.privateRow 7 25, 105629479458833224696401600⟩, ⟨.privateRow 7 26, 157000011642148220300074320⟩, ⟨.privateRow 7 27, 170112997549867972335535800⟩, ⟨.privateRow 7 28, 13360664013452154907107600⟩, ⟨.privateRow 8 17, 558391789639978502115600⟩, ⟨.privateRow 8 18, 3768290769993952781478900⟩, ⟨.privateRow 8 19, 9184357367381164337132400⟩, ⟨.privateRow 8 20, 16429525766553899579219640⟩, ⟨.privateRow 8 21, 25454924396228173919072000⟩, ⟨.privateRow 8 22, 36029077582917145003477200⟩, ⟨.privateRow 8 23, 47388654724190731254903600⟩, ⟨.privateRow 8 24, 69483063976913532877932000⟩, ⟨.privateRow 8 25, 8910703476144757858530960⟩, ⟨.privateRow 9 15, 388166455078695409596480⟩, ⟨.privateRow 9 16, 2217174005102593538675520⟩, ⟨.privateRow 9 17, 5034747255579549283295520⟩, ⟨.privateRow 9 18, 8815045700004598071763200⟩, ⟨.privateRow 9 19, 13500581529776272892985024⟩, ⟨.privateRow 9 20, 18955039050400607648574080⟩, ⟨.privateRow 9 21, 22003710228088400571439680⟩, ⟨.privateRow 10 13, 269940593597210402490624⟩, ⟨.privateRow 10 14, 1408054788030561779908800⟩, ⟨.privateRow 10 15, 3180271770720171138654720⟩, ⟨.privateRow 10 16, 5545325680969009748532720⟩, ⟨.privateRow 10 17, 8480848912476951221789760⟩, ⟨.privateRow 10 18, 3617559139194194670219744⟩, ⟨.privateRow 11 11, 203953881881116001059425⟩, ⟨.privateRow 11 12, 1012277225989539009339840⟩, ⟨.privateRow 11 13, 2364200100172936502076600⟩, ⟨.privateRow 11 14, 3278630691464093957376000⟩, ⟨.privateRow 12 9, 172369187088001998494400⟩, ⟨.privateRow 12 10, 850303355947509858644250⟩, ⟨.privateRow 12 11, 976758726832011324801600⟩, ⟨.privateRow 13 7, 174421201220002022286000⟩, ⟨.privateRow 13 8, 369362543760004282488000⟩, ⟨.privateRow 14 5, 143208986264843765666400⟩, ⟨.hall 5 31, 20492310878334987593326425⟩, ⟨.hall 4 32, 517841958467174876725270080⟩, ⟨.hall 3 33, 1791519145999148771351546400⟩, ⟨.hall 2 34, 4819383372973534277218225920⟩, ⟨.assumptionRow 18, 2327780205517946937120⟩]
  caps := #[0, 421394883958827304137057600, 137793964810941725893992000, 14009389947544726806247440, 8491283846091322388680788, 1777747326520249492305744, 235799928167471187886080, 405341601626025331933380, 0, 255002594421775820966752, 200867090663706225713712, 59674254397820176181760, 1069902999746879650398750, 1045873133302340662112640, 2327780205517946937120, 8087819185871947219309920, 1719542093864005436884320, 283552295702455936194720, 32378350105842904262880] }

theorem case_55_37_18_checked :
    (Witness.linear .conditional case_55_37_18).check 55 37 18 = true := by
  change case_55_37_18.check 55 37 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_19 : Certificate := {
  objectiveScale := 22324071369600000
  eta := 24828811675511696300448000
  rows := #[⟨.count 2, 2831649753285615508646400⟩, ⟨.count 3, 306469420874204158771200⟩, ⟨.count 4, 31285420047575007874560⟩, ⟨.count 5, 2964361957860605702400⟩, ⟨.count 6, 315730859417105932800⟩, ⟨.count 7, 69066125497491922800⟩, ⟨.count 8, 22324404201209510400⟩, ⟨.count 9, 10045981890544279680⟩, ⟨.path 6, 106789700512016121600⟩, ⟨.privateRow 2 34, 48683944461787639804800⟩, ⟨.privateRow 2 35, 248208307010097639004800⟩, ⟨.privateRow 3 31, 19328922621867531172500⟩, ⟨.privateRow 3 32, 49116247247308978136400⟩, ⟨.privateRow 3 33, 74472468321156707201400⟩, ⟨.privateRow 4 28, 3787637482375418151480⟩, ⟨.privateRow 4 29, 10327381005500525558592⟩, ⟨.privateRow 4 30, 17458381722977124930000⟩, ⟨.privateRow 4 31, 26716312145218708892880⟩, ⟨.privateRow 4 32, 42768047112230248328520⟩, ⟨.privateRow 5 24, 8867749446591555520⟩, ⟨.privateRow 5 25, 514487820570999355080⟩, ⟨.privateRow 5 26, 1988728544257032726720⟩, ⟨.privateRow 5 27, 3833718108963956413200⟩, ⟨.privateRow 5 28, 6229720668365519060736⟩, ⟨.privateRow 5 29, 9384770909861581033800⟩, ⟨.privateRow 5 30, 15648410719860312794400⟩, ⟨.privateRow 5 31, 17424177546540271787280⟩, ⟨.privateRow 6 22, 44070765793637703120⟩, ⟨.privateRow 6 23, 314025522985069095200⟩, ⟨.privateRow 6 24, 816186197347345024200⟩, ⟨.privateRow 6 25, 1456183299037822898400⟩, ⟨.privateRow 6 26, 2340939682205996071200⟩, ⟨.privateRow 6 27, 3469092817845451436640⟩, ⟨.privateRow 6 28, 5736873567117067174800⟩, ⟨.privateRow 6 29, 6876647352443402133600⟩, ⟨.privateRow 6 30, 5963805122323112064000⟩, ⟨.privateRow 7 20, 30596393257907677200⟩, ⟨.privateRow 7 21, 151616589782589411480⟩, ⟨.privateRow 7 22, 339605569465621659200⟩, ⟨.privateRow 7 23, 597065692048754578650⟩, ⟨.privateRow 7 24, 945000002838699007200⟩, ⟨.privateRow 7 25, 1385707660775076038400⟩, ⟨.privateRow 7 26, 2268438521895401375520⟩, ⟨.privateRow 7 27, 2797726226501577571200⟩, ⟨.privateRow 7 28, 2346055691502106584000⟩, ⟨.privateRow 8 18, 16685166681633149700⟩, ⟨.privateRow 8 19, 72300627242553528000⟩, ⟨.privateRow 8 20, 154247680277731960920⟩, ⟨.privateRow 8 21, 269288125677089719200⟩, ⟨.privateRow 8 22, 421983562225206331350⟩, ⟨.privateRow 8 23, 612226852714419742800⟩, ⟨.privateRow 8 24, 995180081032042705800⟩, ⟨.privateRow 8 25, 1268584268733730428480⟩, ⟨.privateRow 8 26, 150340909542520296600⟩, ⟨.privateRow 9 16, 8800967040861441600⟩, ⟨.privateRow 9 17, 36742248581157319200⟩, ⟨.privateRow 9 18, 78794999373814476480⟩, ⟨.privateRow 9 19, 137239274826935465184⟩, ⟨.privateRow 9 20, 214190255863826802560⟩, ⟨.privateRow 9 21, 309192998186751719040⟩, ⟨.privateRow 9 22, 498631513837015278720⟩, ⟨.privateRow 9 23, 130597764577075635840⟩, ⟨.privateRow 10 14, 4903395922765660320⟩, ⟨.privateRow 10 15, 20693005432659584640⟩, ⟨.privateRow 10 16, 46137102015832988160⟩, ⟨.privateRow 10 17, 81382600769863760640⟩, ⟨.privateRow 10 18, 127304914957397233056⟩, ⟨.privateRow 10 19, 184052310192193963520⟩, ⟨.privateRow 10 20, 19812908728573440480⟩, ⟨.privateRow 11 12, 3023096402247121200⟩, ⟨.privateRow 11 13, 13255114994468146800⟩, ⟨.privateRow 11 14, 31447357841126858400⟩, ⟨.privateRow 11 15, 57322558704147336600⟩, ⟨.privateRow 11 16, 56572069737155918400⟩, ⟨.privateRow 12 10, 2124057430974453975⟩, ⟨.privateRow 12 11, 9866589356784560400⟩, ⟨.privateRow 12 12, 25292923509852484200⟩, ⟨.privateRow 12 13, 14757719123395710000⟩, ⟨.privateRow 13 8, 1676675315532016800⟩, ⟨.privateRow 13 9, 8770301650475164800⟩, ⟨.privateRow 13 10, 5408352684459684960⟩, ⟨.privateRow 14 6, 1583526686891349200⟩, ⟨.privateRow 14 7, 2682680504851226880⟩, ⟨.privateRow 15 4, 1050128223938473680⟩, ⟨.hall 5 31, 1574817290113446779400⟩, ⟨.hall 4 32, 9134588089029901417920⟩, ⟨.hall 3 33, 26548476946133954011200⟩, ⟨.hall 2 34, 65398385347263208880640⟩, ⟨.assumptionRow 19, 22260585962828928⟩]
  caps := #[0, 9488662579904017910400, 25378234034540175360, 0, 24056154656087258848, 6669657777619580744, 7192832463415713400, 13297176863942871900, 1822394853746987520, 195820656745817152, 4329218079916966944, 5073371986344996000, 288943219669378560, 88978858444544640, 48180139929725852048, 11441880755758973520, 78986695947119600640, 17423568187439082240, 2992568300848279296] }

theorem case_55_37_19_checked :
    (Witness.linear .conditional case_55_37_19).check 55 37 19 = true := by
  change case_55_37_19.check 55 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_20 : Certificate := {
  objectiveScale := 62707076251019200000
  eta := 76676458325225100080763024000
  rows := #[⟨.count 2, 8076843563844512342895609600⟩, ⟨.count 3, 788270476289010632719401600⟩, ⟨.count 4, 69789551722402852196176320⟩, ⟨.count 5, 5558777244076280621997600⟩, ⟨.count 6, 551739676831392617568000⟩, ⟨.count 7, 128739257927324944099200⟩, ⟨.count 8, 46814275609936343308800⟩, ⟨.count 9, 10533212012235677244480⟩, ⟨.path 5, 976782050750168747884800⟩, ⟨.path 6, 157798524654426303648000⟩, ⟨.privateRow 2 34, 146440905892332123912840000⟩, ⟨.privateRow 2 35, 753124658874850922980320000⟩, ⟨.privateRow 3 31, 53084828385970394918404500⟩, ⟨.privateRow 3 32, 141210873539034548058810000⟩, ⟨.privateRow 3 33, 223949985368202198069564600⟩, ⟨.privateRow 4 28, 9337351094753938758061560⟩, ⟨.privateRow 4 29, 27581098618350096023812608⟩, ⟨.privateRow 4 30, 49570246644554423944496340⟩, ⟨.privateRow 4 31, 80319350193708638248956720⟩, ⟨.privateRow 4 32, 135625198985712737046705960⟩, ⟨.privateRow 5 25, 1098306794192490929346300⟩, ⟨.privateRow 5 26, 4788574928537600879902080⟩, ⟨.privateRow 5 27, 10055608871273472508681680⟩, ⟨.privateRow 5 28, 17479664701695349517171808⟩, ⟨.privateRow 5 29, 28140562650657128138026560⟩, ⟨.privateRow 5 30, 50148538793333327331784800⟩, ⟨.privateRow 5 31, 60662398118419539820057680⟩, ⟨.privateRow 6 22, 57472883003270064330000⟩, ⟨.privateRow 6 23, 648804990348026503992000⟩, ⟨.privateRow 6 24, 1920169021139252849265300⟩, ⟨.privateRow 6 25, 3734095312841032179612000⟩, ⟨.privateRow 6 26, 6475278151701760581180000⟩, ⟨.privateRow 6 27, 10335923279308088369107200⟩, ⟨.privateRow 6 28, 18446496528729559847356800⟩, ⟨.privateRow 6 29, 24366969783173086740871200⟩, ⟨.privateRow 6 30, 24179991337135781464917600⟩, ⟨.privateRow 7 20, 34274737500131965636800⟩, ⟨.privateRow 7 21, 302997039193239779147760⟩, ⟨.privateRow 7 22, 773712722741800110469200⟩, ⟨.privateRow 7 23, 1489122398614727366790300⟩, ⟨.privateRow 7 24, 2560006417202800865442000⟩, ⟨.privateRow 7 25, 4070229574291585955850600⟩, ⟨.privateRow 7 26, 7252158268884629797416720⟩, ⟨.privateRow 7 27, 9925566894664740109791000⟩, ⟨.privateRow 7 28, 10885364040819350184102000⟩, ⟨.privateRow 7 29, 4725420440528864689212600⟩, ⟨.privateRow 8 18, 15239022008442820087500⟩, ⟨.privateRow 8 19, 137250944401858824700800⟩, ⟨.privateRow 8 20, 337062784391541671823360⟩, ⟨.privateRow 8 21, 648410227111236366176400⟩, ⟨.privateRow 8 22, 1109278890038569759809300⟩, ⟨.privateRow 8 23, 1753027427750651998545600⟩, ⟨.privateRow 8 24, 3119732585568414128313000⟩, ⟨.privateRow 8 25, 4424534223584108646972960⟩, ⟨.privateRow 8 26, 4517211859830654501617100⟩, ⟨.privateRow 9 16, 6301921716722200060800⟩, ⟨.privateRow 9 17, 64467158704516506098160⟩, ⟨.privateRow 9 18, 163530776391982181058240⟩, ⟨.privateRow 9 19, 316230431745119999050944⟩, ⟨.privateRow 9 20, 540444803985820674420480⟩, ⟨.privateRow 9 21, 850849459210593039637440⟩, ⟨.privateRow 9 22, 1506918093115558079436480⟩, ⟨.privateRow 9 23, 2213339938941448698020640⟩, ⟨.privateRow 9 24, 477739682599400383466304⟩, ⟨.privateRow 10 14, 2675101463424933903360⟩, ⟨.privateRow 10 15, 32409883114571314598400⟩, ⟨.privateRow 10 16, 89532302104003256578080⟩, ⟨.privateRow 10 17, 177468662994031410543360⟩, ⟨.privateRow 10 18, 304760934220685594940288⟩, ⟨.privateRow 10 19, 479976364656319564313280⟩, ⟨.privateRow 10 20, 845143969370632047796680⟩, ⟨.privateRow 10 21, 348933547135489816019520⟩, ⟨.privateRow 11 12, 1267886631102442631280⟩, ⟨.privateRow 11 13, 17868841806471238182600⟩, ⟨.privateRow 11 14, 55817020919539486252800⟩, ⟨.privateRow 11 15, 116791864672705773150600⟩, ⟨.privateRow 11 16, 204546465591142318207200⟩, ⟨.privateRow 11 17, 324481447821371279559120⟩, ⟨.privateRow 11 18, 93791100787962743365200⟩, ⟨.privateRow 12 10, 718411037540875804125⟩, ⟨.privateRow 12 11, 11188054557969905856240⟩, ⟨.privateRow 12 12, 39902601627984644663400⟩, ⟨.privateRow 12 13, 90895574965171732509600⟩, ⟨.privateRow 12 14, 139275953144591122559700⟩, ⟨.privateRow 13 8, 540921251795482958400⟩, ⟨.privateRow 13 9, 8046203620457809006200⟩, ⟨.privateRow 13 10, 33104380609883557054080⟩, ⟨.privateRow 13 11, 53203468837312859551200⟩, ⟨.privateRow 14 6, 664131092482231854480⟩, ⟨.privateRow 14 7, 7031976273341278459200⟩, ⟨.privateRow 14 8, 22414424371275325088700⟩, ⟨.privateRow 15 5, 6973376471063434472040⟩, ⟨.hall 5 31, 8984448435486192806387250⟩, ⟨.hall 4 32, 34917597820561270065451200⟩, ⟨.hall 3 33, 90061157123784256206396600⟩, ⟨.hall 2 34, 206284430373721071856323840⟩, ⟨.assumptionRow 20, 47580852199932219168⟩]
  caps := #[0, 0, 0, 102535002693874496305560, 22096048006163304721548, 0, 0, 4272271357180380891480, 18577628064129446037180, 3592083930005466400232, 4136699465253799956512, 11823456542314248129200, 436498722458535047311, 10179197599901009524416, 0, 337310329740205855601568, 679235576278955308572960, 187127907920090527790400, 42807957313923624286464] }

theorem case_55_37_20_checked :
    (Witness.linear .conditional case_55_37_20).check 55 37 20 = true := by
  change case_55_37_20.check 55 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_21 : Certificate := {
  objectiveScale := 177273288640448000000
  eta := 162942260643195592421903040000
  rows := #[⟨.count 2, 19690699732628704170200409600⟩, ⟨.count 3, 2269947895725060769995176400⟩, ⟨.count 4, 242815917821232647530679040⟩, ⟨.count 5, 22557725159072003475775200⟩, ⟨.count 6, 1660939954843374096091200⟩, ⟨.count 7, 94525038080517224980800⟩, ⟨.path 6, 469210980071392778419200⟩, ⟨.path 7, 61143977600984887408800⟩, ⟨.privateRow 2 34, 1129290629947939286845617600⟩, ⟨.privateRow 2 35, 2764857363855128830688400000⟩, ⟨.privateRow 3 31, 212510009049642818736522300⟩, ⟨.privateRow 3 32, 538430371079639533028133600⟩, ⟨.privateRow 3 33, 809335191675148544938732200⟩, ⟨.privateRow 4 28, 31888021596462485847272880⟩, ⟨.privateRow 4 29, 99006470135914546617139728⟩, ⟨.privateRow 4 30, 176935510968040161114998220⟩, ⟨.privateRow 4 31, 291375005300495687957065680⟩, ⟨.privateRow 4 32, 500039814571888133079056520⟩, ⟨.privateRow 5 24, 68268083058151329152800⟩, ⟨.privateRow 5 25, 3846662665744476857299020⟩, ⟨.privateRow 5 26, 16285699520068214627202240⟩, ⟨.privateRow 5 27, 34939604909161850260403040⟩, ⟨.privateRow 5 28, 61258706393072111540128512⟩, ⟨.privateRow 5 29, 100684694669149786720084560⟩, ⟨.privateRow 5 30, 185037713354130971183129280⟩, ⟨.privateRow 5 31, 232362123788370874713695280⟩, ⟨.privateRow 6 22, 388903013816985154206720⟩, ⟨.privateRow 6 23, 2259598529353316520969600⟩, ⟨.privateRow 6 24, 6456397690321042599135000⟩, ⟨.privateRow 6 25, 12666355102789308147427200⟩, ⟨.privateRow 6 26, 22303407794712516656184000⟩, ⟨.privateRow 6 27, 36482613626019055247232480⟩, ⟨.privateRow 6 28, 67445302617557620688532600⟩, ⟨.privateRow 6 29, 93523522796092697239932000⟩, ⟨.privateRow 6 30, 98852934466918049353135200⟩, ⟨.privateRow 7 19, 19130067230580866960400⟩, ⟨.privateRow 7 20, 255647262081398858470800⟩, ⟨.privateRow 7 21, 1044164081367999203091480⟩, ⟨.privateRow 7 22, 2564929406327685652455200⟩, ⟨.privateRow 7 23, 4943575094255621833259250⟩, ⟨.privateRow 7 24, 8644218278342809900795200⟩, ⟨.privateRow 7 25, 14126429351711583140434200⟩, ⟨.privateRow 7 26, 26176008581025516394861680⟩, ⟨.privateRow 7 27, 37777100263589567030049900⟩, ⟨.privateRow 7 28, 44555051878095226260592800⟩, ⟨.privateRow 7 29, 30867488774614615950426600⟩, ⟨.privateRow 8 17, 13716045735459667261200⟩, ⟨.privateRow 8 18, 138386087947423891875300⟩, ⟨.privateRow 8 19, 479851278024443846648400⟩, ⟨.privateRow 8 20, 1104224308486042128184800⟩, ⟨.privateRow 8 21, 2112730080936004945214800⟩, ⟨.privateRow 8 22, 3668215966420071855789000⟩, ⟨.privateRow 8 23, 5961215388558333045542400⟩, ⟨.privateRow 8 24, 11057639208487172193492600⟩, ⟨.privateRow 8 25, 16570239175514669539134240⟩, ⟨.privateRow 8 26, 20829881118833977577587200⟩, ⟨.privateRow 8 27, 5743828260938095920992400⟩, ⟨.privateRow 9 15, 8102146121187190712640⟩, ⟨.privateRow 9 16, 75223421913026994425280⟩, ⟨.privateRow 9 17, 239463429803976969951360⟩, ⟨.privateRow 9 18, 535589802545476111130880⟩, ⟨.privateRow 9 19, 1016058227512759698339072⟩, ⟨.privateRow 9 20, 1752627877783812304795520⟩, ⟨.privateRow 9 21, 2828017275663474431016480⟩, ⟨.privateRow 9 22, 5215081386670821755369280⟩, ⟨.privateRow 9 23, 8087046667052250948130080⟩, ⟨.privateRow 9 24, 7031631650956875896117184⟩, ⟨.privateRow 10 13, 5041335364294251998976⟩, ⟨.privateRow 10 14, 44439043876814591484480⟩, ⟨.privateRow 10 15, 136301138826591970566720⟩, ⟨.privateRow 10 16, 301620803329650417893280⟩, ⟨.privateRow 10 17, 568400146342019280132480⟩, ⟨.privateRow 10 18, 973607892229327417302240⟩, ⟨.privateRow 10 19, 1196935229674104982181120⟩, ⟨.privateRow 10 20, 3571972291283545226717640⟩, ⟨.privateRow 10 21, 3494725693605408260718720⟩, ⟨.privateRow 11 11, 3625250040019836753525⟩, ⟨.privateRow 11 12, 29646489216162220562160⟩, ⟨.privateRow 11 13, 91302593600499592311000⟩, ⟨.privateRow 11 14, 202766121896494117222800⟩, ⟨.privateRow 11 15, 381859670882089471371300⟩, ⟨.privateRow 11 16, 650933784963561799299600⟩, ⟨.privateRow 11 17, 1037197463301675368652960⟩, ⟨.privateRow 11 18, 1454157909056845794401600⟩, ⟨.privateRow 12 9, 2978730191612937762000⟩, ⟨.privateRow 12 10, 23209272742984140062250⟩, ⟨.privateRow 12 11, 73594493934116982306480⟩, ⟨.privateRow 12 12, 166383357845808380706000⟩, ⟨.privateRow 12 13, 315775951389859740595200⟩, ⟨.privateRow 12 14, 539580425709619159265400⟩, ⟨.privateRow 12 15, 271299135270055931438400⟩, ⟨.privateRow 13 7, 3000794859698959523200⟩, ⟨.privateRow 13 8, 21844021405161543588000⟩, ⟨.privateRow 13 9, 72159738891823417284450⟩, ⟨.privateRow 13 10, 169244830087021317108480⟩, ⟨.privateRow 13 11, 223773559537550981587200⟩, ⟨.privateRow 14 5, 3695715774576613307520⟩, ⟨.privateRow 14 6, 25356716564456207971040⟩, ⟨.privateRow 14 7, 87773249646194566053600⟩, ⟨.privateRow 14 8, 50469618546561875480820⟩, ⟨.privateRow 15 3, 6144127475233619623752⟩, ⟨.privateRow 15 4, 38805015633054439728960⟩, ⟨.privateRow 15 5, 10240212458722699372920⟩, ⟨.privateRow 16 1, 14628874941032427675600⟩, ⟨.hall 5 31, 41220512365094123082921900⟩, ⟨.hall 4 32, 139922263035986964231578880⟩, ⟨.hall 3 33, 343059164675985396874435200⟩, ⟨.hall 2 34, 762573992926138389873676800⟩, ⟨.assumptionRow 21, 69789258500226689424⟩]
  caps := #[0, 0, 850677640929469439486400, 656327302112751297788760, 203693846424681252523884, 0, 0, 6177551043078678265860, 39526231907746972369660, 3182362278171307433664, 572601918360495263240, 15544456111387149171610, 817377147827772752220, 576115326158410262224, 180143304476230837922180, 7021859971695565284288, 313901819072128469246064, 1630986780875195347684080, 459641621794601437839648] }

theorem case_55_37_21_checked :
    (Witness.linear .conditional case_55_37_21).check 55 37 21 = true := by
  change case_55_37_21.check 55 37 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_22 : Certificate := {
  objectiveScale := 2885835031372293000000
  eta := 22496017404733741432835141270400
  rows := #[⟨.count 2, 946092409844393497248128966400⟩, ⟨.count 3, 44369509356025822431943880400⟩, ⟨.count 4, 4883598282414690221743039680⟩, ⟨.count 5, 470727937852541457745456800⟩, ⟨.count 6, 35163314165952407692857600⟩, ⟨.count 7, 1465138090248016987202400⟩, ⟨.path 2, 574481817296719659095650801920⟩, ⟨.path 6, 6724562797211738917838400⟩, ⟨.path 7, 1626885375062092768022400⟩, ⟨.privateRow 2 35, 71996885754787554751125936000⟩, ⟨.privateRow 3 33, 57726074471249307291527759400⟩, ⟨.privateRow 4 28, 671082083269933380704939280⟩, ⟨.privateRow 4 29, 1553075678424702966774288048⟩, ⟨.privateRow 4 32, 41299165974102078033562530960⟩, ⟨.privateRow 5 25, 77003471914606492798823280⟩, ⟨.privateRow 5 26, 338644243977815126331826560⟩, ⟨.privateRow 5 27, 669177403752610958621576160⟩, ⟨.privateRow 5 28, 1055627807914866959230794336⟩, ⟨.privateRow 5 29, 1833526132496734458391769160⟩, ⟨.privateRow 5 31, 16517924968367850713234508960⟩, ⟨.privateRow 6 21, 38055534811636804862400⟩, ⟨.privateRow 6 22, 7409412627825685906709280⟩, ⟨.privateRow 6 23, 44861132953784520131959200⟩, ⟨.privateRow 6 24, 132438018086347535521759800⟩, ⟨.privateRow 6 25, 255860951801066966520223200⟩, ⟨.privateRow 6 26, 456146325430549288682347200⟩, ⟨.privateRow 6 27, 779453464011945037191676800⟩, ⟨.privateRow 6 28, 1529133228975635729179133400⟩, ⟨.privateRow 6 29, 1567907062006842178733311200⟩, ⟨.privateRow 6 30, 4832653337962352031073744800⟩, ⟨.privateRow 6 31, 6087858070421974584252715200⟩, ⟨.privateRow 7 18, 24150627861231049239600⟩, ⟨.privateRow 7 19, 549426783843006370200900⟩, ⟨.privateRow 7 20, 4947219525512784632112000⟩, ⟨.privateRow 7 21, 20511933263472237820833600⟩, ⟨.privateRow 7 22, 51558907080632597787741600⟩, ⟨.privateRow 7 24, 376719893857852367791082400⟩, ⟨.privateRow 7 25, 198090158225556296710210200⟩, ⟨.privateRow 7 26, 574857394980882665050198800⟩, ⟨.privateRow 7 28, 2625562341964690441471158000⟩, ⟨.privateRow 7 29, 129141457383289497300554400⟩, ⟨.privateRow 8 15, 4439812394690960567280⟩, ⟨.privateRow 8 16, 38055534811636804862400⟩, ⟨.privateRow 8 17, 414951696888424391480400⟩, ⟨.privateRow 8 18, 2691636264281394843913500⟩, ⟨.privateRow 8 19, 9353877476996637376974000⟩, ⟨.privateRow 8 20, 21863856137655635313570360⟩, ⟨.privateRow 8 21, 24256175049661614565906400⟩, ⟨.privateRow 8 22, 57248605946793254664721050⟩, ⟨.privateRow 8 24, 632717664367408790443072800⟩, ⟨.privateRow 8 25, 190521229480978499863119360⟩, ⟨.privateRow 8 26, 269918394535236947687787600⟩, ⟨.privateRow 8 27, 976692129646090960393090800⟩, ⟨.privateRow 9 13, 3329859296018220425460⟩, ⟨.privateRow 9 14, 28414799326022147630592⟩, ⟨.privateRow 9 15, 273999850643784995009280⟩, ⟨.privateRow 9 16, 1487678676251832633159360⟩, ⟨.privateRow 9 17, 4644043764846744753374880⟩, ⟨.privateRow 9 18, 10461812479126336173081600⟩, ⟨.privateRow 9 19, 16478807684134969241516448⟩, ⟨.privateRow 9 20, 24566961917289981805616000⟩, ⟨.privateRow 9 21, 48336237541000487695977360⟩, ⟨.privateRow 9 22, 26098485773820520774633920⟩, ⟨.privateRow 9 23, 422696778848947591768459680⟩, ⟨.privateRow 9 24, 218555980866015101269152192⟩, ⟨.privateRow 9 25, 206091651549159698572570320⟩, ⟨.privateRow 9 26, 234244501943895079529692800⟩, ⟨.privateRow 10 11, 3133985219781854518080⟩, ⟨.privateRow 10 12, 23309015072127542978220⟩, ⟨.privateRow 10 13, 188248045534896728052672⟩, ⟨.privateRow 10 14, 909527281998119636211360⟩, ⟨.privateRow 10 15, 2647494283357255870581120⟩, ⟨.privateRow 10 16, 5842793111413304106540480⟩, ⟨.privateRow 10 17, 10292292369510863133240000⟩, ⟨.privateRow 10 18, 15700952552585112950128992⟩, ⟨.privateRow 10 19, 23359332945934040531315840⟩, ⟨.privateRow 10 20, 51040083289367282681450880⟩, ⟨.privateRow 10 21, 33762870484884173273921280⟩, ⟨.privateRow 10 22, 33218676337077766964388960⟩, ⟨.privateRow 10 23, 584840503428019348069752192⟩, ⟨.privateRow 11 9, 3699843662242467139400⟩, ⟨.privateRow 11 10, 19587407623636590738000⟩, ⟨.privateRow 11 11, 145681344200797143613875⟩, ⟨.privateRow 11 12, 643772797230189282255600⟩, ⟨.privateRow 11 13, 1798124019849839029748400⟩, ⟨.privateRow 11 14, 3918988248390674808426000⟩, ⟨.privateRow 11 15, 7186946313905992418284500⟩, ⟨.privateRow 11 16, 11557638901997786894914800⟩, ⟨.privateRow 11 17, 17015581002653106374100600⟩, ⟨.privateRow 11 18, 28829181816193303950204800⟩, ⟨.privateRow 11 19, 55333936851582777920081550⟩, ⟨.privateRow 11 20, 41899143827612122153502400⟩, ⟨.privateRow 11 21, 38859457984532632365118200⟩, ⟨.privateRow 11 23, 212694762533163829676257500⟩, ⟨.privateRow 12 7, 5508037933263221756400⟩, ⟨.privateRow 12 8, 23256160162666936304800⟩, ⟨.privateRow 12 9, 135432932712001570245600⟩, ⟨.privateRow 12 10, 542885988797256294365175⟩, ⟨.privateRow 12 11, 1486068634394417229876720⟩, ⟨.privateRow 12 12, 3236759148354037527850200⟩, ⟨.privateRow 12 13, 6013506337446531260660400⟩, ⟨.privateRow 12 14, 9968171649723115573644900⟩, ⟨.privateRow 12 15, 15079505669111083926726000⟩, ⟨.privateRow 12 16, 24645715732386285749011800⟩, ⟨.privateRow 12 17, 37384277461487100109966000⟩, ⟨.privateRow 12 18, 67030067628846777164509800⟩, ⟨.privateRow 12 19, 55047331105032638233461600⟩, ⟨.privateRow 12 20, 42506446737314492831098200⟩, ⟨.privateRow 12 23, 58117144246504673825695200⟩, ⟨.privateRow 13 5, 10465272073200121337160⟩, ⟨.privateRow 13 6, 22032151733052887025600⟩, ⟨.privateRow 13 7, 151165041057335085981200⟩, ⟨.privateRow 13 8, 566355900432006566481600⟩, ⟨.privateRow 13 9, 1530546040705517745559650⟩, ⟨.privateRow 13 10, 3362840759521638989674080⟩, ⟨.privateRow 13 11, 6338964798624073495651200⟩, ⟨.privateRow 13 12, 10755079607534893928035200⟩, ⟨.privateRow 13 13, 16796761677486194746141800⟩, ⟨.privateRow 13 14, 28065956923582143586020000⟩, ⟨.privateRow 13 15, 41944810469386086319337280⟩, ⟨.privateRow 13 16, 61838129872531383634463200⟩, ⟨.privateRow 13 17, 104731210272550214281628700⟩, ⟨.privateRow 13 18, 102410162430601187370780000⟩, ⟨.privateRow 13 21, 273300580191621168719933400⟩, ⟨.privateRow 14 4, 54419414780640630953232⟩, ⟨.privateRow 14 5, 200492580770781271932960⟩, ⟨.privateRow 14 6, 755825205286675429906000⟩, ⟨.privateRow 14 7, 2016719488929623382384480⟩, ⟨.privateRow 14 8, 4489601719402852053641640⟩, ⟨.privateRow 14 9, 8598267535341219690610656⟩, ⟨.privateRow 14 10, 3887101055760045068088000⟩, ⟨.privateRow 14 11, 45586725150859728544668960⟩, ⟨.privateRow 14 12, 29431833493863141240539640⟩, ⟨.privateRow 14 13, 61889716264164935747721120⟩, ⟨.privateRow 14 14, 89737614973276400441879568⟩, ⟨.privateRow 14 15, 128308886849466020980842560⟩, ⟨.privateRow 14 16, 204616999575208772384152320⟩, ⟨.privateRow 14 19, 685358109747388106225003808⟩, ⟨.privateRow 15 2, 181398049268802103177440⟩, ⟨.privateRow 15 3, 285701927598363312504468⟩, ⟨.privateRow 15 4, 1303201775010078267564240⟩, ⟨.privateRow 15 5, 3386096919684305925978880⟩, ⟨.privateRow 15 6, 7058518211253681838345680⟩, ⟨.privateRow 15 7, 12975629211759000442911255⟩, ⟨.privateRow 15 8, 18792837904247897889182784⟩, ⟨.privateRow 15 10, 127173986233527874489168320⟩, ⟨.privateRow 15 11, 53331026485027818334167360⟩, ⟨.privateRow 15 12, 122592099842206803183735360⟩, ⟨.privateRow 15 13, 172754432221143682961034984⟩, ⟨.privateRow 15 15, 601402557594554772821905140⟩, ⟨.privateRow 16 1, 1813980492688021031774400⟩, ⟨.privateRow 16 2, 2857019275983633125044680⟩, ⟨.privateRow 16 3, 8520934682758204057150800⟩, ⟨.privateRow 16 4, 17988639885822875231762800⟩, ⟨.privateRow 16 6, 7142548189959082812611700⟩, ⟨.privateRow 16 7, 634893172440807361121040⟩, ⟨.privateRow 16 8, 1360485369516015773830800⟩, ⟨.privateRow 16 9, 1465138090248016987202400⟩, ⟨.privateRow 16 10, 1587232931102018402802600⟩, ⟨.privateRow 16 11, 1731526833929474621239200⟩, ⟨.privateRow 16 12, 1904679517322422083363120⟩, ⟨.privateRow 16 13, 5290776437006728009342000⟩, ⟨.privateRow 16 15, 4081456108548047321492400⟩, ⟨.privateRow 16 16, 17559557916781629590205163800⟩, ⟨.privateRow 17 1, 76187180692896883334524800⟩, ⟨.privateRow 17 2, 48118219384987505263910400⟩, ⟨.privateRow 17 3, 105815528740134560186840000⟩, ⟨.privateRow 17 5, 47616987933060552084078000⟩, ⟨.privateRow 17 12, 16930484598421529629894400⟩, ⟨.privateRow 17 15, 52683435449138194825823899200⟩, ⟨.privateRow 17 16, 78990868942395488641235312640⟩, ⟨.privateRow 18 2, 4964864608487113563966532800⟩, ⟨.privateRow 18 9, 117743824707204274244265600⟩, ⟨.privateRow 18 10, 129518207177924701668692160⟩, ⟨.privateRow 18 11, 287818238173166003708204800⟩, ⟨.privateRow 18 12, 323795517944811754171730400⟩, ⟨.hall 16 3, 1202955484624687631597760⟩, ⟨.hall 14 6, 167058282528185336127840⟩, ⟨.hall 11 11, 96198321370340844270⟩, ⟨.hall 17 11, 1125842953559002527008160⟩, ⟨.hall 13 15, 442429529177891545290⟩, ⟨.hall 15 17, 32909135732577734029400⟩, ⟨.hall 6 19, 33056847537590198784⟩, ⟨.hall 10 19, 490192725527144262896⟩, ⟨.hall 14 20, 258115801331101806892800⟩, ⟨.hall 15 20, 29683317153076707792672000⟩, ⟨.hall 16 20, 602241523572422982549100800⟩, ⟨.hall 4 29, 893132712081687070761768⟩, ⟨.hall 2 33, 331254178911805440649438080⟩, ⟨.hall 3 33, 3426742531606251730568295600⟩]
  caps := #[0, 654962634023966012569144320, 76802788797928807802348160, 7940734034273901218358000, 9605717884675244140112304, 0, 455597653141741494384000, 492931315484704554861700, 45903086262838731940580, 124944733406819559808512, 327428660534792854392684, 184329364297177933024730, 2195021607059702113721545, 347401201203349742780760, 11991384649540451388162072, 2299739758059694032218136, 37429882101667200737812220, 0, 0] }

theorem case_55_37_22_checked :
    (Witness.linear .conditional case_55_37_22).check 55 37 22 = true := by
  change case_55_37_22.check 55 37 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_23 : Certificate := {
  objectiveScale := 219501052232378716800000
  eta := 1647536354406791167576598621280000
  rows := #[⟨.count 2, 65367839162698596932188933152000⟩, ⟨.count 3, 2377725722244618831987184483200⟩, ⟨.count 4, 222078013001725125231806339520⟩, ⟨.count 5, 17376119139458553463366977600⟩, ⟨.count 6, 905455339773274498091083200⟩, ⟨.path 2, 41910750948396238474842095339520⟩, ⟨.path 3, 91259210452340365452085068000⟩, ⟨.path 6, 808569817106903145361267200⟩, ⟨.path 7, 2921979873784759490102400⟩, ⟨.privateRow 2 35, 5689277718242074763005639440000⟩, ⟨.privateRow 3 34, 10489851020496680606134880719200⟩, ⟨.privateRow 4 28, 34560727288401569106304372920⟩, ⟨.privateRow 4 29, 89380514773485836621564459616⟩, ⟨.privateRow 5 25, 3251015838995471293146079680⟩, ⟨.privateRow 5 26, 16767554598168760807507120320⟩, ⟨.privateRow 5 27, 37199842157701053704907153120⟩, ⟨.privateRow 5 28, 65109999975467921622732519936⟩, ⟨.privateRow 6 21, 11759160256795772702481600⟩, ⟨.privateRow 6 22, 241454757272873199490955520⟩, ⟨.privateRow 6 23, 1815701448540058385060955200⟩, ⟨.privateRow 6 24, 6303154880147884080461439300⟩, ⟨.privateRow 6 25, 13587989656733629542781833600⟩, ⟨.privateRow 6 26, 26962447895470840609823366400⟩, ⟨.privateRow 6 27, 51955889734609322390464536000⟩, ⟨.privateRow 7 18, 3316686226275730762238400⟩, ⟨.privateRow 7 19, 16168845353094187465912200⟩, ⟨.privateRow 7 20, 152869083338345045132260800⟩, ⟨.privateRow 7 22, 3910465190952038672311358000⟩, ⟨.privateRow 7 23, 4154045851965781663117276050⟩, ⟨.privateRow 7 24, 9665889741083068068907702800⟩, ⟨.privateRow 7 25, 17866574115169077149832981000⟩, ⟨.privateRow 7 26, 39117826524252537542530249200⟩, ⟨.privateRow 7 27, 29861162559606115218295514700⟩, ⟨.privateRow 7 28, 40878434129367237955485133200⟩, ⟨.privateRow 8 15, 457300676653168938429840⟩, ⟨.privateRow 8 16, 1469895032099471587810200⟩, ⟨.privateRow 8 17, 10553092538150052425304000⟩, ⟨.privateRow 8 18, 80599244260121025398259300⟩, ⟨.privateRow 8 19, 58617632189178927562370400⟩, ⟨.privateRow 8 20, 1221678757678940819015317560⟩, ⟨.privateRow 8 21, 2287265551060266640379916400⟩, ⟨.privateRow 8 22, 3631253185549069601719448250⟩, ⟨.privateRow 8 23, 7375933271075148427631583600⟩, ⟨.privateRow 8 24, 16231887517804231469567170800⟩, ⟨.privateRow 8 25, 30512473048329391078854214320⟩, ⟨.privateRow 8 27, 122000961020915675239004864400⟩, ⟨.privateRow 9 13, 342975507489876703822380⟩, ⟨.privateRow 9 14, 1097521623967605452231616⟩, ⟨.privateRow 9 15, 6663524145517604531406240⟩, ⟨.privateRow 9 16, 43478741257178215992252480⟩, ⟨.privateRow 9 17, 49388473078542245350422720⟩, ⟨.privateRow 9 18, 420550331365768816468751040⟩, ⟨.privateRow 9 19, 1062400932000642077760204288⟩, ⟨.privateRow 9 20, 1826763769670525519381067520⟩, ⟨.privateRow 9 21, 2948903413397959899464823240⟩, ⟨.privateRow 9 22, 6802282236547794649295522880⟩, ⟨.privateRow 9 23, 12800760540875504924528081280⟩, ⟨.privateRow 9 24, 21753976108661907668682860736⟩, ⟨.privateRow 9 26, 63980023069191559837842054720⟩, ⟨.privateRow 10 11, 322800477637531015362240⟩, ⟨.privateRow 10 12, 1028926522469630111467140⟩, ⟨.privateRow 10 13, 4755927037192956959670336⟩, ⟨.privateRow 10 14, 25870152564950699945459520⟩, ⟨.privateRow 10 15, 37991133137340188731094400⟩, ⟨.privateRow 10 16, 170573152391632014034330320⟩, ⟨.privateRow 10 17, 500868959301579942745701120⟩, ⟨.privateRow 10 18, 1004781046742342791518044448⟩, ⟨.privateRow 10 19, 1667623134195222728807483200⟩, ⟨.privateRow 10 20, 3202705288940468660293384440⟩, ⟨.privateRow 10 21, 6521630278418935540796295360⟩, ⟨.privateRow 10 22, 11644704430296293848177445760⟩, ⟨.privateRow 10 24, 18633173370910021565262260640⟩, ⟨.privateRow 10 25, 74536351889053311612556481280⟩, ⟨.privateRow 11 10, 807001194093827538405600⟩, ⟨.privateRow 11 11, 3858474459261112918001775⟩, ⟨.privateRow 11 12, 17834726389473588598763760⟩, ⟨.privateRow 11 13, 32337690706188374931824400⟩, ⟨.privateRow 11 14, 89701286574275445615084000⟩, ⟨.privateRow 11 15, 260661385692306294905008800⟩, ⟨.privateRow 11 16, 588670689218988378924230400⟩, ⟨.privateRow 11 17, 1074885240473273589779338920⟩, ⟨.privateRow 11 18, 2046420528022930999473534000⟩, ⟨.privateRow 11 19, 3567802716663442411512307950⟩, ⟨.privateRow 11 20, 6806593928641953099286432800⟩, ⟨.privateRow 11 22, 29265414103096199383756040640⟩, ⟨.privateRow 12 8, 1197692248377347219697200⟩, ⟨.privateRow 12 9, 3804434200728044109626400⟩, ⟨.privateRow 12 10, 14821441573669671843752850⟩, ⟨.privateRow 12 11, 31619075357161966600006080⟩, ⟨.privateRow 12 12, 66215271446004767717545200⟩, ⟨.privateRow 12 13, 165834311313786538111920000⟩, ⟨.privateRow 12 14, 388052288474260499181892800⟩, ⟨.privateRow 12 15, 777084506969920646088992400⟩, ⟨.privateRow 12 16, 1586702690650309596654850560⟩, ⟨.privateRow 12 17, 2745110633280879827545982400⟩, ⟨.privateRow 12 18, 4589257272719900209074746100⟩, ⟨.privateRow 12 19, 8186055418766542911313262400⟩, ⟨.privateRow 12 20, 3381085217169251201205195600⟩, ⟨.privateRow 12 21, 21183343258600464805340436960⟩, ⟨.privateRow 13 6, 1134655814252223681818400⟩, ⟨.privateRow 13 7, 3593076745132041659091600⟩, ⟨.privateRow 13 8, 15217736802912176438505600⟩, ⟨.privateRow 13 9, 36379902044461921798302450⟩, ⟨.privateRow 13 10, 70424304204588016518195360⟩, ⟨.privateRow 13 11, 144749663161033678266261600⟩, ⟨.privateRow 13 12, 315085191496194422412648000⟩, ⟨.privateRow 13 13, 653939967614031581954671200⟩, ⟨.privateRow 13 14, 1440497131457482156053996000⟩, ⟨.privateRow 13 15, 2681872482566555894345970240⟩, ⟨.privateRow 13 16, 4455415163963731657273584000⟩, ⟨.privateRow 13 18, 26347518475375385480167404000⟩, ⟨.privateRow 13 19, 1875586060958925746045815200⟩, ⟨.privateRow 13 20, 20510719291911746606758489440⟩, ⟨.privateRow 14 4, 2802599861202992494091448⟩, ⟨.privateRow 14 5, 5900210234111563145455680⟩, ⟨.privateRow 14 7, 92320936604333870393600640⟩, ⟨.privateRow 14 8, 77071496183082293587514820⟩, ⟨.privateRow 14 9, 183103190931928842947307936⟩, ⟨.privateRow 14 10, 352326839694090484971496320⟩, ⟨.privateRow 14 11, 694182427159510448536497120⟩, ⟨.privateRow 14 12, 1574126922042347450848029960⟩, ⟨.privateRow 14 13, 677719602799996366753022880⟩, ⟨.privateRow 14 14, 10683510670905807387476599776⟩, ⟨.privateRow 14 15, 6632819671513748902683093600⟩, ⟨.privateRow 14 16, 2732534864672917681739161800⟩, ⟨.privateRow 14 17, 36946273598830306764965545920⟩, ⟨.privateRow 14 18, 28595860583807866748046407760⟩, ⟨.privateRow 14 20, 58616376097060588013922634920⟩, ⟨.privateRow 15 3, 19618199028420947458640136⟩, ⟨.privateRow 15 4, 10325367909695235504547440⟩, ⟨.privateRow 15 5, 87191995681870877593956160⟩, ⟨.privateRow 15 6, 265422692737459877381601840⟩, ⟨.privateRow 15 7, 294272985426314211879602040⟩, ⟨.privateRow 15 8, 588545970852628423759204080⟩, ⟨.privateRow 15 9, 1050974947951122185284293000⟩, ⟨.privateRow 15 11, 9236902042548196095109730700⟩, ⟨.privateRow 15 13, 27073114659220907492923387680⟩, ⟨.privateRow 15 15, 58045346375340478293251502390⟩, ⟨.privateRow 15 16, 45121857765368179154872312800⟩, ⟨.privateRow 15 17, 98090995142104737293200680000⟩, ⟨.privateRow 16 1, 46709997686716541568190800⟩, ⟨.privateRow 16 2, 49045497571052368646600340⟩, ⟨.privateRow 16 3, 154880518645428532568211600⟩, ⟨.privateRow 16 4, 544949973011692984962226000⟩, ⟨.privateRow 16 5, 1154011707554173379920008000⟩, ⟨.privateRow 16 6, 1348751183203940137781509350⟩, ⟨.privateRow 16 7, 2550365873694723169623217680⟩, ⟨.privateRow 16 8, 4904549757105236864660034000⟩, ⟨.privateRow 16 10, 36947608170192784380438922800⟩, ⟨.privateRow 16 12, 102308907933215240996808309240⟩, ⟨.privateRow 16 19, 1524661034492114633327315902800⟩, ⟨.privateRow 17 16, 4651867353619175061392749048320⟩, ⟨.privateRow 17 19, 10323096328755102552736439563200⟩, ⟨.privateRow 18 11, 14822639265918049190972547200⟩, ⟨.privateRow 18 12, 16675469174157805339844115600⟩, ⟨.privateRow 18 13, 38115358112360697919643692800⟩, ⟨.privateRow 18 17, 104366203071328984353637704835200⟩, ⟨.hall 17 5, 258134197742380887613686000⟩, ⟨.hall 16 6, 11713652670662662127007600⟩, ⟨.hall 15 11, 3879521717847676559158500⟩, ⟨.hall 17 14, 5228077951609020910469187120⟩, ⟨.hall 8 17, 5285118023938183993408⟩, ⟨.hall 11 17, 16000406404687787887728⟩, ⟨.hall 14 17, 8718163079784081775531680⟩, ⟨.hall 9 18, 6726581139357553699008⟩, ⟨.hall 6 19, 4577642182150964715360⟩, ⟨.hall 12 19, 492521349886083813190896⟩, ⟨.hall 16 19, 16479287183873595865257714240⟩, ⟨.hall 7 20, 10804984492548198651776⟩, ⟨.hall 13 22, 211210424322544361873558400⟩, ⟨.hall 4 32, 1757552836594657244446172668800⟩, ⟨.hall 3 33, 2936325089286216456537464355600⟩]
  caps := #[0, 0, 232317666822183699294457920, 25204324732163723763817200, 464969747225458832962412808, 0, 0, 4416100038461508333792240, 51392207936377175703779650, 15665264936696201117334680, 12647431924115862016987704, 26535819167233400417872906, 277143079934037752146005250, 48655042482030279909033420, 287538947775455931951232980, 22420798889623939952731584, 1564441552315010069940289050, 167247116923064493928507614720, 0] }

theorem case_55_37_23_checked :
    (Witness.linear .conditional case_55_37_23).check 55 37 23 = true := by
  change case_55_37_23.check 55 37 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_37_24 : Certificate := {
  objectiveScale := 13
  eta := 797355
  rows := #[⟨.assumptionRow 24, 5⟩]
  caps := #[0, 0, 416520, 161460, 93610, 46046, 20020, 11305, 5130, 2601, 1428, 580, 364, 29716, 1069776, 1051688, 739670, 436050, 224808] }

theorem case_55_37_24_checked :
    (Witness.linear .conditional case_55_37_24).check 55 37 24 = true := by
  change case_55_37_24.check 55 37 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_38_1_checked :
    (Witness.rising).check 55 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_38_2_checked :
    (Witness.rising).check 55 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_38_3_checked :
    (Witness.rising).check 55 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_38_4_checked :
    (Witness.rising).check 55 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_38_5_checked :
    (Witness.rising).check 55 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_38_6_checked :
    (Witness.rising).check 55 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_38_7_checked :
    (Witness.rising).check 55 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_38_8_checked :
    (Witness.rising).check 55 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_38_9_checked :
    (Witness.rising).check 55 38 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_38_10_checked :
    (Witness.rising).check 55 38 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_38_11_checked :
    (Witness.linear .positive case_55_38_11).check 55 38 11 = true := by
  change case_55_38_11.check 55 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_55_38_12_checked :
    (Witness.linear .positive case_55_38_12).check 55 38 12 = true := by
  change case_55_38_12.check 55 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_55_38_13_checked :
    (Witness.linear .positive case_55_38_13).check 55 38 13 = true := by
  change case_55_38_13.check 55 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_55_38_14_checked :
    (Witness.linear .positive case_55_38_14).check 55 38 14 = true := by
  change case_55_38_14.check 55 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_55_38_15_checked :
    (Witness.linear .positive case_55_38_15).check 55 38 15 = true := by
  change case_55_38_15.check 55 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_55_38_16_checked :
    (Witness.linear .positive case_55_38_16).check 55 38 16 = true := by
  change case_55_38_16.check 55 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_55_38_17_checked :
    (Witness.linear .positive case_55_38_17).check 55 38 17 = true := by
  change case_55_38_17.check 55 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_18 : Certificate := {
  objectiveScale := 2
  eta := 61780875
  rows := #[⟨.assumptionRow 18, 5⟩]
  caps := #[0, 0, 17206875, 4828850, 1366936, 390830, 113050, 33592, 10166, 3146, 1001, 330, 32890, 45540, 20746, 6578, 1573, 278] }

theorem case_55_38_18_checked :
    (Witness.linear .conditional case_55_38_18).check 55 38 18 = true := by
  change case_55_38_18.check 55 38 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_19 : Certificate := {
  objectiveScale := 2869284698280000
  eta := 5955165343770950225318400
  rows := #[⟨.count 2, 647540008822787723042400⟩, ⟨.count 3, 69386228058950040157920⟩, ⟨.count 4, 6830336975791000351680⟩, ⟨.count 5, 669222092687465116800⟩, ⟨.count 6, 17798459911900668000⟩, ⟨.count 7, 9061034136967612800⟩, ⟨.count 8, 3624413654787045120⟩, ⟨.count 9, 1812206827393522560⟩, ⟨.path 6, 22570895717719148800⟩, ⟨.privateRow 2 35, 15953649542032163761800⟩, ⟨.privateRow 2 36, 57821856715791700131600⟩, ⟨.privateRow 3 32, 6392257549159418576640⟩, ⟨.privateRow 3 33, 12467781616153280376960⟩, ⟨.privateRow 3 34, 17341158148564233503520⟩, ⟨.privateRow 4 28, 254517976740179552400⟩, ⟨.privateRow 4 29, 1077459434866760105160⟩, ⟨.privateRow 4 30, 2950557490355245138368⟩, ⟨.privateRow 4 31, 4371924700459720584180⟩, ⟨.privateRow 4 32, 6261142227808416989040⟩, ⟨.privateRow 4 33, 9440303137272114307200⟩, ⟨.privateRow 5 25, 66605792203646055360⟩, ⟨.privateRow 5 26, 201478566202715561760⟩, ⟨.privateRow 5 27, 582975841228655022720⟩, ⟨.privateRow 5 28, 1071229973897594871360⟩, ⟨.privateRow 5 29, 1596165884899251906240⟩, ⟨.privateRow 5 30, 2227299273375249593520⟩, ⟨.privateRow 5 31, 3479480256377167922880⟩, ⟨.privateRow 5 32, 3430831132617972763680⟩, ⟨.privateRow 6 3, 296640998531677800⟩, ⟨.privateRow 6 22, 8413817412898497600⟩, ⟨.privateRow 6 23, 37554750414110409480⟩, ⟨.privateRow 6 24, 116876553421481053200⟩, ⟨.privateRow 6 25, 247621073524318043550⟩, ⟨.privateRow 6 26, 413432797382149802400⟩, ⟨.privateRow 6 27, 618298721272860427800⟩, ⟨.privateRow 6 28, 849461163395312548080⟩, ⟨.privateRow 6 29, 1307593521527635742400⟩, ⟨.privateRow 6 30, 1389664197788066600400⟩, ⟨.privateRow 6 31, 719947703436382020600⟩, ⟨.privateRow 7 15, 76143144008131200⟩, ⟨.privateRow 7 20, 5042896975038522600⟩, ⟨.privateRow 7 21, 23446896776503855200⟩, ⟨.privateRow 7 22, 57828814295575443120⟩, ⟨.privateRow 7 23, 109559408791033000800⟩, ⟨.privateRow 7 24, 177094676123411646600⟩, ⟨.privateRow 7 25, 261013258863873172800⟩, ⟨.privateRow 7 26, 356238871873042158000⟩, ⟨.privateRow 7 27, 542755944804360006720⟩, ⟨.privateRow 7 28, 517611575074274881200⟩, ⟨.privateRow 8 18, 3275912341826752320⟩, ⟨.privateRow 8 19, 13685936977711498500⟩, ⟨.privateRow 8 20, 30292684580634905520⟩, ⟨.privateRow 8 21, 54320899651120838736⟩, ⟨.privateRow 8 22, 85979146144114903680⟩, ⟨.privateRow 8 23, 124985639626797009060⟩, ⟨.privateRow 8 24, 169182451671666713280⟩, ⟨.privateRow 8 25, 243666309666620720880⟩, ⟨.privateRow 9 16, 2200536861834991680⟩, ⟨.privateRow 9 17, 8580876772444542720⟩, ⟨.privateRow 9 18, 18054949502550280320⟩, ⟨.privateRow 9 19, 31374974769217148160⟩, ⟨.privateRow 9 20, 48869177445378658368⟩, ⟨.privateRow 9 21, 70340472411422653440⟩, ⟨.privateRow 9 22, 70273353640037708160⟩, ⟨.privateRow 10 14, 1630986144654170304⟩, ⟨.privateRow 10 15, 6116198042453138640⟩, ⟨.privateRow 10 16, 12755148054346716480⟩, ⟨.privateRow 10 17, 21840867700982350020⟩, ⟨.privateRow 10 18, 33649385863193362080⟩, ⟨.privateRow 10 19, 7135564382861995080⟩, ⟨.privateRow 11 12, 1375335538646869800⟩, ⟨.privateRow 11 13, 5134586010948313920⟩, ⟨.privateRow 11 14, 10956454543170021600⟩, ⟨.privateRow 11 15, 9608679057333787200⟩, ⟨.privateRow 12 10, 1361058699145345200⟩, ⟨.privateRow 12 11, 5228297599120821225⟩, ⟨.privateRow 12 12, 1898502390602737920⟩, ⟨.privateRow 13 8, 1661189591777395680⟩, ⟨.privateRow 13 9, 921332042498387520⟩, ⟨.privateRow 14 6, 730673617435922160⟩, ⟨.hall 4 33, 1175410292581920114720⟩, ⟨.hall 3 34, 4575770461830718934784⟩, ⟨.hall 2 35, 13029263698174040116800⟩, ⟨.assumptionRow 19, 3009213047000160⟩]
  caps := #[0, 1588261647301051923200, 0, 24449183161917906392, 25166221918623533748, 1386580181625839200, 1788741930450320560, 0, 197011119387672072, 0, 385663744389924000, 1160308319286481200, 6514243455490165395, 12176780536720800, 3009213047000160, 49823779584205186560, 12631059254043790560, 2644857596190569760] }

theorem case_55_38_19_checked :
    (Witness.linear .conditional case_55_38_19).check 55 38 19 = true := by
  change case_55_38_19.check 55 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_20 : Certificate := {
  objectiveScale := 250433181999000000
  eta := 476506519909150236566860800
  rows := #[⟨.count 2, 50839395116569690643812800⟩, ⟨.count 3, 5268731903035878337220160⟩, ⟨.count 4, 494826137712295262153280⟩, ⟨.count 5, 40141459921306639896000⟩, ⟨.count 6, 3541893522468232932000⟩, ⟨.count 7, 751310747190231228000⟩, ⟨.count 8, 360629158651310989440⟩, ⟨.count 9, 120209719550436996480⟩, ⟨.path 5, 2379456329555431526400⟩, ⟨.path 6, 1405505479660169888000⟩, ⟨.privateRow 2 35, 1901642632213194261190800⟩, ⟨.privateRow 2 36, 5533027997682457878606000⟩, ⟨.privateRow 3 32, 541842806504437460862840⟩, ⟨.privateRow 3 33, 1154594321328688945024320⟩, ⟨.privateRow 3 34, 1737621478624937581035360⟩, ⟨.privateRow 3 35, 2958110761220524406296800⟩, ⟨.privateRow 4 28, 13331012572185196711680⟩, ⟨.privateRow 4 29, 82982629794183510671280⟩, ⟨.privateRow 4 30, 247720032961428211264080⟩, ⟨.privateRow 4 31, 396367400943549167031900⟩, ⟨.privateRow 4 32, 602979824139486348194640⟩, ⟨.privateRow 4 33, 975224962476403255496880⟩, ⟨.privateRow 5 25, 2791536820671259140480⟩, ⟨.privateRow 5 26, 12986942915716854084000⟩, ⟨.privateRow 5 27, 44391732148268519414400⟩, ⟨.privateRow 5 28, 89523326499008180819040⟩, ⟨.privateRow 5 29, 143621421073738533237312⟩, ⟨.privateRow 5 30, 215536027153933534688640⟩, ⟨.privateRow 5 31, 361745391761422190121600⟩, ⟨.privateRow 5 32, 396975425998239547018560⟩, ⟨.privateRow 6 22, 157417489887477019200⟩, ⟨.privateRow 6 23, 1826042882694733422720⟩, ⟨.privateRow 6 24, 7556039514598896921600⟩, ⟨.privateRow 6 25, 18668730441342977745750⟩, ⟨.privateRow 6 26, 34125862986320910948000⟩, ⟨.privateRow 6 27, 55233861764268499111800⟩, ⟨.privateRow 6 28, 82132575348791134767600⟩, ⟨.privateRow 6 29, 137376275706177601193100⟩, ⟨.privateRow 6 30, 164107733207694792516000⟩, ⟨.privateRow 6 31, 134847757274860001572200⟩, ⟨.privateRow 7 20, 41143207584226948200⟩, ⟨.privateRow 7 21, 1141602044431909788000⟩, ⟨.privateRow 7 22, 3698595478310766873840⟩, ⟨.privateRow 7 23, 8066453799991625438400⟩, ⟨.privateRow 7 24, 14333935755322197214200⟩, ⟨.privateRow 7 25, 22987042289542748102400⟩, ⟨.privateRow 7 26, 34091619571312920817200⟩, ⟨.privateRow 7 27, 56842024530278065478400⟩, ⟨.privateRow 7 28, 71014965125488070286600⟩, ⟨.privateRow 7 29, 39454547238161285630400⟩, ⟨.privateRow 8 19, 654892534634151553740⟩, ⟨.privateRow 8 20, 1875544828894886320080⟩, ⟨.privateRow 8 21, 3863239862052168974376⟩, ⟨.privateRow 8 22, 6758457565835680024320⟩, ⟨.privateRow 8 23, 10723082639272575201630⟩, ⟨.privateRow 8 24, 14923178041332821420160⟩, ⟨.privateRow 8 25, 28106535052386550239480⟩, ⟨.privateRow 8 26, 27981817468352971855632⟩, ⟨.privateRow 9 17, 372958360656484014720⟩, ⟨.privateRow 9 18, 1064078628613127487360⟩, ⟨.privateRow 9 19, 2133418962122402048640⟩, ⟨.privateRow 9 20, 3686431399546734558720⟩, ⟨.privateRow 9 21, 5801232021267385422720⟩, ⟨.privateRow 9 22, 8503168078755216987120⟩, ⟨.privateRow 9 23, 13410062047626527162880⟩, ⟨.privateRow 10 15, 232906331628971680680⟩, ⟨.privateRow 10 16, 698141063542922556480⟩, ⟨.privateRow 10 17, 1402446728088431625600⟩, ⟨.privateRow 10 18, 2406926430089431679520⟩, ⟨.privateRow 10 19, 3768574707906199839648⟩, ⟨.privateRow 10 20, 4052069296512647089680⟩, ⟨.privateRow 11 13, 164572830336907792800⟩, ⟨.privateRow 11 14, 539717108185635494400⟩, ⟨.privateRow 11 15, 1122838039756829088000⟩, ⟨.privateRow 11 16, 1940886096908097339000⟩, ⟨.privateRow 11 17, 614708793155643732000⟩, ⟨.privateRow 12 11, 135280655372050563375⟩, ⟨.privateRow 12 12, 498488717977010560800⟩, ⟨.privateRow 12 13, 860174141170856569200⟩, ⟨.privateRow 13 9, 133341873787039357440⟩, ⟨.privateRow 13 10, 360092508117603681420⟩, ⟨.privateRow 14 7, 153482052640290093720⟩, ⟨.privateRow 15 5, 75394692525054782880⟩, ⟨.hall 5 32, 10532661141562098739200⟩, ⟨.hall 4 33, 156226672875739987160640⟩, ⟨.hall 3 34, 476653862679684915056832⟩, ⟨.assumptionRow 20, 207411265663391790⟩]
  caps := #[0, 99963536105537869564800, 0, 0, 0, 748308883868743124928, 87964532440430209850, 0, 119849364574919231616, 253145604049395392160, 36889331113803077910, 11796179215017096900, 10922693617657525275, 113102555802717040560, 1482990073670205500400, 0, 3565188629232893412750, 933465844662346195200] }

theorem case_55_38_20_checked :
    (Witness.linear .conditional case_55_38_20).check 55 38 20 = true := by
  change case_55_38_20.check 55 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_21 : Certificate := {
  objectiveScale := 6406696296000000
  eta := 12643712668519785095443200
  rows := #[⟨.count 2, 1394527132557329238468000⟩, ⟨.count 3, 148296056047559889749280⟩, ⟨.count 4, 14030881917749534597760⟩, ⟨.count 5, 1089265746608320881600⟩, ⟨.count 6, 56955071718082137600⟩, ⟨.count 7, 2265258534241903200⟩, ⟨.path 6, 48876206023489644800⟩, ⟨.privateRow 2 35, 65110326049715023677600⟩, ⟨.privateRow 2 36, 171198046354598955291600⟩, ⟨.privateRow 3 32, 15748492627447655395320⟩, ⟨.privateRow 3 33, 35092630126297483740000⟩, ⟨.privateRow 3 34, 53653932030022214370480⟩, ⟨.privateRow 3 35, 93940271415011725704000⟩, ⟨.privateRow 4 28, 358969510051733758320⟩, ⟨.privateRow 4 29, 2315342321739451564560⟩, ⟨.privateRow 4 30, 7133907508048378145088⟩, ⟨.privateRow 4 31, 11823516919475613752400⟩, ⟨.privateRow 4 32, 18578269768840742600640⟩, ⟨.privateRow 4 33, 31060448361456093740160⟩, ⟨.privateRow 5 25, 91286323281481648320⟩, ⟨.privateRow 5 26, 349027798872372099480⟩, ⟨.privateRow 5 27, 1222296521264127017280⟩, ⟨.privateRow 5 28, 2545891705798271550720⟩, ⟨.privateRow 5 29, 4224642444688742556480⟩, ⟨.privateRow 5 30, 6593261489764483453920⟩, ⟨.privateRow 5 31, 11561879558770673932800⟩, ⟨.privateRow 5 32, 13450652124621572820960⟩, ⟨.privateRow 6 22, 13052203935393823200⟩, ⟨.privateRow 6 23, 52861425938344983960⟩, ⟨.privateRow 6 24, 199540511678975266800⟩, ⟨.privateRow 6 25, 505179620499447293400⟩, ⟨.privateRow 6 26, 953234660138794347600⟩, ⟨.privateRow 6 27, 1599982665747026160600⟩, ⟨.privateRow 6 28, 2483953065304857226080⟩, ⟨.privateRow 6 29, 4372784959355462449800⟩, ⟨.privateRow 6 30, 5599197727618262367600⟩, ⟨.privateRow 6 31, 5127736300618582450800⟩, ⟨.privateRow 7 19, 970825086103672800⟩, ⟨.privateRow 7 20, 6687906148714190400⟩, ⟨.privateRow 7 21, 31831295247399211200⟩, ⟨.privateRow 7 22, 95788075162229049600⟩, ⟨.privateRow 7 23, 213905127304842573600⟩, ⟨.privateRow 7 24, 392132432695375171800⟩, ⟨.privateRow 7 25, 653550202011791541600⟩, ⟨.privateRow 7 26, 1014512214978338076000⟩, ⟨.privateRow 7 27, 1788195086930558386080⟩, ⟨.privateRow 7 28, 2405300052912358001400⟩, ⟨.privateRow 7 29, 2308406315846510880000⟩, ⟨.privateRow 8 17, 404510452543197000⟩, ⟨.privateRow 8 18, 4373691477651674640⟩, ⟨.privateRow 8 19, 17876665266059019420⟩, ⟨.privateRow 8 20, 47941107888319551360⟩, ⟨.privateRow 8 21, 100282995310889054664⟩, ⟨.privateRow 8 22, 180817970111042584320⟩, ⟨.privateRow 8 23, 298108023106234461120⟩, ⟨.privateRow 8 24, 460041647468327084160⟩, ⟨.privateRow 8 25, 811717641436681980000⟩, ⟨.privateRow 8 26, 1143185371890518868912⟩, ⟨.privateRow 8 27, 490428472663372042800⟩, ⟨.privateRow 9 15, 214780068431824896⟩, ⟨.privateRow 9 16, 2962814336849727360⟩, ⟨.privateRow 9 17, 10873240964361135360⟩, ⟨.privateRow 9 18, 27048864868132947840⟩, ⟨.privateRow 9 19, 54402815060742919680⟩, ⟨.privateRow 9 20, 96429538848750883776⟩, ⟨.privateRow 9 21, 157214535507336827520⟩, ⟨.privateRow 9 22, 240570456336490119840⟩, ⟨.privateRow 9 23, 421553826277017033600⟩, ⟨.privateRow 9 24, 364186453534713089280⟩, ⟨.privateRow 10 13, 155736524229130845⟩, ⟨.privateRow 10 14, 2235055087118677824⟩, ⟨.privateRow 10 15, 7620976925913831480⟩, ⟨.privateRow 10 16, 18069793076991181680⟩, ⟨.privateRow 10 17, 35413541751981753360⟩, ⟨.privateRow 10 18, 61738591687792961760⟩, ⟨.privateRow 10 19, 99490154823904388544⟩, ⟨.privateRow 10 20, 151017235616126880000⟩, ⟨.privateRow 10 21, 139851398757759498810⟩, ⟨.privateRow 11 11, 152286288016262400⟩, ⟨.privateRow 11 12, 1941650172207345600⟩, ⟨.privateRow 11 13, 6407445568284240480⟩, ⟨.privateRow 11 14, 14816640004582244400⟩, ⟨.privateRow 11 15, 28527321760892539200⟩, ⟨.privateRow 11 16, 49134536302246995600⟩, ⟨.privateRow 11 17, 78401480438372364000⟩, ⟨.privateRow 11 18, 6601610585504975040⟩, ⟨.privateRow 12 9, 164800554739821000⟩, ⟨.privateRow 12 10, 2024138578216154400⟩, ⟨.privateRow 12 11, 6637342342146290775⟩, ⟨.privateRow 12 12, 15227571257959460400⟩, ⟨.privateRow 12 13, 29197949712618000600⟩, ⟨.privateRow 12 14, 13234752242182548000⟩, ⟨.privateRow 13 7, 224822651518745280⟩, ⟨.privateRow 13 8, 2531336520803650560⟩, ⟨.privateRow 13 9, 8627018216121264960⟩, ⟨.privateRow 13 10, 11746983541854440880⟩, ⟨.privateRow 14 5, 462759957709417368⟩, ⟨.privateRow 14 6, 4140483832136892240⟩, ⟨.privateRow 14 7, 3342155250123569880⟩, ⟨.privateRow 15 3, 1028355461576483040⟩, ⟨.privateRow 15 4, 1079773234655307192⟩, ⟨.hall 5 32, 864034326632268792000⟩, ⟨.hall 4 33, 5765444649579682267200⟩, ⟨.hall 3 34, 15970771660467412204416⟩, ⟨.assumptionRow 21, 3352872431178270⟩]
  caps := #[0, 481137438613203672300, 97283316282504852500, 0, 37760953698584748060, 0, 0, 0, 596902684272394500, 2391258216739665546, 1634391219794812227, 35147358028012230, 0, 16827730660080890550, 0, 79917924926785533588, 245540609706004482870, 76418164428609153150] }

theorem case_55_38_21_checked :
    (Witness.linear .conditional case_55_38_21).check 55 38 21 = true := by
  change case_55_38_21.check 55 38 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_22 : Certificate := {
  objectiveScale := 591019228800000
  eta := 1910766716046031606963200
  rows := #[⟨.count 2, 209691962170060656686400⟩, ⟨.count 3, 22070564916354479004480⟩, ⟨.count 4, 2046427368537201249600⟩, ⟨.count 5, 153462276573721315200⟩, ⟨.count 6, 7514905296135837600⟩, ⟨.path 6, 7421855407699532800⟩, ⟨.privateRow 2 36, 46934143266350685945600⟩, ⟨.privateRow 3 32, 2336509304990234173800⟩, ⟨.privateRow 4 28, 61995143540753691840⟩, ⟨.privateRow 4 29, 337471983974015850960⟩, ⟨.privateRow 4 30, 1045940339969440899984⟩, ⟨.privateRow 4 31, 1361285542261869424200⟩, ⟨.privateRow 4 33, 7138586525398551142920⟩, ⟨.privateRow 5 25, 17807249274820125120⟩, ⟨.privateRow 5 26, 52683441339225977280⟩, ⟨.privateRow 5 27, 176764133296476348480⟩, ⟨.privateRow 5 28, 369548763948574610400⟩, ⟨.privateRow 5 29, 591510061498793044608⟩, ⟨.privateRow 5 30, 936752721229900935360⟩, ⟨.privateRow 5 31, 1185614742931409831040⟩, ⟨.privateRow 5 32, 2856217742395544086560⟩, ⟨.privateRow 5 33, 3122878224008953650240⟩, ⟨.privateRow 6 21, 87893629194571200⟩, ⟨.privateRow 6 23, 15491252145543174000⟩, ⟨.privateRow 6 24, 26477955794864574000⟩, ⟨.privateRow 6 25, 72330963475307436900⟩, ⟨.privateRow 6 27, 501938542922897480400⟩, ⟨.privateRow 6 28, 221360105126527567200⟩, ⟨.privateRow 6 29, 641832240489706866600⟩, ⟨.privateRow 6 30, 585173809770156406800⟩, ⟨.privateRow 6 31, 1116886319582714881200⟩, ⟨.privateRow 7 17, 4794197956067520⟩, ⟨.privateRow 7 18, 46229766004936800⟩, ⟨.privateRow 7 19, 143825938682025600⟩, ⟨.privateRow 7 20, 416495947433365800⟩, ⟨.privateRow 7 21, 8289604102218566400⟩, ⟨.privateRow 7 22, 12958717075250506560⟩, ⟨.privateRow 7 23, 30151509978701311200⟩, ⟨.privateRow 7 24, 30715827029780092200⟩, ⟨.privateRow 7 25, 80773674491959020000⟩, ⟨.privateRow 7 26, 246499680658656625200⟩, ⟨.privateRow 7 28, 485996835927732129000⟩, ⟨.privateRow 7 29, 774682462226060388000⟩, ⟨.privateRow 8 14, 1480561133491440⟩, ⟨.privateRow 8 15, 11011673430342585⟩, ⟨.privateRow 8 16, 38593293546343536⟩, ⟨.privateRow 8 17, 98880332843892600⟩, ⟨.privateRow 8 18, 350437431365627760⟩, ⟨.privateRow 8 19, 4469690681916199740⟩, ⟨.privateRow 8 20, 6928487718873215040⟩, ⟨.privateRow 8 21, 13928823031660769232⟩, ⟨.privateRow 8 22, 20342580960587165280⟩, ⟨.privateRow 8 23, 30864147529045931100⟩, ⟨.privateRow 8 24, 59705742795375877200⟩, ⟨.privateRow 8 25, 179513348992247710440⟩, ⟨.privateRow 8 26, 43905744301461954912⟩, ⟨.privateRow 8 27, 238305197802248216640⟩, ⟨.privateRow 9 11, 1177522304999040⟩, ⟨.privateRow 9 12, 3728820632496960⟩, ⟨.privateRow 9 13, 10528434727050240⟩, ⟨.privateRow 9 14, 26567847006540840⟩, ⟨.privateRow 9 15, 82034053914933120⟩, ⟨.privateRow 9 16, 257288623642290240⟩, ⟨.privateRow 9 17, 2605585125046337280⟩, ⟨.privateRow 9 18, 4323567523380225120⟩, ⟨.privateRow 9 20, 27456052081201615872⟩, ⟨.privateRow 9 21, 10303974347799932800⟩, ⟨.privateRow 9 22, 26514711312527758320⟩, ⟨.privateRow 9 23, 56239138156642721280⟩, ⟨.privateRow 9 24, 133335168176826295680⟩, ⟨.privateRow 9 25, 6470249561508724992⟩, ⟨.privateRow 10 9, 1258476963467724⟩, ⟨.privateRow 10 10, 3974137779371760⟩, ⟨.privateRow 10 11, 9788154160304520⟩, ⟨.privateRow 10 12, 26650100402845920⟩, ⟨.privateRow 10 13, 72362425399394130⟩, ⟨.privateRow 10 14, 208068191293330368⟩, ⟨.privateRow 10 15, 1713326494549629960⟩, ⟨.privateRow 10 16, 3206212079234693760⟩, ⟨.privateRow 10 17, 2349156998473084800⟩, ⟨.privateRow 10 18, 7322047787448576000⟩, ⟨.privateRow 10 19, 22858975564427738736⟩, ⟨.privateRow 10 20, 10876037579835508080⟩, ⟨.privateRow 10 21, 29618255335212884340⟩, ⟨.privateRow 10 22, 53549992619785181520⟩, ⟨.privateRow 10 23, 5373696634007181480⟩, ⟨.privateRow 11 7, 1712213555738400⟩, ⟨.privateRow 11 8, 3595648467050640⟩, ⟨.privateRow 11 9, 11354679369633600⟩, ⟨.privateRow 11 10, 29963737225422000⟩, ⟨.privateRow 11 11, 76143144008131200⟩, ⟨.privateRow 11 12, 197760665687785200⟩, ⟨.privateRow 11 13, 1313610239962500480⟩, ⟨.privateRow 11 14, 2822584046634752400⟩, ⟨.privateRow 11 15, 3332889540612324000⟩, ⟨.privateRow 11 16, 4197919585281622200⟩, ⟨.privateRow 11 17, 10786945401151920000⟩, ⟨.privateRow 11 18, 26496333553696166160⟩, ⟨.privateRow 11 19, 14538405301774754400⟩, ⟨.privateRow 12 5, 2996373722542200⟩, ⟨.privateRow 12 6, 6278116371040800⟩, ⟨.privateRow 12 7, 16480055473982100⟩, ⟨.privateRow 12 8, 41633824355323200⟩, ⟨.privateRow 12 9, 98880332843892600⟩, ⟨.privateRow 12 10, 236537266803037200⟩, ⟨.privateRow 12 11, 1227764132811666450⟩, ⟨.privateRow 12 12, 2979594029695963680⟩, ⟨.privateRow 12 13, 4506118025314534200⟩, ⟨.privateRow 12 14, 5339537973570200400⟩, ⟨.privateRow 12 16, 31515858813698859600⟩, ⟨.privateRow 12 17, 37165821104924431920⟩, ⟨.privateRow 13 3, 13757263700019840⟩, ⟨.privateRow 13 4, 7191296934101280⟩, ⟨.privateRow 13 5, 37668698226244800⟩, ⟨.privateRow 13 6, 71193839647602672⟩, ⟨.privateRow 13 7, 166535297421292800⟩, ⟨.privateRow 13 8, 360363879697741920⟩, ⟨.privateRow 13 9, 1470408714290355840⟩, ⟨.privateRow 13 11, 14607921172137733440⟩, ⟨.privateRow 13 12, 5503396810854365280⟩, ⟨.privateRow 13 15, 98535150591055738560⟩, ⟨.privateRow 13 20, 54740152262378943360⟩, ⟨.privateRow 14 3, 257088865394120760⟩, ⟨.privateRow 14 4, 48969307694118240⟩, ⟨.privateRow 14 5, 359924411551769064⟩, ⟨.privateRow 14 6, 757735603266882240⟩, ⟨.privateRow 14 7, 2370930647523558120⟩, ⟨.privateRow 14 8, 2570888653941207600⟩, ⟨.privateRow 14 9, 10958412887424397395⟩, ⟨.privateRow 14 11, 6978126346411849200⟩, ⟨.privateRow 14 12, 1621637458639838640⟩, ⟨.privateRow 14 13, 2742281230870621440⟩, ⟨.privateRow 14 14, 4253652136520907120⟩, ⟨.privateRow 14 15, 344344826308885345944⟩, ⟨.privateRow 14 22, 344670472205051232240⟩, ⟨.privateRow 15 1, 834607331134536960⟩, ⟨.privateRow 15 3, 1942449205200023520⟩, ⟨.privateRow 15 4, 1679647253908255632⟩, ⟨.privateRow 15 5, 5683017024501616800⟩, ⟨.privateRow 15 6, 9597984308047175040⟩, ⟨.privateRow 15 7, 18207940819677729120⟩, ⟨.privateRow 15 8, 35392567135923957960⟩, ⟨.privateRow 15 10, 23823568193188523760⟩, ⟨.privateRow 15 14, 1126803357764738349696⟩, ⟨.privateRow 15 21, 865418251775586949440⟩, ⟨.privateRow 16 3, 44990551443971133000⟩, ⟨.privateRow 16 6, 467901735017299783200⟩, ⟨.privateRow 16 9, 165822318179207890200⟩, ⟨.privateRow 16 14, 8814148922889989078400⟩, ⟨.privateRow 17 1, 219382498469649715200⟩, ⟨.privateRow 17 2, 446306270324193639360⟩, ⟨.privateRow 17 9, 19048307319047470464000⟩, ⟨.privateRow 17 16, 229007905590005596454400⟩, ⟨.hall 14 6, 33337228922197200⟩, ⟨.hall 15 6, 250118353892206800⟩, ⟨.hall 10 11, 9353229011280⟩, ⟨.hall 15 18, 316079715930778800⟩, ⟨.hall 16 21, 248675047981222262400⟩, ⟨.hall 5 23, 16401815259984⟩, ⟨.hall 3 29, 15604056803332998⟩, ⟨.hall 2 35, 19656871820887032131400⟩]
  caps := #[0, 8461235261044966400, 40769628993804110400, 0, 1444217322357477096, 0, 0, 100050612555554370, 679662336789355815, 0, 0, 2221373206528740, 3161990948508013050, 49624415489357280, 7196998370506693749, 0, 0, 0] }

theorem case_55_38_22_checked :
    (Witness.linear .conditional case_55_38_22).check 55 38 22 = true := by
  change case_55_38_22.check 55 38 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_23 : Certificate := {
  objectiveScale := 16302753967500000
  eta := 37005988298106688084224000
  rows := #[⟨.count 2, 4206256635599749166436000⟩, ⟨.count 3, 447673983088090361803200⟩, ⟨.count 4, 41833500176931330067200⟩, ⟨.count 5, 3132528944494517568000⟩, ⟨.count 6, 142387679295205344000⟩, ⟨.path 6, 146239406846557024000⟩, ⟨.privateRow 2 36, 1648003899392662601790000⟩, ⟨.privateRow 3 35, 1741566250175544969976800⟩, ⟨.privateRow 4 28, 475981670786829292800⟩, ⟨.privateRow 4 29, 6941399365641260520000⟩, ⟨.privateRow 4 30, 16566806485997141774400⟩, ⟨.privateRow 5 25, 136059337993196217600⟩, ⟨.privateRow 5 26, 815169463965050594400⟩, ⟨.privateRow 5 27, 3545453214450613065600⟩, ⟨.privateRow 5 28, 7195324060384376716800⟩, ⟨.privateRow 5 31, 108003427873401506846400⟩, ⟨.privateRow 6 22, 25079648057678214000⟩, ⟨.privateRow 6 23, 99671375506643740800⟩, ⟨.privateRow 6 24, 467374373242132356000⟩, ⟨.privateRow 6 25, 1414235960499773911500⟩, ⟨.privateRow 6 26, 2790968023328042844000⟩, ⟨.privateRow 6 27, 4107983427999518067000⟩, ⟨.privateRow 6 30, 82234817612951719716000⟩, ⟨.privateRow 7 18, 231148830024684000⟩, ⟨.privateRow 7 19, 3236083620345576000⟩, ⟨.privateRow 7 20, 13348844933925501000⟩, ⟨.privateRow 7 21, 61044304656518820000⟩, ⟨.privateRow 7 22, 220215490364516446800⟩, ⟨.privateRow 7 23, 570269846874231504000⟩, ⟨.privateRow 7 24, 1127977396916704834500⟩, ⟨.privateRow 7 25, 1983256961611788720000⟩, ⟨.privateRow 7 26, 3318064405394330592000⟩, ⟨.privateRow 7 27, 3626355304959252465600⟩, ⟨.privateRow 7 28, 6699502115020428714000⟩, ⟨.privateRow 7 29, 34038745560604941156000⟩, ⟨.privateRow 8 15, 70789329195059475⟩, ⟨.privateRow 8 16, 453051706848380640⟩, ⟨.privateRow 8 17, 1779845991190066800⟩, ⟨.privateRow 8 18, 8886783480487466400⟩, ⟨.privateRow 8 19, 34167649558148706600⟩, ⟨.privateRow 8 20, 106879016297413432800⟩, ⟨.privateRow 8 21, 253029378274820587440⟩, ⟨.privateRow 8 22, 497853486747831614400⟩, ⟨.privateRow 8 23, 892795019808090098700⟩, ⟨.privateRow 8 24, 1524518993544800853600⟩, ⟨.privateRow 8 25, 3056588848870408051200⟩, ⟨.privateRow 8 26, 3750815080997743318560⟩, ⟨.privateRow 8 27, 6191234731399901683500⟩, ⟨.privateRow 8 28, 15911553487604168394000⟩, ⟨.privateRow 8 29, 14571841836144602809800⟩, ⟨.privateRow 9 13, 59222445339657600⟩, ⟨.privateRow 9 14, 251695392693544800⟩, ⟨.privateRow 9 15, 1409494199083850880⟩, ⟨.privateRow 9 16, 6112602393986088000⟩, ⟨.privateRow 9 17, 20755189305190771200⟩, ⟨.privateRow 9 18, 58141635712208848800⟩, ⟨.privateRow 9 19, 129966348227212224000⟩, ⟨.privateRow 9 20, 251091323751080292480⟩, ⟨.privateRow 9 21, 445556777377061750400⟩, ⟨.privateRow 9 22, 750807356404844138400⟩, ⟨.privateRow 9 23, 1497371847618568521600⟩, ⟨.privateRow 9 24, 2590784575458887808000⟩, ⟨.privateRow 9 25, 3258347875653553562880⟩, ⟨.privateRow 9 27, 16527997453542775200000⟩, ⟨.privateRow 10 11, 62923848173386200⟩, ⟨.privateRow 10 12, 266501004028459200⟩, ⟨.privateRow 10 13, 1274207925511070550⟩, ⟨.privateRow 10 14, 4757042921907996720⟩, ⟨.privateRow 10 15, 14643278382063731400⟩, ⟨.privateRow 10 16, 37551016471471549200⟩, ⟨.privateRow 10 17, 80416677965587563600⟩, ⟨.privateRow 10 18, 151772321794207514400⟩, ⟨.privateRow 10 19, 264355670946030103440⟩, ⟨.privateRow 10 20, 437320744805034090000⟩, ⟨.privateRow 10 21, 850038264974274175800⟩, ⟨.privateRow 10 22, 1497174086952880736400⟩, ⟨.privateRow 10 24, 1374558878577986861760⟩, ⟨.privateRow 10 25, 12688845679556020774800⟩, ⟨.privateRow 10 27, 9289258934292484547400⟩, ⟨.privateRow 11 9, 85160095272252000⟩, ⟨.privateRow 11 10, 359564846705064000⟩, ⟨.privateRow 11 11, 1332505020142296000⟩, ⟨.privateRow 11 12, 4449614977975167000⟩, ⟨.privateRow 11 13, 12512856665336227200⟩, ⟨.privateRow 11 14, 30049347903208920000⟩, ⟨.privateRow 11 15, 61983447805080648000⟩, ⟨.privateRow 11 16, 114341621252210352000⟩, ⟨.privateRow 11 17, 195488869610875932000⟩, ⟨.privateRow 11 18, 316650782250814611600⟩, ⟨.privateRow 11 19, 593102214640003068000⟩, ⟨.privateRow 11 20, 1030288122627522759000⟩, ⟨.privateRow 11 21, 1716280062933278700000⟩, ⟨.privateRow 11 23, 2248107291054071647200⟩, ⟨.privateRow 11 24, 172321452783401922000⟩, ⟨.privateRow 12 7, 148320499265838900⟩, ⟨.privateRow 12 8, 468380523997386000⟩, ⟨.privateRow 12 9, 1648005547398210000⟩, ⟨.privateRow 12 10, 5060346445540386000⟩, ⟨.privateRow 12 11, 13534245558007799625⟩, ⟨.privateRow 12 12, 30455142515918920800⟩, ⟨.privateRow 12 13, 61235177554039203000⟩, ⟨.privateRow 12 14, 110898096374150316000⟩, ⟨.privateRow 12 15, 186883829074957014000⟩, ⟨.privateRow 12 16, 297719693071792992000⟩, ⟨.privateRow 12 17, 537513489339400173600⟩, ⟨.privateRow 12 18, 909039859944852636000⟩, ⟨.privateRow 12 19, 1504711465051935640500⟩, ⟨.privateRow 12 20, 2391350221020368322000⟩, ⟨.privateRow 12 21, 903766242193178364000⟩, ⟨.privateRow 12 22, 1873584546726076984800⟩, ⟨.privateRow 13 5, 339018284036203200⟩, ⟨.privateRow 13 6, 711938396476026720⟩, ⟨.privateRow 13 7, 2622930934385361600⟩, ⟨.privateRow 13 8, 7514905296135837600⟩, ⟨.privateRow 13 9, 18426640849967750400⟩, ⟨.privateRow 13 10, 40491496299574019700⟩, ⟨.privateRow 13 11, 79262474807664308160⟩, ⟨.privateRow 13 12, 142387679295205344000⟩, ⟨.privateRow 13 14, 850173101791788574800⟩, ⟨.privateRow 13 15, 420690870644924880000⟩, ⟨.privateRow 13 17, 3916452223280898100800⟩, ⟨.privateRow 13 18, 1700642844582108827400⟩, ⟨.privateRow 13 19, 4248238117257662299200⟩, ⟨.privateRow 13 20, 2939119013451863642400⟩, ⟨.privateRow 14 3, 1051727176612312200⟩, ⟨.privateRow 14 4, 2203618846235320800⟩, ⟨.privateRow 14 5, 4627599577094173680⟩, ⟨.privateRow 14 6, 14613472348718443200⟩, ⟨.privateRow 14 7, 34706996828206302600⟩, ⟨.privateRow 14 8, 73497169753848640800⟩, ⟨.privateRow 14 9, 140274112180667139675⟩, ⟨.privateRow 14 12, 302573818502311356000⟩, ⟨.privateRow 14 13, 4012514466638739761700⟩, ⟨.privateRow 14 15, 108748590061713081480⟩, ⟨.privateRow 14 16, 8815577194364400860400⟩, ⟨.privateRow 14 18, 21782772295036146108000⟩, ⟨.privateRow 15 1, 4694666237631770400⟩, ⟨.privateRow 15 2, 4908060157524123600⟩, ⟨.privateRow 15 3, 15425331923647245600⟩, ⟨.privateRow 15 4, 37792063212935751720⟩, ⟨.privateRow 15 5, 90928272392025868800⟩, ⟨.privateRow 15 6, 185960945968414016400⟩, ⟨.privateRow 15 7, 362041613972661823200⟩, ⟨.privateRow 15 8, 465652207445101226550⟩, ⟨.privateRow 15 11, 1312339777504142587200⟩, ⟨.privateRow 15 13, 265035248506302674400⟩, ⟨.privateRow 15 14, 507493420287994380240⟩, ⟨.privateRow 15 15, 29549794188400240154400⟩, ⟨.privateRow 15 16, 6006238617770146255500⟩, ⟨.privateRow 15 18, 151780124351381014288800⟩, ⟨.privateRow 16 4, 639339415256431890000⟩, ⟨.privateRow 16 8, 15710700564234719643600⟩, ⟨.privateRow 16 14, 128493014923981555848000⟩, ⟨.privateRow 16 15, 87866546970075622749000⟩, ⟨.privateRow 16 17, 422596249713220852269000⟩, ⟨.privateRow 17 2, 2591455763172737260800⟩, ⟨.privateRow 17 3, 6819620429401940160000⟩, ⟨.privateRow 17 12, 1479721240771632975916800⟩, ⟨.privateRow 17 14, 1562971757163557160420000⟩, ⟨.privateRow 17 15, 777436728951821178240000⟩, ⟨.privateRow 17 19, 20662540618363958426112000⟩, ⟨.hall 15 8, 3156314093763831000⟩, ⟨.hall 14 9, 5202715539171150⟩, ⟨.hall 15 13, 1797237381490551000⟩, ⟨.hall 12 15, 2155306011469380⟩, ⟨.hall 13 15, 18489106106551080⟩, ⟨.hall 8 19, 387159176039328⟩, ⟨.hall 14 22, 169594817834447705700⟩, ⟨.hall 5 24, 5870195323977600⟩, ⟨.hall 4 26, 24627494223832500⟩, ⟨.hall 3 30, 8977199921357047380⟩, ⟨.hall 4 32, 762027894709375694400⟩]
  caps := #[0, 7481587133911834944000, 1419166352938480146000, 50174349797563992000, 90611568875119886880, 19292547453758779200, 3966657308892850000, 6521378570844196050, 0, 4955907640175956800, 17942771785505556150, 3661002905620860000, 956222236900359000, 31795304690167375500, 480345068665949733675, 99633383291151940230, 7586426397838610322000, 0] }

theorem case_55_38_23_checked :
    (Witness.linear .conditional case_55_38_23).check 55 38 23 = true := by
  change case_55_38_23.check 55 38 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_38_24 : Certificate := {
  objectiveScale := 13
  eta := 797355
  rows := #[⟨.assumptionRow 24, 5⟩]
  caps := #[0, 0, 416520, 161460, 93610, 46046, 20020, 11305, 5130, 2601, 1428, 580, 364, 3714500, 3684784, 2615008, 1563320, 823650] }

theorem case_55_38_24_checked :
    (Witness.linear .conditional case_55_38_24).check 55 38 24 = true := by
  change case_55_38_24.check 55 38 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_39_1_checked :
    (Witness.rising).check 55 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_39_2_checked :
    (Witness.rising).check 55 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_39_3_checked :
    (Witness.rising).check 55 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_39_4_checked :
    (Witness.rising).check 55 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_39_5_checked :
    (Witness.rising).check 55 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_39_6_checked :
    (Witness.rising).check 55 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_39_7_checked :
    (Witness.rising).check 55 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_39_8_checked :
    (Witness.rising).check 55 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_39_9_checked :
    (Witness.rising).check 55 39 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_39_10_checked :
    (Witness.linear .positive case_55_39_10).check 55 39 10 = true := by
  change case_55_39_10.check 55 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_55_39_11_checked :
    (Witness.linear .positive case_55_39_11).check 55 39 11 = true := by
  change case_55_39_11.check 55 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_55_39_12_checked :
    (Witness.linear .positive case_55_39_12).check 55 39 12 = true := by
  change case_55_39_12.check 55 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_55_39_13_checked :
    (Witness.linear .positive case_55_39_13).check 55 39 13 = true := by
  change case_55_39_13.check 55 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_55_39_14_checked :
    (Witness.linear .positive case_55_39_14).check 55 39 14 = true := by
  change case_55_39_14.check 55 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_55_39_15_checked :
    (Witness.linear .positive case_55_39_15).check 55 39 15 = true := by
  change case_55_39_15.check 55 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_55_39_16_checked :
    (Witness.linear .positive case_55_39_16).check 55 39 16 = true := by
  change case_55_39_16.check 55 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_55_39_17_checked :
    (Witness.linear .positive case_55_39_17).check 55 39 17 = true := by
  change case_55_39_17.check 55 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_55_39_18_checked :
    (Witness.linear .positive case_55_39_18).check 55 39 18 = true := by
  change case_55_39_18.check 55 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_19 : Certificate := {
  objectiveScale := 999
  eta := 40875947760
  rows := #[⟨.assumptionRow 19, 1748⟩]
  caps := #[0, 0, 11625259725, 3333040515, 964321345, 281885976, 83374698, 24996970, 7613892, 2362776, 1430715, 431730585, 295861995, 139683830, 53086990, 16809826, 4423452] }

theorem case_55_39_19_checked :
    (Witness.linear .conditional case_55_39_19).check 55 39 19 = true := by
  change case_55_39_19.check 55 39 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_20 : Certificate := {
  objectiveScale := 881774916750000
  eta := 3026782433193913004410800
  rows := #[⟨.count 2, 283566118223876302694880⟩, ⟨.count 3, 23953251620309312901600⟩, ⟨.count 4, 1719720629150412208320⟩, ⟨.count 5, 95304714669665701200⟩, ⟨.count 6, 5776043313313072800⟩, ⟨.count 7, 1347743439773050320⟩, ⟨.path 5, 64348837633714233600⟩, ⟨.privateRow 2 36, 22356368178955358708160⟩, ⟨.privateRow 2 37, 36489704384042079730560⟩, ⟨.privateRow 3 32, 1683151857151236776304⟩, ⟨.privateRow 3 33, 4056451040680734215520⟩, ⟨.privateRow 3 34, 8691084017024107018320⟩, ⟨.privateRow 3 35, 11127707888745226779000⟩, ⟨.privateRow 3 36, 17749267675738778219040⟩, ⟨.privateRow 4 28, 45799210105144906410⟩, ⟨.privateRow 4 29, 439611906079442107440⟩, ⟨.privateRow 4 30, 782204621140663680960⟩, ⟨.privateRow 4 31, 1860348030351874487424⟩, ⟨.privateRow 4 32, 2791898669184151346820⟩, ⟨.privateRow 4 33, 3940673461378325511840⟩, ⟨.privateRow 4 34, 5888772425311232937480⟩, ⟨.privateRow 5 25, 14825177837503553520⟩, ⟨.privateRow 5 26, 79381375510865588160⟩, ⟨.privateRow 5 27, 166783250671914977100⟩, ⟨.privateRow 5 28, 392009974519566751920⟩, ⟨.privateRow 5 29, 680899239251056065240⟩, ⟨.privateRow 5 30, 1019831043050363495952⟩, ⟨.privateRow 5 31, 1426393896222663327960⟩, ⟨.privateRow 5 32, 2229659682703907454000⟩, ⟨.privateRow 5 33, 2106940155049016927640⟩, ⟨.privateRow 6 22, 2032311536165710800⟩, ⟨.privateRow 6 23, 13535778269582150400⟩, ⟨.privateRow 6 24, 33051803403958138800⟩, ⟨.privateRow 6 25, 88708615824215587200⟩, ⟨.privateRow 6 26, 166462359376730917500⟩, ⟨.privateRow 6 27, 271840768634496204000⟩, ⟨.privateRow 6 28, 406783198528326219600⟩, ⟨.privateRow 6 29, 563164223048024598000⟩, ⟨.privateRow 6 30, 877397023857014961300⟩, ⟨.privateRow 6 31, 917321249166165043200⟩, ⟨.privateRow 6 32, 136699691748409389600⟩, ⟨.privateRow 7 20, 1984589240984491680⟩, ⟨.privateRow 7 21, 6401781338921989020⟩, ⟨.privateRow 7 22, 19901094688596859920⟩, ⟨.privateRow 7 23, 44051957002867701888⟩, ⟨.privateRow 7 24, 77163660115260198480⟩, ⟨.privateRow 7 25, 122283650312265512070⟩, ⟨.privateRow 7 26, 180350076216161039760⟩, ⟨.privateRow 7 27, 248337773342943724440⟩, ⟨.privateRow 7 28, 385801186373891175888⟩, ⟨.privateRow 7 29, 227576106544535068320⟩, ⟨.privateRow 8 17, 59899708434357792⟩, ⟨.privateRow 8 18, 1101726780131937960⟩, ⟨.privateRow 8 19, 4527035656673579280⟩, ⟨.privateRow 8 20, 12067295428338330180⟩, ⟨.privateRow 8 21, 24436358327198235600⟩, ⟨.privateRow 8 22, 41270899111272518688⟩, ⟨.privateRow 8 23, 63759911866794183040⟩, ⟨.privateRow 8 24, 92470174895539841400⟩, ⟨.privateRow 8 25, 126324206537458129200⟩, ⟨.privateRow 8 26, 113934237084518050200⟩, ⟨.privateRow 9 16, 938428765471605408⟩, ⟨.privateRow 9 17, 3465625987987843680⟩, ⟨.privateRow 9 18, 8408997530207920800⟩, ⟨.privateRow 9 19, 16073088429886007520⟩, ⟨.privateRow 9 20, 26492007412104605280⟩, ⟨.privateRow 9 21, 40072904942585362848⟩, ⟨.privateRow 9 22, 57154305131116393200⟩, ⟨.privateRow 9 23, 16734481043848708140⟩, ⟨.privateRow 10 14, 902506767705167625⟩, ⟨.privateRow 10 15, 3119063389189059312⟩, ⟨.privateRow 10 16, 7082529300848172600⟩, ⟨.privateRow 10 17, 13062744108569564640⟩, ⟨.privateRow 10 18, 21146736352629527640⟩, ⟨.privateRow 10 19, 13512440720841491520⟩, ⟨.privateRow 11 12, 1038177719713134000⟩, ⟨.privateRow 11 13, 3409470011330633250⟩, ⟨.privateRow 11 14, 7487463554294724000⟩, ⟨.privateRow 11 15, 8091044799998074200⟩, ⟨.privateRow 12 10, 1451141745999025080⟩, ⟨.privateRow 12 11, 4734090401891891040⟩, ⟨.privateRow 12 12, 485348083965890145⟩, ⟨.privateRow 13 8, 2117882548214793360⟩, ⟨.privateRow 14 6, 458874552113205228⟩, ⟨.hall 4 34, 432048039835817845440⟩, ⟨.hall 3 35, 2173535795176215429960⟩, ⟨.assumptionRow 20, 782489135888460⟩]
  caps := #[0, 281096557818663787200, 74280177521262793080, 18767519425387861128, 1107383206183195500, 1657830351207205032, 0, 1517911243153882236, 403548255663933744, 257721027288199020, 72887481422322840, 5213745915594559200, 4595649034469220, 782489135888460, 48182181134981817924, 56260226959488672120, 16319574247265649360] }

theorem case_55_39_20_checked :
    (Witness.linear .conditional case_55_39_20).check 55 39 20 = true := by
  change case_55_39_20.check 55 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_21 : Certificate := {
  objectiveScale := 9052889145300000
  eta := 33456818919305061096616800
  rows := #[⟨.count 2, 3129634575304566824214720⟩, ⟨.count 3, 259989143736299818080240⟩, ⟨.count 4, 17759151127630447254720⟩, ⟨.count 5, 804795368321621476800⟩, ⟨.count 6, 12193869216994264800⟩, ⟨.path 5, 712056999927469996800⟩, ⟨.privateRow 2 36, 259989143736299818080240⟩, ⟨.privateRow 2 37, 437790796025443825124160⟩, ⟨.privateRow 3 32, 17065238676722026959168⟩, ⟨.privateRow 3 33, 45118840336530904043100⟩, ⟨.privateRow 3 34, 100729082516210056949040⟩, ⟨.privateRow 3 35, 134266693948323849712800⟩, ⟨.privateRow 3 36, 221627231179635861019440⟩, ⟨.privateRow 4 28, 405750998195484161220⟩, ⟨.privateRow 4 29, 4447452499701151065840⟩, ⟨.privateRow 4 30, 8177615159223587117040⟩, ⟨.privateRow 4 31, 20557156358161951255728⟩, ⟨.privateRow 4 32, 32315887352147775716340⟩, ⟨.privateRow 4 33, 47634943633880862299040⟩, ⟨.privateRow 4 34, 74497224594304761369120⟩, ⟨.privateRow 5 25, 158276422436585557104⟩, ⟨.privateRow 5 26, 771013834342689217280⟩, ⟨.privateRow 5 27, 1655978247456225302610⟩, ⟨.privateRow 5 28, 4067410242438163146240⟩, ⟨.privateRow 5 29, 7466712583872821479200⟩, ⟨.privateRow 5 30, 11719608996914634527712⟩, ⟨.privateRow 5 31, 17250565165704978127020⟩, ⟨.privateRow 5 32, 28504659656517282157920⟩, ⟨.privateRow 5 33, 29368324315669837057560⟩, ⟨.privateRow 6 22, 31331469515888041500⟩, ⟨.privateRow 6 23, 130622205097196139600⟩, ⟨.privateRow 6 24, 311959820801436607800⟩, ⟨.privateRow 6 25, 866216339192407403200⟩, ⟨.privateRow 6 26, 1707141690379197072000⟩, ⟨.privateRow 6 27, 2936690169759452106000⟩, ⟨.privateRow 6 28, 4624186181955713973600⟩, ⟨.privateRow 6 29, 6766784490817350679680⟩, ⟨.privateRow 6 30, 11237158561344256440900⟩, ⟨.privateRow 6 31, 12936340364873471145600⟩, ⟨.privateRow 6 32, 6358086640894426237800⟩, ⟨.privateRow 7 19, 4529151423455012640⟩, ⟨.privateRow 7 20, 23355949500242861040⟩, ⟨.privateRow 7 21, 60054805893696754140⟩, ⟨.privateRow 7 22, 184016571820095268800⟩, ⟨.privateRow 7 23, 423249200521870931208⟩, ⟨.privateRow 7 24, 777562393737000952080⟩, ⟨.privateRow 7 25, 1295751027670853063310⟩, ⟨.privateRow 7 26, 2015994977832494664720⟩, ⟨.privateRow 7 27, 2940551561678166956520⟩, ⟨.privateRow 7 28, 4889741556014700184800⟩, ⟨.privateRow 7 29, 5938414308676206957600⟩, ⟨.privateRow 8 16, 652033284519832215⟩, ⟨.privateRow 8 17, 4299467960955014848⟩, ⟨.privateRow 8 18, 12939050113588358760⟩, ⟨.privateRow 8 19, 41803084982362389840⟩, ⟨.privateRow 8 20, 109857729149402033800⟩, ⟨.privateRow 8 21, 231067663142234755200⟩, ⟨.privateRow 8 22, 407437816770501701184⟩, ⟨.privateRow 8 23, 660410924296693089520⟩, ⟨.privateRow 8 24, 1009110421424147602560⟩, ⟨.privateRow 8 25, 1459335170402724735120⟩, ⟨.privateRow 8 26, 2425405749738740728960⟩, ⟨.privateRow 8 27, 864572424972042250464⟩, ⟨.privateRow 9 13, 158068675035110840⟩, ⟨.privateRow 9 14, 892623106080625920⟩, ⟨.privateRow 9 15, 3082339163184661380⟩, ⟨.privateRow 9 16, 11191262192485847472⟩, ⟨.privateRow 9 17, 31704059964185088480⟩, ⟨.privateRow 9 18, 75872964016853203200⟩, ⟨.privateRow 9 19, 149612000920732410060⟩, ⟨.privateRow 9 20, 256071253556879560800⟩, ⟨.privateRow 9 21, 404497739414848639560⟩, ⟨.privateRow 9 22, 605403025384474517200⟩, ⟨.privateRow 9 23, 864714686779573850220⟩, ⟨.privateRow 9 24, 286013976856387699920⟩, ⟨.privateRow 10 10, 60969346084971324⟩, ⟨.privateRow 10 11, 256713036147247680⟩, ⟨.privateRow 10 12, 880668332338474680⟩, ⟨.privateRow 10 13, 3442974837739557120⟩, ⟨.privateRow 10 14, 11126905660507266630⟩, ⟨.privateRow 10 15, 28777531352106464928⟩, ⟨.privateRow 10 16, 63756516191712870240⟩, ⟨.privateRow 10 17, 119968913296428189840⟩, ⟨.privateRow 10 18, 200487533042747370420⟩, ⟨.privateRow 10 19, 310056838181208714960⟩, ⟨.privateRow 10 20, 233390656813270228272⟩, ⟨.privateRow 11 8, 96776739817414800⟩, ⟨.privateRow 11 9, 304846730424856620⟩, ⟨.privateRow 11 10, 1283565180736238400⟩, ⟨.privateRow 11 11, 4629154054599674600⟩, ⟨.privateRow 11 12, 13508894328630901200⟩, ⟨.privateRow 11 13, 32516984578651372800⟩, ⟨.privateRow 11 14, 67608230436445979280⟩, ⟨.privateRow 11 15, 123100013047751625600⟩, ⟨.privateRow 11 16, 102553566748054329600⟩, ⟨.privateRow 12 6, 203231153616571080⟩, ⟨.privateRow 12 7, 638726482794937680⟩, ⟨.privateRow 12 8, 2235542689782281880⟩, ⟨.privateRow 12 9, 7530249060319265280⟩, ⟨.privateRow 12 10, 20865065104634630880⟩, ⟨.privateRow 12 11, 47077898996591583120⟩, ⟨.privateRow 12 12, 41636982597195000015⟩, ⟨.privateRow 13 4, 583185049508421360⟩, ⟨.privateRow 13 5, 1829080382549139720⟩, ⟨.privateRow 13 6, 5109811862359501440⟩, ⟨.privateRow 13 7, 16095907366432429536⟩, ⟨.privateRow 13 8, 16943060385718346880⟩, ⟨.privateRow 14 2, 2421837913930805370⟩, ⟨.privateRow 14 3, 5054270429072985120⟩, ⟨.privateRow 14 4, 5284009994030848080⟩, ⟨.hall 4 34, 7552812913753579078464⟩, ⟨.hall 3 35, 29628765039029472896580⟩, ⟨.assumptionRow 21, 5632601813215650⟩]
  caps := #[0, 0, 787863114033775507728, 151617056864748130656, 18585750696344970138, 25403127094488535964, 5153311293666354000, 6152787645819728508, 2765676759823239157, 15275565066108050886, 0, 145165109726122200, 17386096120753814025, 850478197199781150, 0, 1396040911161456760200, 469586604343530573900] }

theorem case_55_39_21_checked :
    (Witness.linear .conditional case_55_39_21).check 55 39 21 = true := by
  change case_55_39_21.check 55 39 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_22 : Certificate := {
  objectiveScale := 9211093740946468800000
  eta := 53087909764389951147943742496000
  rows := #[⟨.count 2, 5033208941085889913385365128800⟩, ⟨.count 3, 426813754165869435942178602000⟩, ⟨.count 4, 29961104660425933346385633600⟩, ⟨.count 5, 1484856508501285242937614000⟩, ⟨.count 6, 19998067454562764214648000⟩, ⟨.path 5, 992897982496254735796896000⟩, ⟨.path 6, 24646736216157487784352000⟩, ⟨.privateRow 2 36, 418711203835529089307877054000⟩, ⟨.privateRow 2 37, 708639519479413375051737739200⟩, ⟨.privateRow 3 32, 27806046251297401332067782960⟩, ⟨.privateRow 3 33, 72184191031179146927351143800⟩, ⟨.privateRow 3 34, 161653822767084366674545590000⟩, ⟨.privateRow 3 35, 216910038549287750192390264400⟩, ⟨.privateRow 3 36, 361326082672412751968470796400⟩, ⟨.privateRow 4 28, 948658324875821127432364500⟩, ⟨.privateRow 4 29, 7282867636934875239170202000⟩, ⟨.privateRow 4 30, 13116232491761352979282257000⟩, ⟨.privateRow 4 31, 32699839998328303905581677200⟩, ⟨.privateRow 4 32, 51513521907894588409617149400⟩, ⟨.privateRow 4 33, 76563601153166270933990600400⟩, ⟨.privateRow 4 34, 121301777807454994827685007400⟩, ⟨.privateRow 5 25, 410626985067022091874105600⟩, ⟨.privateRow 5 26, 1326390340652999931688579200⟩, ⟨.privateRow 5 27, 2702530503281505888149107950⟩, ⟨.privateRow 5 28, 6471041327172267787123182000⟩, ⟨.privateRow 5 29, 11769473749071298380338017800⟩, ⟨.privateRow 5 30, 18517810501576028407479755040⟩, ⟨.privateRow 5 31, 27526673248957159515989150400⟩, ⟨.privateRow 5 32, 46278638900351168378239972800⟩, ⟨.privateRow 5 33, 48998431624359078096888252600⟩, ⟨.privateRow 6 21, 6922407965040956843532000⟩, ⟨.privateRow 6 22, 97768329777862402827168000⟩, ⟨.privateRow 6 23, 262853386618684817518290000⟩, ⟨.privateRow 6 24, 539281219024709208321674400⟩, ⟨.privateRow 6 25, 1406345577013001798243070000⟩, ⟨.privateRow 6 26, 2690156699043995177791294500⟩, ⟨.privateRow 6 27, 4585747325116523384554164000⟩, ⟨.privateRow 6 28, 7235411905435555663771950000⟩, ⟨.privateRow 6 29, 10701632497185020556731966400⟩, ⟨.privateRow 6 30, 18127831521155842369657273500⟩, ⟨.privateRow 6 31, 21562916232882300514444206000⟩, ⟨.privateRow 6 32, 12800429676541382661059274000⟩, ⟨.privateRow 7 17, 62493960795508638170775⟩, ⟨.privateRow 7 18, 2399768094547531705757760⟩, ⟨.privateRow 7 19, 22497825886383109741479000⟩, ⟨.privateRow 7 20, 61301768312640473381055600⟩, ⟨.privateRow 7 21, 122988114845560999920085200⟩, ⟨.privateRow 7 22, 318605574673829493510642000⟩, ⟨.privateRow 7 23, 683333964922409653214522160⟩, ⟨.privateRow 7 24, 1218215609107115053408974000⟩, ⟨.privateRow 7 25, 2007431008673328475321634550⟩, ⟨.privateRow 7 26, 3124698039775431908538750000⟩, ⟨.privateRow 7 27, 4603888429164591034948880400⟩, ⟨.privateRow 7 28, 7814244857870400116873706000⟩, ⟨.privateRow 7 29, 9964537060922261339053732200⟩, ⟨.privateRow 7 30, 1673838245946903364766037600⟩, ⟨.privateRow 8 14, 43205701290722021451400⟩, ⟨.privateRow 8 15, 823449836364349114720800⟩, ⟨.privateRow 8 16, 5881376088199535170071825⟩, ⟨.privateRow 8 17, 17109457711125920494754400⟩, ⟨.privateRow 8 18, 35385469357101335568696600⟩, ⟨.privateRow 8 19, 86564284293703520824858800⟩, ⟨.privateRow 8 20, 190472334140148031568496900⟩, ⟨.privateRow 8 21, 373792160821168353949448400⟩, ⟨.privateRow 8 22, 637793921313380336261276520⟩, ⟨.privateRow 8 23, 1018531202227480933695303600⟩, ⟨.privateRow 8 24, 1552294435973060786705899200⟩, ⟨.privateRow 8 25, 2261781429111048632676688800⟩, ⟨.privateRow 8 26, 3829537333903146371344839000⟩, ⟨.privateRow 8 27, 2451940830528991006175530560⟩, ⟨.privateRow 9 12, 327453736098103741526400⟩, ⟨.privateRow 9 13, 1857845155501046922410200⟩, ⟨.privateRow 9 14, 5809896067681796531641200⟩, ⟨.privateRow 9 15, 12880699697296502645198625⟩, ⟨.privateRow 9 16, 31263645453966454722233040⟩, ⟨.privateRow 9 17, 66104722974804692820642000⟩, ⟨.privateRow 9 18, 133525558081234456448572800⟩, ⟨.privateRow 9 19, 244457857902905197372021200⟩, ⟨.privateRow 9 20, 403203460027070762733819600⟩, ⟨.privateRow 9 21, 624417436193772798419923080⟩, ⟨.privateRow 9 22, 927885640919546132690266400⟩, ⟨.privateRow 9 23, 1329190995933094948436232450⟩, ⟨.privateRow 9 24, 944464285729100325492903600⟩, ⟨.privateRow 10 9, 142843338961162601533200⟩, ⟨.privateRow 10 10, 749927529546103658049300⟩, ⟨.privateRow 10 11, 2420818691868124089141600⟩, ⟨.privateRow 10 12, 5832769674247472895939000⟩, ⟨.privateRow 10 13, 14763279209103687699637200⟩, ⟨.privateRow 10 14, 31309474358549827723558275⟩, ⟨.privateRow 10 15, 53861461677622378284785280⟩, ⟨.privateRow 10 16, 130273125132580292598278400⟩, ⟨.privateRow 10 17, 192289110140026578987000000⟩, ⟨.privateRow 10 18, 319635778148761514697457200⟩, ⟨.privateRow 10 19, 482226126574797564357762000⟩, ⟨.privateRow 10 20, 495652101861338111060050680⟩, ⟨.privateRow 11 6, 72456766139720160198000⟩, ⟨.privateRow 11 7, 378751277548537201035000⟩, ⟨.privateRow 11 8, 1269718568543667569184000⟩, ⟨.privateRow 11 9, 3249685961366449184880300⟩, ⟨.privateRow 11 10, 8683371394744358145834000⟩, ⟨.privateRow 11 11, 19627732872070861173636000⟩, ⟨.privateRow 11 12, 39015837484882255673676000⟩, ⟨.privateRow 11 13, 64368779619373897315898250⟩, ⟨.privateRow 11 14, 135764657941531654834999200⟩, ⟨.privateRow 11 15, 215812477947156497149743000⟩, ⟨.privateRow 11 16, 138191773820632434765324000⟩, ⟨.privateRow 12 4, 305526030555820008834900⟩, ⟨.privateRow 12 5, 956429313044306114613600⟩, ⟨.privateRow 12 6, 2333107869698989158375600⟩, ⟨.privateRow 12 7, 6459693217465908758223600⟩, ⟨.privateRow 12 8, 15765143176680312455880840⟩, ⟨.privateRow 12 9, 33189775108800657801854400⟩, ⟨.privateRow 12 10, 62530994253757828474876200⟩, ⟨.privateRow 12 11, 100715757366753842912398800⟩, ⟨.privateRow 13 1, 423036042308058473771400⟩, ⟨.privateRow 13 2, 879914968000761625444512⟩, ⟨.privateRow 13 3, 2291445229168650066261750⟩, ⟨.privateRow 13 4, 6216790534787989744988400⟩, ⟨.privateRow 13 5, 15998453963650211371718400⟩, ⟨.privateRow 13 6, 36663123666698401060188000⟩, ⟨.privateRow 13 7, 14848565085012852429376140⟩, ⟨.privateRow 14 1, 19064824306683168551297760⟩, ⟨.privateRow 14 2, 5957757595838490172280550⟩, ⟨.privateRow 15 0, 13345377014678217985908432⟩, ⟨.hall 4 34, 13316884530000098085655943040⟩, ⟨.hall 3 35, 49258739802392636744415587400⟩, ⟨.assumptionRow 22, 934310931801654697290⟩]
  caps := #[0, 0, 286061113326782774937502260, 61207171582807171330308900, 41197008559678719900918480, 0, 9545085735349369588446900, 9874095750913777824899070, 0, 766538670393650157458180, 6210579954833156588400, 36620837378185074291937200, 2471756678506041366459096, 25464431570139680921800074, 612208797325466609947330080, 0, 1265454571293502507829777580] }

theorem case_55_39_22_checked :
    (Witness.linear .conditional case_55_39_22).check 55 39 22 = true := by
  change case_55_39_22.check 55 39 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_23 : Certificate := {
  objectiveScale := 194907947622968580000000
  eta := 1167663770932031691340547689164000
  rows := #[⟨.count 2, 111149641542150474139235557598400⟩, ⟨.count 3, 9184288461501549617902182902400⟩, ⟨.count 4, 628347278649343876729926019200⟩, ⟨.count 5, 27808979301190737204152598000⟩, ⟨.count 6, 369964247909411137970988000⟩, ⟨.path 5, 23201139136306476515186016000⟩, ⟨.path 6, 240006074740873956811296000⟩, ⟨.privateRow 2 37, 43588336770916628630124472887600⟩, ⟨.privateRow 3 32, 440168663592700995512362682880⟩, ⟨.privateRow 3 33, 1629470533492210416079419547200⟩, ⟨.privateRow 3 35, 12047324620727311101132634888200⟩, ⟨.privateRow 4 29, 124762514802136561756330610400⟩, ⟨.privateRow 4 30, 249941679816799674627566643000⟩, ⟨.privateRow 5 25, 2496025459228827144177599040⟩, ⟨.privateRow 5 26, 20137016989913726235635702400⟩, ⟨.privateRow 5 27, 46139166267402436544206840950⟩, ⟨.privateRow 5 28, 123367221067163925464554312800⟩, ⟨.privateRow 5 29, 135563121861739561200080469600⟩, ⟨.privateRow 5 30, 280178857798435846933935492240⟩, ⟨.privateRow 5 31, 532575867007194313480502925600⟩, ⟨.privateRow 5 32, 897303065451754453787323828800⟩, ⟨.privateRow 5 33, 1148578671917960838573463645200⟩, ⟨.privateRow 6 21, 61660707984901856328498000⟩, ⟨.privateRow 6 22, 709098141826371347777727000⟩, ⟨.privateRow 6 23, 3139090588322276322178080000⟩, ⟨.privateRow 6 24, 8046722392029692250868989000⟩, ⟨.privateRow 6 25, 23677711866202312830143232000⟩, ⟨.privateRow 6 26, 50677394375091213169984293750⟩, ⟨.privateRow 6 27, 74583030644023431076198938000⟩, ⟨.privateRow 6 28, 131327031223176803670312657000⟩, ⟨.privateRow 6 29, 232695179793422625412485752400⟩, ⟨.privateRow 6 30, 463950582055397792479701076500⟩, ⟨.privateRow 6 31, 639647631066043556933062086000⟩, ⟨.privateRow 6 32, 675431395266614934222367092000⟩, ⟨.privateRow 7 18, 19731426555168594025119360⟩, ⟨.privateRow 7 19, 166483911559235012086944600⟩, ⟨.privateRow 7 20, 583405160164840640646558000⟩, ⟨.privateRow 7 21, 1464441814641419087801827500⟩, ⟨.privateRow 7 22, 4685092703070997410850784400⟩, ⟨.privateRow 7 23, 11343103840902545490190492080⟩, ⟨.privateRow 7 24, 22349951287594092857202908400⟩, ⟨.privateRow 7 25, 36201001657935879850461175800⟩, ⟨.privateRow 7 26, 59400402603626739709370487600⟩, ⟨.privateRow 7 27, 99619039820407439084321368800⟩, ⟨.privateRow 7 28, 201327144427343353061052249840⟩, ⟨.privateRow 7 29, 324310659717389803545368080800⟩, ⟨.privateRow 8 15, 6770587543440203832148800⟩, ⟨.privateRow 8 16, 44960932905657603572863125⟩, ⟨.privateRow 8 17, 141956652160796273680719840⟩, ⟨.privateRow 8 18, 335023180051300086051505800⟩, ⟨.privateRow 8 19, 1024832587584958545439292400⟩, ⟨.privateRow 8 20, 2769593466988508380088368500⟩, ⟨.privateRow 8 21, 6063676653109197095673991200⟩, ⟨.privateRow 8 22, 11311451344136962537275196440⟩, ⟨.privateRow 8 23, 18722931420126643663835481600⟩, ⟨.privateRow 8 24, 29753346959647975740377901600⟩, ⟨.privateRow 8 25, 47092338045002377739951539200⟩, ⟨.privateRow 8 26, 91878565611369426053217253200⟩, ⟨.privateRow 8 27, 152651359401288695650584882000⟩, ⟨.privateRow 8 28, 220963202420828632215050199600⟩, ⟨.privateRow 9 12, 3028947058907459609119200⟩, ⟨.privateRow 9 13, 14387498529810433143316200⟩, ⟨.privateRow 9 14, 45701465918221375867004400⟩, ⟨.privateRow 9 15, 106107801657351944431956975⟩, ⟨.privateRow 9 16, 295423303145440893876092640⟩, ⟨.privateRow 9 17, 778980277542593451616691400⟩, ⟨.privateRow 9 18, 1901363267247255703093633200⟩, ⟨.privateRow 9 19, 3858247522410831154599294300⟩, ⟨.privateRow 9 20, 6895535659014600321051182400⟩, ⟨.privateRow 9 21, 11282676347077341670988564040⟩, ⟨.privateRow 9 22, 17546353762577701575670956800⟩, ⟨.privateRow 9 23, 26645647277208922181421602400⟩, ⟨.privateRow 9 24, 49184691402623380731365238000⟩, ⟨.privateRow 9 25, 82008741619919468916902340000⟩, ⟨.privateRow 9 26, 125269072199353479292225490160⟩, ⟨.privateRow 9 27, 154082915505004833748344843900⟩, ⟨.privateRow 10 9, 1761734513854338752242800⟩, ⟨.privateRow 10 10, 5549463718641167069564820⟩, ⟨.privateRow 10 11, 19471802521547954630052000⟩, ⟨.privateRow 10 12, 45217852522261361307565200⟩, ⟨.privateRow 10 13, 117518055218283537943725600⟩, ⟨.privateRow 10 14, 282097739030925992702878350⟩, ⟨.privateRow 10 15, 673334931195128271107198160⟩, ⟨.privateRow 10 16, 1490427398720770584397408800⟩, ⟨.privateRow 10 17, 2828803557091959008793554400⟩, ⟨.privateRow 10 18, 4784870939628384051091444800⟩, ⟨.privateRow 10 19, 7463187873736211955978385200⟩, ⟨.privateRow 10 20, 10991637805388604909118053480⟩, ⟨.privateRow 10 21, 15563162695389228537312895200⟩, ⟨.privateRow 10 22, 27141502137254174609396607150⟩, ⟨.privateRow 10 24, 153837300351531641353969660200⟩, ⟨.privateRow 11 7, 2802759453859175287659000⟩, ⟨.privateRow 11 8, 8808672569271693761214000⟩, ⟨.privateRow 11 9, 24664283193960742531399200⟩, ⟨.privateRow 11 10, 64906008405159848766840000⟩, ⟨.privateRow 11 12, 663759385955119982830302000⟩, ⟨.privateRow 11 13, 616607079849018563284980000⟩, ⟨.privateRow 11 14, 1599067693741788140785714800⟩, ⟨.privateRow 11 15, 2933287965567474022484262000⟩, ⟨.privateRow 11 16, 4880682193574154627848034000⟩, ⟨.privateRow 11 17, 7563713512814627709629088000⟩, ⟨.privateRow 11 18, 11132560550728644242581548000⟩, ⟨.privateRow 11 19, 15772809102537894848829788400⟩, ⟨.privateRow 11 21, 81515455956040254066274356000⟩, ⟨.privateRow 11 23, 150349359636519026347654290000⟩, ⟨.privateRow 12 5, 5897980763773221040117200⟩, ⟨.privateRow 12 6, 18498212395470556898549400⟩, ⟨.privateRow 12 7, 51677545739727270065788800⟩, ⟨.privateRow 12 8, 122088201810105675530426040⟩, ⟨.privateRow 12 9, 14279321849135166728704800⟩, ⟨.privateRow 12 10, 926965976706357906805086600⟩, ⟨.privateRow 12 11, 1141085807767654352996792400⟩, ⟨.privateRow 12 12, 2094151794937229295556613325⟩, ⟨.privateRow 12 13, 3952040310445642978281198480⟩, ⟨.privateRow 12 14, 6472612603900840575740047200⟩, ⟨.privateRow 12 15, 9934014369506034453415862400⟩, ⟨.privateRow 12 18, 2970812910712571437907033640⟩, ⟨.privateRow 12 20, 314461903134501354543298737750⟩, ⟨.privateRow 12 26, 1124093204777156311425417089400⟩, ⟨.privateRow 13 3, 16956694695848010490336950⟩, ⟨.privateRow 13 4, 53081826873958989361054800⟩, ⟨.privateRow 13 5, 129487486768293898289845800⟩, ⟨.privateRow 13 6, 290686194785965894120062000⟩, ⟨.privateRow 13 7, 81392134540070450353617360⟩, ⟨.privateRow 13 8, 1627842690801409007072347200⟩, ⟨.privateRow 13 9, 2645244372552289636492564200⟩, ⟨.privateRow 13 10, 4045667863903501796988627600⟩, ⟨.privateRow 13 12, 25936960206769116846019398720⟩, ⟨.privateRow 13 13, 10813526446037931261266306400⟩, ⟨.privateRow 13 14, 22351532331388577520185690400⟩, ⟨.privateRow 13 15, 33913389391696020980673900⟩, ⟨.privateRow 13 17, 7284596041336305306648753720⟩, ⟨.privateRow 13 19, 562674000092324532100851011850⟩, ⟨.privateRow 13 21, 87021757179091989836409227400⟩, ⟨.privateRow 14 1, 141079699869455447279603424⟩, ⟨.privateRow 14 2, 146958020697349424249586900⟩, ⟨.privateRow 14 3, 460042499574311241129141600⟩, ⟨.privateRow 14 4, 961907044564468958724568800⟩, ⟨.privateRow 14 5, 503856070962340883141440800⟩, ⟨.privateRow 14 9, 1970966395235039336994459600⟩, ⟨.privateRow 14 11, 1881062664926072630394712320⟩, ⟨.privateRow 14 12, 3023136425774045298848644800⟩, ⟨.privateRow 14 15, 4488899541300855140714654400⟩, ⟨.privateRow 14 17, 1671206611370257652566302226800⟩, ⟨.privateRow 14 19, 672143998663762738110682027200⟩, ⟨.privateRow 15 3, 17394485722540813670269285800⟩, ⟨.privateRow 15 8, 7987600654373580470977546800⟩, ⟨.privateRow 15 10, 8229649159051567757976866400⟩, ⟨.privateRow 15 11, 881748124184096545497521400⟩, ⟨.privateRow 15 18, 18310381546806948863801529392400⟩, ⟨.privateRow 15 20, 943117793627309665064148889440⟩, ⟨.privateRow 15 23, 8363380957886155734043990479000⟩, ⟨.privateRow 16 1, 144913387365908040955679604000⟩, ⟨.privateRow 16 2, 109416926319208344054919701000⟩, ⟨.privateRow 16 6, 20574122897628919394942166000⟩, ⟨.privateRow 16 7, 87137461684075423319755056000⟩, ⟨.privateRow 16 9, 98755789908618813095722396800⟩, ⟨.privateRow 16 12, 15430592173221689546206624500⟩, ⟨.privateRow 16 13, 50500119839634620333039862000⟩, ⟨.privateRow 16 14, 74066842431464109821791797600⟩, ⟨.privateRow 16 15, 82296491590515677579768664000⟩, ⟨.privateRow 16 17, 127924017856628726820780404712000⟩, ⟨.privateRow 16 18, 127302385429078938756204652125000⟩, ⟨.hall 15 6, 528278468410692334310976000⟩, ⟨.hall 14 7, 36080685672355271582975340⟩, ⟨.hall 15 8, 118833882055346369319408000⟩, ⟨.hall 13 9, 2820307165222467515546952⟩, ⟨.hall 9 11, 19838730294212564898108⟩, ⟨.hall 15 11, 62015533030850780054173500⟩, ⟨.hall 10 12, 20993610566708758585200⟩, ⟨.hall 12 13, 69550320117697288357488⟩, ⟨.hall 12 16, 175233595341869031881760⟩, ⟨.hall 7 21, 1559799577839711803595⟩, ⟨.hall 12 22, 17698983300519469292180760⟩, ⟨.hall 13 22, 192274172899007005907820720⟩, ⟨.hall 15 23, 2954958401171953548098568591750⟩, ⟨.hall 5 26, 154696813795453303874500⟩, ⟨.hall 4 29, 3802438183650128299314180⟩, ⟨.hall 2 34, 7878009066283855982475152160⟩]
  caps := #[0, 0, 0, 0, 0, 560326345760701874484418860, 0, 55420994195178259350306240, 593719124722500288566548935, 426917693797889460980416120, 0, 2394569154287310350472792000, 771101344275816485765920185, 1343168003283047279844597432, 0, 675876075919320924753208062960, 0] }

theorem case_55_39_23_checked :
    (Witness.linear .conditional case_55_39_23).check 55 39 23 = true := by
  change case_55_39_23.check 55 39 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_24 : Certificate := {
  objectiveScale := 21
  eta := 1204515
  rows := #[⟨.assumptionRow 24, 8⟩]
  caps := #[0, 0, 610740, 248170, 141680, 67298, 30877, 17157, 7467, 4029, 2176, 910, 21395520, 21246940, 15155160, 9152528, 4903140] }

theorem case_55_39_24_checked :
    (Witness.linear .conditional case_55_39_24).check 55 39 24 = true := by
  change case_55_39_24.check 55 39 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876] }

theorem case_55_39_25_checked :
    (Witness.linear .negative case_55_39_25).check 55 39 25 = true := by
  change case_55_39_25.check 55 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_40_1_checked :
    (Witness.rising).check 55 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_40_2_checked :
    (Witness.rising).check 55 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_40_3_checked :
    (Witness.rising).check 55 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_40_4_checked :
    (Witness.rising).check 55 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_40_5_checked :
    (Witness.rising).check 55 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_40_6_checked :
    (Witness.rising).check 55 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_40_7_checked :
    (Witness.rising).check 55 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_40_8_checked :
    (Witness.rising).check 55 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_40_9_checked :
    (Witness.rising).check 55 40 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_55_40_10_checked :
    (Witness.linear .positive case_55_40_10).check 55 40 10 = true := by
  change case_55_40_10.check 55 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_55_40_11_checked :
    (Witness.linear .positive case_55_40_11).check 55 40 11 = true := by
  change case_55_40_11.check 55 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_55_40_12_checked :
    (Witness.linear .positive case_55_40_12).check 55 40 12 = true := by
  change case_55_40_12.check 55 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_55_40_13_checked :
    (Witness.linear .positive case_55_40_13).check 55 40 13 = true := by
  change case_55_40_13.check 55 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_55_40_14_checked :
    (Witness.linear .positive case_55_40_14).check 55 40 14 = true := by
  change case_55_40_14.check 55 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_55_40_15_checked :
    (Witness.linear .positive case_55_40_15).check 55 40 15 = true := by
  change case_55_40_15.check 55 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_55_40_16_checked :
    (Witness.linear .positive case_55_40_16).check 55 40 16 = true := by
  change case_55_40_16.check 55 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_55_40_17_checked :
    (Witness.linear .positive case_55_40_17).check 55 40 17 = true := by
  change case_55_40_17.check 55 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_55_40_18_checked :
    (Witness.linear .positive case_55_40_18).check 55 40 18 = true := by
  change case_55_40_18.check 55 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_55_40_19_checked :
    (Witness.linear .positive case_55_40_19).check 55 40 19 = true := by
  change case_55_40_19.check 55 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_20 : Certificate := {
  objectiveScale := 299
  eta := 28521853800
  rows := #[⟨.assumptionRow 20, 467⟩]
  caps := #[0, 0, 8045420700, 2284751805, 653684265, 188585165, 54915168, 16571192, 5122780, 1608438, 520260, 321910875, 237301350, 121808115, 51045280, 18162870] }

theorem case_55_40_20_checked :
    (Witness.linear .conditional case_55_40_20).check 55 40 20 = true := by
  change case_55_40_20.check 55 40 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_21 : Certificate := {
  objectiveScale := 91334405635200000
  eta := 847461552016224410336111040
  rows := #[⟨.count 2, 63494848928258514109062720⟩, ⟨.count 3, 4006667962765500642529920⟩, ⟨.count 4, 184134246107315038254720⟩, ⟨.count 5, 4767572540177892244800⟩, ⟨.count 6, 317838169345192816320⟩, ⟨.path 4, 105930773182552566568320⟩, ⟨.path 5, 2832460913757453778800⟩, ⟨.privateRow 2 37, 4920055401921248498429520⟩, ⟨.privateRow 2 38, 7734221039817697793528160⟩, ⟨.privateRow 3 32, 34767964191149147518560⟩, ⟨.privateRow 3 33, 471756600153424857503232⟩, ⟨.privateRow 3 34, 895614988186529157587040⟩, ⟨.privateRow 3 35, 1917093891433754670436800⟩, ⟨.privateRow 3 36, 2355869484214793353366560⟩, ⟨.privateRow 3 37, 3625579997720614455762240⟩, ⟨.privateRow 4 29, 35872672550574626716950⟩, ⟨.privateRow 4 30, 108466059076777348483680⟩, ⟨.privateRow 4 31, 182240460348299931057480⟩, ⟨.privateRow 4 32, 418147895590535669150592⟩, ⟨.privateRow 4 33, 618830915715090413375040⟩, ⟨.privateRow 4 34, 856865218040527733397360⟩, ⟨.privateRow 4 35, 1247859139363339096273680⟩, ⟨.privateRow 5 25, 529730282241988027200⟩, ⟨.privateRow 5 26, 9725847981962900179392⟩, ⟨.privateRow 5 27, 21836659412419728676800⟩, ⟨.privateRow 5 28, 40113825622774543359720⟩, ⟨.privateRow 5 29, 92309285468396713654080⟩, ⟨.privateRow 5 30, 156517640726432729103360⟩, ⟨.privateRow 5 31, 231661647030066204055104⟩, ⟨.privateRow 5 32, 319983576988272867830160⟩, ⟨.privateRow 5 33, 493355469528038182665600⟩, ⟨.privateRow 5 34, 429399366785355494848320⟩, ⟨.privateRow 6 22, 73347269848890649920⟩, ⟨.privateRow 6 23, 2216038347378983247120⟩, ⟨.privateRow 6 24, 5003543302267505093280⟩, ⟨.privateRow 6 25, 9068982431982835025664⟩, ⟨.privateRow 6 26, 22107410445565633668480⟩, ⟨.privateRow 6 27, 40537609848568133781480⟩, ⟨.privateRow 6 28, 64960067753788931792640⟩, ⟨.privateRow 6 29, 96154875064958193403920⟩, ⟨.privateRow 6 30, 132072353968572454941504⟩, ⟨.privateRow 6 31, 205085078769985664730480⟩, ⟨.privateRow 6 32, 151679437481955905121600⟩, ⟨.privateRow 7 20, 491892404938988882400⟩, ⟨.privateRow 7 21, 1339266816129744089280⟩, ⟨.privateRow 7 22, 2460302866412788837440⟩, ⟨.privateRow 7 23, 5772454833158148320640⟩, ⟨.privateRow 7 24, 11650534674108790011552⟩, ⟨.privateRow 7 25, 19906086828248927866560⟩, ⟨.privateRow 7 26, 30984807092137616357640⟩, ⟨.privateRow 7 27, 45203650751316311654400⟩, ⟨.privateRow 7 28, 61913698210038578423520⟩, ⟨.privateRow 7 29, 96580425058359257119104⟩, ⟨.privateRow 7 30, 494414930092522158720⟩, ⟨.privateRow 8 17, 112015882599087051585⟩, ⟨.privateRow 8 18, 405832255117611938616⟩, ⟨.privateRow 8 19, 845361242077839226740⟩, ⟨.privateRow 8 20, 1908726869539881218520⟩, ⟨.privateRow 8 21, 3821415397173452518440⟩, ⟨.privateRow 8 22, 7104405444340843973880⟩, ⟨.privateRow 8 23, 11606390483921957675952⟩, ⟨.privateRow 8 24, 17586064388429850673360⟩, ⟨.privateRow 8 25, 24917739953334847233615⟩, ⟨.privateRow 8 26, 34803279543298613387040⟩, ⟨.privateRow 9 14, 29429460124554890400⟩, ⟨.privateRow 9 15, 135029287630310673600⟩, ⟨.privateRow 9 16, 344324683457292217680⟩, ⟨.privateRow 9 17, 845214094777216452288⟩, ⟨.privateRow 9 18, 1649731450410762713280⟩, ⟨.privateRow 9 19, 3064285940353653818880⟩, ⟨.privateRow 9 20, 5326732282544435162400⟩, ⟨.privateRow 9 21, 8411474784690961401600⟩, ⟨.privateRow 9 22, 12423940886182092531264⟩, ⟨.privateRow 9 23, 5207052478037911941440⟩, ⟨.privateRow 10 11, 10594605644839760544⟩, ⟨.privateRow 10 12, 52973028224198802720⟩, ⟨.privateRow 10 13, 155976138660140919120⟩, ⟨.privateRow 10 14, 458060891115130823520⟩, ⟨.privateRow 10 15, 983311836411690275490⟩, ⟨.privateRow 10 16, 1794019889192866118784⟩, ⟨.privateRow 10 17, 3121624877497429446000⟩, ⟨.privateRow 10 18, 5138383737747283863840⟩, ⟨.privateRow 10 19, 1509731304389665877520⟩, ⟨.privateRow 11 8, 4815729838563527520⟩, ⟨.privateRow 11 9, 25225251535332763200⟩, ⟨.privateRow 11 10, 84756845158718084352⟩, ⟨.privateRow 11 11, 284381519940435677760⟩, ⟨.privateRow 11 12, 735736503113872260000⟩, ⟨.privateRow 11 13, 1470780548342460875520⟩, ⟨.privateRow 11 14, 1993110186935479952340⟩, ⟨.privateRow 12 6, 12667463271004061520⟩, ⟨.privateRow 12 7, 52973028224198802720⟩, ⟨.privateRow 12 8, 208108325166495296400⟩, ⟨.privateRow 12 9, 640973641512805512912⟩, ⟨.privateRow 12 10, 659374798685421939120⟩, ⟨.privateRow 13 5, 253349265420081230400⟩, ⟨.privateRow 13 6, 211892112896795210880⟩, ⟨.hall 4 35, 24376421821168815718320⟩, ⟨.hall 3 36, 354441100144648670112960⟩, ⟨.assumptionRow 21, 64543414907949120⟩]
  caps := #[0, 123135449251162573265040, 3228126086653613217072, 1323351572833271086560, 502773589964111896716, 0, 85695778754384130504, 140125494041889439536, 3782495674654482240, 42178280615566002648, 1456688549906317637442, 0, 0, 8554733880285313543680, 55012858624705714761600, 19727678404708267593600] }

theorem case_55_40_21_checked :
    (Witness.linear .conditional case_55_40_21).check 55 40 21 = true := by
  change case_55_40_21.check 55 40 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_22 : Certificate := {
  objectiveScale := 1906806012384000000
  eta := 22776788577965776074069148800
  rows := #[⟨.count 2, 1781370636359970434011833600⟩, ⟨.count 3, 120130114485709076856307200⟩, ⟨.count 4, 6165001024732256660553600⟩, ⟨.count 5, 169513690317436168704000⟩, ⟨.path 4, 2106906485205148686259200⟩, ⟨.path 5, 171020057828331151440000⟩, ⟨.privateRow 2 37, 142185434786854248368779200⟩, ⟨.privateRow 2 38, 227027036790731050805131200⟩, ⟨.privateRow 3 32, 429258105376757631374400⟩, ⟨.privateRow 3 33, 13287966291870924469495680⟩, ⟨.privateRow 3 34, 25481615766686350072401600⟩, ⟨.privateRow 3 35, 55422854202807250016457600⟩, ⟨.privateRow 3 36, 69434926475150822653267200⟩, ⟨.privateRow 3 37, 108802362130246404882662400⟩, ⟨.privateRow 4 29, 937423950712478062633800⟩, ⟨.privateRow 4 30, 3047954530388490111074400⟩, ⟨.privateRow 4 31, 5103509827499686318716000⟩, ⟨.privateRow 4 32, 11838783158741517823484640⟩, ⟨.privateRow 4 33, 17828536162851068794939800⟩, ⟨.privateRow 4 34, 25204831694214911328189600⟩, ⟨.privateRow 4 35, 37667398746810482153103600⟩, ⟨.privateRow 5 25, 36503232176311538601600⟩, ⟨.privateRow 5 26, 270586228169207484293760⟩, ⟨.privateRow 5 27, 610484720823766646457600⟩, ⟨.privateRow 5 28, 1116141704683868773310400⟩, ⟨.privateRow 5 29, 2562078347940678092697600⟩, ⟨.privateRow 5 30, 4394642421479532673651200⟩, ⟨.privateRow 5 31, 6619721499008779183102080⟩, ⟨.privateRow 5 32, 9370663827719647207154400⟩, ⟨.privateRow 5 33, 14920736283149329432800000⟩, ⟨.privateRow 5 34, 13764511653775816898764800⟩, ⟨.privateRow 6 20, 70630704298931736960⟩, ⟨.privateRow 6 21, 643243914150985461600⟩, ⟨.privateRow 6 22, 13691490371792921318400⟩, ⟨.privateRow 6 23, 67143313274171982447600⟩, ⟨.privateRow 6 24, 142401131326323508766400⟩, ⟨.privateRow 6 25, 253211074911670277001600⟩, ⟨.privateRow 6 26, 609307542418784450841600⟩, ⟨.privateRow 6 27, 1113757918413779827188000⟩, ⟨.privateRow 6 28, 1804261341316211220643200⟩, ⟨.privateRow 6 29, 2719988422551861190329600⟩, ⟨.privateRow 6 30, 3834611567093302931295360⟩, ⟨.privateRow 6 31, 6175198332665414930077200⟩, ⟨.privateRow 6 32, 5901195344175746623008000⟩, ⟨.privateRow 7 17, 20773736558509334400⟩, ⟨.privateRow 7 18, 286937236214410181400⟩, ⟨.privateRow 7 19, 4755800756128070288640⟩, ⟨.privateRow 7 20, 18591010381540246478400⟩, ⟨.privateRow 7 21, 40558323660886570492800⟩, ⟨.privateRow 7 22, 70660133759056291850400⟩, ⟨.privateRow 7 23, 160524327952117584000000⟩, ⟨.privateRow 7 24, 318367899627434804347200⟩, ⟨.privateRow 7 25, 542012176933968934793600⟩, ⟨.privateRow 7 26, 851055842611940598032400⟩, ⟨.privateRow 7 27, 1263633750410959439740800⟩, ⟨.privateRow 7 28, 1775538188234645647612800⟩, ⟨.privateRow 7 29, 2874245880740728103850240⟩, ⟨.privateRow 7 30, 1037300181010186221928800⟩, ⟨.privateRow 8 14, 16263649016201386800⟩, ⟨.privateRow 8 15, 137337480581256155200⟩, ⟨.privateRow 8 16, 1854055987846958095200⟩, ⟨.privateRow 8 17, 6431256707844135892725⟩, ⟨.privateRow 8 18, 14482237327293461565840⟩, ⟨.privateRow 8 19, 25912639639670580997200⟩, ⟨.privateRow 8 20, 54956121075668809180800⟩, ⟨.privateRow 8 21, 105938699083366466717400⟩, ⟨.privateRow 8 22, 193299382611741191713200⟩, ⟨.privateRow 8 23, 314077084341274701326880⟩, ⟨.privateRow 8 24, 478415113604805816639200⟩, ⟨.privateRow 8 25, 695464126274676677168250⟩, ⟨.privateRow 8 26, 966846053472001814311200⟩, ⟨.privateRow 8 27, 562808995421987724009600⟩, ⟨.privateRow 9 11, 16816834356888508800⟩, ⟨.privateRow 9 12, 88288380373664671200⟩, ⟨.privateRow 9 13, 855003262566015763200⟩, ⟨.privateRow 9 14, 2903706732289415852800⟩, ⟨.privateRow 9 15, 6668369435281496342400⟩, ⟨.privateRow 9 16, 12426589537593302471400⟩, ⟨.privateRow 9 17, 26039186318206167025920⟩, ⟨.privateRow 9 18, 47600049647172924158400⟩, ⟨.privateRow 9 19, 85109998680212743036800⟩, ⟨.privateRow 9 20, 144910661653308280329600⟩, ⟨.privateRow 9 21, 227045609455475110809600⟩, ⟨.privateRow 9 22, 335778368237121477507840⟩, ⟨.privateRow 9 23, 367750533716437910438400⟩, ⟨.privateRow 10 9, 72235947578452912800⟩, ⟨.privateRow 10 10, 479279779171322500800⟩, ⟨.privateRow 10 11, 1668650389062262285680⟩, ⟨.privateRow 10 12, 4014797928570856627200⟩, ⟨.privateRow 10 13, 7769377472882491065600⟩, ⟨.privateRow 10 14, 16577441773690448851200⟩, ⟨.privateRow 10 15, 30426383086274187312300⟩, ⟨.privateRow 10 16, 52090144420462156008000⟩, ⟨.privateRow 10 17, 87254145060716027908800⟩, ⟨.privateRow 10 18, 140419273277376210902400⟩, ⟨.privateRow 10 19, 115790210860061216278800⟩, ⟨.privateRow 11 6, 44144190186832335600⟩, ⟨.privateRow 11 7, 368508022429209062400⟩, ⟨.privateRow 11 8, 1252089758026517155200⟩, ⟨.privateRow 11 9, 3127931190381262636800⟩, ⟨.privateRow 11 10, 6409736415128055129120⟩, ⟨.privateRow 11 11, 12936571103172760243200⟩, ⟨.privateRow 11 12, 28664294161316463249600⟩, ⟨.privateRow 11 13, 44808949756704634300800⟩, ⟨.privateRow 11 14, 64627094433522539318400⟩, ⟨.privateRow 12 3, 112058328935805159600⟩, ⟨.privateRow 12 4, 349621986279712097952⟩, ⟨.privateRow 12 5, 1213965230137889229000⟩, ⟨.privateRow 12 6, 3293540450461055995200⟩, ⟨.privateRow 12 7, 7018926239706341360400⟩, ⟨.privateRow 12 8, 15954971596097972724000⟩, ⟨.privateRow 12 9, 29135165523309341496000⟩, ⟨.privateRow 13 3, 10255578264204888206592⟩, ⟨.privateRow 13 4, 7769377472882491065600⟩, ⟨.privateRow 13 5, 1520095592520487382400⟩, ⟨.privateRow 14 0, 5611217063748465769600⟩, ⟨.hall 4 35, 1266084804018475939898400⟩, ⟨.hall 3 36, 11244599018185335042240000⟩, ⟨.assumptionRow 22, 596568937287435840⟩]
  caps := #[0, 905110459257766006627200, 37547527348525343909760, 0, 0, 1905608781433508511360, 4063499901753476145600, 32685668446704524160, 1059298870121047574620, 2507401046597487884480, 0, 770402804198192665632, 12206538622894640878872, 3835492967690226146304, 391279445175970062712000, 964633733330770478976000] }

theorem case_55_40_22_checked :
    (Witness.linear .conditional case_55_40_22).check 55 40 22 = true := by
  change case_55_40_22.check 55 40 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_23 : Certificate := {
  objectiveScale := 2711037119648000000
  eta := 48658779789273443117308780800
  rows := #[⟨.count 2, 3511987814378335995137635200⟩, ⟨.count 3, 214912634966139026611094400⟩, ⟨.count 4, 9544680225436140274089600⟩, ⟨.count 5, 174810993139856048976000⟩, ⟨.path 2, 79099154863637445128592000⟩, ⟨.path 4, 5593698339383490912576000⟩, ⟨.path 5, 168028617872918098296000⟩, ⟨.privateRow 3 33, 24508501238207818066435200⟩, ⟨.privateRow 3 34, 50371787673249520512434400⟩, ⟨.privateRow 3 35, 95889656770315704731635200⟩, ⟨.privateRow 4 29, 1390839964168979689665300⟩, ⟨.privateRow 4 30, 5319248791255619775984000⟩, ⟨.privateRow 4 31, 9225650162955902984708400⟩, ⟨.privateRow 4 32, 23064562434872607101893440⟩, ⟨.privateRow 4 33, 35674553425016123194777200⟩, ⟨.privateRow 4 34, 54587646124472382226905600⟩, ⟨.privateRow 4 35, 60108759991139502440397600⟩, ⟨.privateRow 5 24, 7416223951387832380800⟩, ⟨.privateRow 5 25, 52009882256486097216000⟩, ⟨.privateRow 5 26, 400793931544288141379520⟩, ⟨.privateRow 5 27, 995186623571948173766400⟩, ⟨.privateRow 5 28, 1891137107603897257104000⟩, ⟨.privateRow 5 29, 4573237202349688637107200⟩, ⟨.privateRow 5 30, 8446549350348499093704000⟩, ⟨.privateRow 5 31, 13463624853462367699315200⟩, ⟨.privateRow 5 32, 20556183602400345395496000⟩, ⟨.privateRow 5 33, 35825658988025650279536000⟩, ⟨.privateRow 5 34, 32889893763840552632793600⟩, ⟨.privateRow 6 20, 211892112896795210880⟩, ⟨.privateRow 6 21, 3972977116814910204000⟩, ⟨.privateRow 6 23, 137597440812356390065200⟩, ⟨.privateRow 6 24, 199226743421373133502400⟩, ⟨.privateRow 6 25, 404131232322412665950880⟩, ⟨.privateRow 6 26, 1017082141904617012224000⟩, ⟨.privateRow 6 27, 1964835833120813841388200⟩, ⟨.privateRow 6 28, 3394057594079023288560000⟩, ⟨.privateRow 6 29, 5460724614491533578391200⟩, ⟨.privateRow 6 30, 8362322235472022997379200⟩, ⟨.privateRow 6 31, 15137837410488170859280800⟩, ⟨.privateRow 6 32, 20071480394148926350608000⟩, ⟨.privateRow 6 33, 18351181302568070232276000⟩, ⟨.privateRow 7 17, 124642419351056006400⟩, ⟨.privateRow 7 18, 1787839702566709591800⟩, ⟨.privateRow 7 19, 635676338690385632640⟩, ⟨.privateRow 7 20, 31405438161489290184000⟩, ⟨.privateRow 7 21, 71228348719922697811200⟩, ⟨.privateRow 7 22, 98706409257757102401600⟩, ⟨.privateRow 7 23, 253211074911670277001600⟩, ⟨.privateRow 7 24, 525280547871155327771520⟩, ⟨.privateRow 7 25, 937740317408817027705600⟩, ⟨.privateRow 7 26, 1551050266404540943641600⟩, ⟨.privateRow 7 27, 2436002540767084942224000⟩, ⟨.privateRow 7 28, 3647899300279076884641600⟩, ⟨.privateRow 7 29, 6514411118899071963294720⟩, ⟨.privateRow 7 30, 9008328314666127396549600⟩, ⟨.privateRow 7 31, 9753747110160978215491200⟩, ⟨.privateRow 8 14, 97581894097208320800⟩, ⟨.privateRow 8 15, 927027993923479047600⟩, ⟨.privateRow 8 16, 708903760059131036400⟩, ⟨.privateRow 8 17, 8111494946830441666500⟩, ⟨.privateRow 8 18, 24720746504626107936000⟩, ⟨.privateRow 8 19, 45093290275849230815400⟩, ⟨.privateRow 8 20, 76087605347411703368400⟩, ⟨.privateRow 8 21, 164470216588590574361700⟩, ⟨.privateRow 8 22, 310807203780890066140800⟩, ⟨.privateRow 8 23, 522565680174665139132120⟩, ⟨.privateRow 8 24, 825260920812768236596800⟩, ⟨.privateRow 8 25, 1248243193817964537593400⟩, ⟨.privateRow 8 26, 1817504598372260921323200⟩, ⟨.privateRow 8 27, 3184804673124112268029800⟩, ⟨.privateRow 8 28, 4608626968991183737238640⟩, ⟨.privateRow 8 29, 5607592335243124758932400⟩, ⟨.privateRow 9 11, 50450503070665526400⟩, ⟨.privateRow 9 12, 529730282241988027200⟩, ⟨.privateRow 9 13, 669132988095142771200⟩, ⟨.privateRow 9 14, 2707510331459049916800⟩, ⟨.privateRow 9 15, 9348181451329200480000⟩, ⟨.privateRow 9 16, 21255427574959769591400⟩, ⟨.privateRow 9 17, 45274281455615243391360⟩, ⟨.privateRow 9 18, 65913582261824510241600⟩, ⟨.privateRow 9 19, 130558140331025356857600⟩, ⟨.privateRow 9 20, 230874114677133115188000⟩, ⟨.privateRow 9 21, 372930118698359571148800⟩, ⟨.privateRow 9 22, 569671945523033924450880⟩, ⟨.privateRow 9 23, 838975049230810815523200⟩, ⟨.privateRow 9 24, 1199309358995860893580800⟩, ⟨.privateRow 9 25, 2024931841747302233116800⟩, ⟨.privateRow 9 26, 3006219351723282054360000⟩, ⟨.privateRow 9 27, 3988233348943479459183360⟩, ⟨.privateRow 10 8, 69095254205476699200⟩, ⟨.privateRow 10 9, 361179737892264564000⟩, ⟨.privateRow 10 10, 681081791453984606400⟩, ⟨.privateRow 10 11, 1509731304389665877520⟩, ⟨.privateRow 10 12, 4265722799106535166400⟩, ⟨.privateRow 10 13, 10859470785960754557600⟩, ⟨.privateRow 10 14, 28324989797527477454400⟩, ⟨.privateRow 10 15, 52840595653638305713200⟩, ⟨.privateRow 10 16, 73632509231636335780800⟩, ⟨.privateRow 10 17, 131335272118710031600800⟩, ⟨.privateRow 10 18, 221019773144657158425600⟩, ⟨.privateRow 10 19, 344986846310094702714000⟩, ⟨.privateRow 10 20, 511719452645760434275200⟩, ⟨.privateRow 10 21, 733252656679359827250240⟩, ⟨.privateRow 10 23, 3731420108112563663596800⟩, ⟨.privateRow 10 24, 1465915042472792867841600⟩, ⟨.privateRow 10 25, 3508668524429807698159200⟩, ⟨.privateRow 11 6, 397297711681491020400⟩, ⟨.privateRow 11 8, 3033909798295022337600⟩, ⟨.privateRow 11 9, 1967569619755955529600⟩, ⟨.privateRow 11 10, 6674601556249049142720⟩, ⟨.privateRow 11 11, 19237573407735354672000⟩, ⟨.privateRow 11 12, 44673920469074323627200⟩, ⟨.privateRow 11 13, 78524724191165284032000⟩, ⟨.privateRow 11 14, 107667679865684066528400⟩, ⟨.privateRow 11 15, 172692072010888096867200⟩, ⟨.privateRow 11 16, 277881370913225719411200⟩, ⟨.privateRow 11 17, 422969256128602747872000⟩, ⟨.privateRow 11 19, 2083573671952895816803200⟩, ⟨.privateRow 11 20, 556852472692777814192640⟩, ⟨.privateRow 11 23, 14130630954559636623849600⟩, ⟨.privateRow 12 3, 672349973614830957600⟩, ⟨.privateRow 12 4, 349621986279712097952⟩, ⟨.privateRow 12 5, 1456758276165467074800⟩, ⟨.privateRow 12 6, 6460406268212071375200⟩, ⟨.privateRow 12 9, 90464688949875505345080⟩, ⟨.privateRow 12 11, 298149860521865594642400⟩, ⟨.privateRow 12 12, 153216693987285595867200⟩, ⟨.privateRow 12 14, 1152587148102117549581760⟩, ⟨.privateRow 12 15, 415800433682657602207200⟩, ⟨.privateRow 12 16, 753031970448610672512000⟩, ⟨.privateRow 12 17, 540457320457388284750800⟩, ⟨.privateRow 12 18, 4715129242235935430107200⟩, ⟨.privateRow 12 22, 30519502102316868207652800⟩, ⟨.privateRow 13 3, 19578831231663877485312⟩, ⟨.privateRow 13 4, 13110824485489203673200⟩, ⟨.privateRow 13 7, 8324333006659811856000⟩, ⟨.privateRow 13 10, 3884688736441245532800⟩, ⟨.privateRow 13 12, 4370274828496401224400⟩, ⟨.privateRow 13 15, 26893998944593238304000⟩, ⟨.privateRow 13 16, 16123400600599389583886400⟩, ⟨.privateRow 13 17, 28605435241067353468800⟩, ⟨.privateRow 13 20, 85058658987025457030497200⟩, ⟨.privateRow 13 22, 41092237454075495245958400⟩, ⟨.privateRow 14 0, 8416825595622698654400⟩, ⟨.privateRow 14 1, 113627145540906431834400⟩, ⟨.privateRow 14 3, 123096074335981967820600⟩, ⟨.privateRow 14 6, 10821632908657755412800⟩, ⟨.privateRow 14 8, 11960752162200677035200⟩, ⟨.privateRow 14 9, 12625238393434047981600⟩, ⟨.privateRow 14 15, 96980768719163639570660400⟩, ⟨.privateRow 14 19, 340256487322244310128110800⟩, ⟨.privateRow 14 21, 429131852992823290894584000⟩, ⟨.privateRow 15 0, 3059192379947480857080000⟩, ⟨.privateRow 15 13, 244735390395798468566400⟩, ⟨.privateRow 15 25, 79268569272247144976314128000⟩, ⟨.hall 12 2, 184985177925773596800⟩, ⟨.hall 14 2, 39157662463327754970624⟩, ⟨.hall 14 3, 7342061711873954056992⟩, ⟨.hall 13 5, 67559804112021661440⟩, ⟨.hall 10 7, 1470692383943273568⟩, ⟨.hall 12 11, 283290098214087360⟩, ⟨.hall 11 14, 456305458740751620⟩, ⟨.hall 7 15, 22260470502386025⟩, ⟨.hall 8 16, 32202588597379200⟩, ⟨.hall 6 20, 18843049002588720⟩, ⟨.hall 9 21, 557640808461011520⟩, ⟨.hall 12 23, 555311274504101124240⟩, ⟨.hall 10 24, 12118826414003899392⟩, ⟨.hall 13 26, 3652902308500251216009600⟩, ⟨.hall 4 28, 3852326536162944840⟩, ⟨.hall 5 28, 4951404488580170400⟩, ⟨.hall 3 31, 132943893226753752000⟩]
  caps := #[0, 0, 112584157546218656812800, 60545716255371617899200, 0, 0, 16233578641512003200, 14868549978863381862480, 0, 910762524311940470560, 26896678275220339922640, 1215119770496621767008, 220317937676237003495112, 140801441212559050650144, 0, 0] }

theorem case_55_40_23_checked :
    (Witness.linear .conditional case_55_40_23).check 55 40 23 = true := by
  change case_55_40_23.check 55 40 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_24 : Certificate := {
  objectiveScale := 45
  eta := 2425995
  rows := #[⟨.assumptionRow 24, 17⟩]
  caps := #[0, 0, 1193400, 508300, 285890, 131054, 63448, 34713, 14478, 8313, 4420, 164812365, 163809450, 117341055, 71466980, 38816525] }

theorem case_55_40_24_checked :
    (Witness.linear .conditional case_55_40_24).check 55 40 24 = true := by
  change case_55_40_24.check 55 40 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640] }

theorem case_55_40_25_checked :
    (Witness.linear .negative case_55_40_25).check 55 40 25 = true := by
  change case_55_40_25.check 55 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900] }

theorem case_55_40_26_checked :
    (Witness.linear .negative case_55_40_26).check 55 40 26 = true := by
  change case_55_40_26.check 55 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_41_1_checked :
    (Witness.rising).check 55 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_41_2_checked :
    (Witness.rising).check 55 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_41_3_checked :
    (Witness.rising).check 55 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_41_4_checked :
    (Witness.rising).check 55 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_41_5_checked :
    (Witness.rising).check 55 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_41_6_checked :
    (Witness.rising).check 55 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_41_7_checked :
    (Witness.rising).check 55 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_41_8_checked :
    (Witness.rising).check 55 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_41_9_checked :
    (Witness.rising).check 55 41 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_55_41_10_checked :
    (Witness.linear .positive case_55_41_10).check 55 41 10 = true := by
  change case_55_41_10.check 55 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_55_41_11_checked :
    (Witness.linear .positive case_55_41_11).check 55 41 11 = true := by
  change case_55_41_11.check 55 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_55_41_12_checked :
    (Witness.linear .positive case_55_41_12).check 55 41 12 = true := by
  change case_55_41_12.check 55 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_55_41_13_checked :
    (Witness.linear .positive case_55_41_13).check 55 41 13 = true := by
  change case_55_41_13.check 55 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_55_41_14_checked :
    (Witness.linear .positive case_55_41_14).check 55 41 14 = true := by
  change case_55_41_14.check 55 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_55_41_15_checked :
    (Witness.linear .positive case_55_41_15).check 55 41 15 = true := by
  change case_55_41_15.check 55 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_55_41_16_checked :
    (Witness.linear .positive case_55_41_16).check 55 41 16 = true := by
  change case_55_41_16.check 55 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_55_41_17_checked :
    (Witness.linear .positive case_55_41_17).check 55 41 17 = true := by
  change case_55_41_17.check 55 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_55_41_18_checked :
    (Witness.linear .positive case_55_41_18).check 55 41 18 = true := by
  change case_55_41_18.check 55 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_55_41_19_checked :
    (Witness.linear .positive case_55_41_19).check 55 41 19 = true := by
  change case_55_41_19.check 55 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_20 : Certificate := {
  objectiveScale := 3
  eta := 354817320
  rows := #[⟨.assumptionRow 20, 5⟩]
  caps := #[0, 0, 99249600, 28514250, 8259300, 2414425, 713184, 213180, 64600, 19890, 6240, 4942470, 3511755, 1735695, 699660] }

theorem case_55_41_20_checked :
    (Witness.linear .conditional case_55_41_20).check 55 41 20 = true := by
  change case_55_41_20.check 55 41 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_21 : Certificate := {
  objectiveScale := 593
  eta := 70526765760
  rows := #[⟨.assumptionRow 21, 745⟩]
  caps := #[0, 0, 20328799320, 5887142100, 1713758865, 508989195, 158646295, 49685152, 15662270, 4978722, 3435276780, 2852585580, 1675367265, 819257010, 348847785] }

theorem case_55_41_21_checked :
    (Witness.linear .conditional case_55_41_21).check 55 41 21 = true := by
  change case_55_41_21.check 55 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_22 : Certificate := {
  objectiveScale := 1122543864000000
  eta := 51505428611589950821824000
  rows := #[⟨.count 2, 2058299155737715042152000⟩, ⟨.count 3, 62370020837062198260000⟩, ⟨.count 4, 2268000757711352664000⟩, ⟨.path 2, 980644581129752170632000⟩, ⟨.path 4, 2265218101247092992000⟩, ⟨.privateRow 2 38, 146149325422449292944000⟩, ⟨.privateRow 2 39, 216127604120486454396000⟩, ⟨.privateRow 3 33, 7362513098023575492000⟩, ⟨.privateRow 3 34, 14665064473887012385200⟩, ⟨.privateRow 3 35, 26791094056960287054000⟩, ⟨.privateRow 3 36, 56673657231849031374000⟩, ⟨.privateRow 3 37, 65024064276937185420000⟩, ⟨.privateRow 3 38, 93790946228026629582000⟩, ⟨.privateRow 4 28, 36995757040681639200⟩, ⟨.privateRow 4 29, 432510782794442352000⟩, ⟨.privateRow 4 30, 2355463552889051104500⟩, ⟨.privateRow 4 31, 3524362879574252430000⟩, ⟨.privateRow 4 32, 5688767857994669448000⟩, ⟨.privateRow 4 33, 12835114926353006086800⟩, ⟨.privateRow 4 34, 18382266779588689477500⟩, ⟨.privateRow 4 35, 24461433704181131658000⟩, ⟨.privateRow 4 36, 33658096351141882620000⟩, ⟨.privateRow 5 23, 114893655405843600⟩, ⟨.privateRow 5 24, 7176434476118846400⟩, ⟨.privateRow 5 25, 21580858273730956200⟩, ⟨.privateRow 5 26, 174450348417127255200⟩, ⟨.privateRow 5 27, 592092963768474408240⟩, ⟨.privateRow 5 28, 880391783489844225600⟩, ⟨.privateRow 5 29, 1347128109633516210000⟩, ⟨.privateRow 5 30, 2998954193403329647200⟩, ⟨.privateRow 5 31, 4947780376397248790400⟩, ⟨.privateRow 5 32, 7090638964640556605280⟩, ⟨.privateRow 5 33, 9469305291238817824800⟩, ⟨.privateRow 5 34, 14025681281553492751200⟩, ⟨.privateRow 5 35, 7182806655007124341200⟩, ⟨.privateRow 6 20, 726064072356372750⟩, ⟨.privateRow 6 21, 2382979519528608000⟩, ⟨.privateRow 6 22, 10276599177967122000⟩, ⟨.privateRow 6 23, 61590855273970176000⟩, ⟨.privateRow 6 24, 162787288427798034000⟩, ⟨.privateRow 6 25, 263292157595189268000⟩, ⟨.privateRow 6 26, 378178849749190089600⟩, ⟨.privateRow 6 27, 789163384217224016000⟩, ⟨.privateRow 6 28, 1388457910675340505000⟩, ⟨.privateRow 6 29, 2155021996562273124000⟩, ⟨.privateRow 6 30, 3096532949407455558000⟩, ⟨.privateRow 6 31, 4128512017583313360000⟩, ⟨.privateRow 6 32, 6234991444736617563000⟩, ⟨.privateRow 6 33, 263021364467970108000⟩, ⟨.privateRow 7 16, 70548735775518000⟩, ⟨.privateRow 7 17, 335106494933710500⟩, ⟨.privateRow 7 18, 1458698860299681000⟩, ⟨.privateRow 7 19, 5110374047739085125⟩, ⟨.privateRow 7 20, 24440433697165285800⟩, ⟨.privateRow 7 21, 56872359425892582000⟩, ⟨.privateRow 7 22, 97026218994652794000⟩, ⟨.privateRow 7 23, 141135685449581072250⟩, ⟨.privateRow 7 24, 261200280687421257000⟩, ⟨.privateRow 7 25, 451857597768615238200⟩, ⟨.privateRow 7 26, 738202374283971597000⟩, ⟨.privateRow 7 27, 1109034944983114899750⟩, ⟨.privateRow 7 28, 1570500524685043809000⟩, ⟨.privateRow 7 29, 2095979423645381274000⟩, ⟨.privateRow 7 30, 738574714833897942000⟩, ⟨.privateRow 8 13, 63829808558802000⟩, ⟨.privateRow 8 14, 301595845440339450⟩, ⟨.privateRow 8 15, 1058231036632770000⟩, ⟨.privateRow 8 16, 3090426564388663500⟩, ⟨.privateRow 8 17, 11906136643527126000⟩, ⟨.privateRow 8 18, 26724742970963412375⟩, ⟨.privateRow 8 19, 46512781496799017400⟩, ⟨.privateRow 8 20, 70085129797564596000⟩, ⟨.privateRow 8 21, 123628519207851966000⟩, ⟨.privateRow 8 22, 193859107319151524250⟩, ⟨.privateRow 8 23, 312989466268085607000⟩, ⟨.privateRow 8 24, 482553352704543120000⟩, ⟨.privateRow 8 25, 703649171250806781000⟩, ⟨.privateRow 8 26, 701210340648789221250⟩, ⟨.privateRow 9 10, 77705853897672000⟩, ⟨.privateRow 9 11, 284332783580118000⟩, ⟨.privateRow 9 12, 936170525529096000⟩, ⟨.privateRow 9 13, 2412766763522715600⟩, ⟨.privateRow 9 14, 7525198482721920000⟩, ⟨.privateRow 9 15, 16829792856670794000⟩, ⟨.privateRow 9 16, 30015028801121364000⟩, ⟨.privateRow 9 17, 46523951713296807750⟩, ⟨.privateRow 9 18, 81974495471784115200⟩, ⟨.privateRow 9 19, 124340467072546296000⟩, ⟨.privateRow 9 20, 184360127058915192000⟩, ⟨.privateRow 9 21, 278734135674861867000⟩, ⟨.privateRow 9 22, 185222499017905440000⟩, ⟨.privateRow 10 7, 128680894054544832⟩, ⟨.privateRow 10 8, 335106494933710500⟩, ⟨.privateRow 10 9, 1049029027618572000⟩, ⟨.privateRow 10 10, 2485880907871888800⟩, ⟨.privateRow 10 11, 6434044702727241600⟩, ⟨.privateRow 10 12, 14235323904784022040⟩, ⟨.privateRow 10 13, 26244129708492696000⟩, ⟨.privateRow 10 14, 42000014031691716000⟩, ⟨.privateRow 10 15, 74464605603622634400⟩, ⟨.privateRow 10 16, 114807485164289217300⟩, ⟨.privateRow 10 17, 55654486678590639840⟩, ⟨.privateRow 11 4, 297872439941076000⟩, ⟨.privateRow 11 5, 463993608369753000⟩, ⟨.privateRow 11 6, 1608511175681810400⟩, ⟨.privateRow 11 7, 3518618196803960250⟩, ⟨.privateRow 11 8, 7867717707139290000⟩, ⟨.privateRow 11 9, 16816253200309836000⟩, ⟨.privateRow 11 10, 27000009020373246000⟩, ⟨.privateRow 11 11, 61324488572869021500⟩, ⟨.privateRow 12 1, 508437440589078000⟩, ⟨.privateRow 12 2, 1579787761830349500⟩, ⟨.privateRow 12 3, 3276596839351836000⟩, ⟨.privateRow 12 5, 29489371554166524000⟩, ⟨.privateRow 12 6, 6143619073784692500⟩, ⟨.privateRow 13 0, 15253123217672340000⟩, ⟨.hall 3 37, 6189275863954081899000⟩, ⟨.assumptionRow 22, 515815141862800⟩]
  caps := #[0, 178675859760206484000, 81241954584913980000, 4022529072007500600, 4098318388807042400, 6215827102669709280, 8732786977429189750, 1234460865790513325, 7338455059451959575, 4088106292194908400, 290723501382490176, 761139120206206500, 136640587580271606000, 0, 2081946095879366574000] }

theorem case_55_41_22_checked :
    (Witness.linear .conditional case_55_41_22).check 55 41 22 = true := by
  change case_55_41_22.check 55 41 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_23 : Certificate := {
  objectiveScale := 804
  eta := 21099709800
  rows := #[⟨.assumptionRow 23, 611⟩]
  caps := #[0, 0, 7257627000, 2366532675, 848544060, 307653060, 104311900, 36461095, 14048562, 4984536, 7583289750, 7276286325, 5007502500, 2916155970, 1507381590] }

theorem case_55_41_23_checked :
    (Witness.linear .conditional case_55_41_23).check 55 41 23 = true := by
  change case_55_41_23.check 55 41 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_24 : Certificate := {
  objectiveScale := 5
  eta := 32957340
  rows := #[⟨.assumptionRow 24, 3⟩]
  caps := #[0, 0, 11219520, 4942470, 1776060, 740025, 284625, 110561, 46398, 16473, 7752, 28514250, 27943965, 19684665, 11759670] }

theorem case_55_41_24_checked :
    (Witness.linear .conditional case_55_41_24).check 55 41 24 = true := by
  change case_55_41_24.check 55 41 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405, 4345965] }

theorem case_55_41_25_checked :
    (Witness.linear .negative case_55_41_25).check 55 41 25 = true := by
  change case_55_41_25.check 55 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440] }

theorem case_55_41_26_checked :
    (Witness.linear .negative case_55_41_26).check 55 41 26 = true := by
  change case_55_41_26.check 55 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_42_1_checked :
    (Witness.rising).check 55 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_42_2_checked :
    (Witness.rising).check 55 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_42_3_checked :
    (Witness.rising).check 55 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_42_4_checked :
    (Witness.rising).check 55 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_42_5_checked :
    (Witness.rising).check 55 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_42_6_checked :
    (Witness.rising).check 55 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_42_7_checked :
    (Witness.rising).check 55 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_42_8_checked :
    (Witness.rising).check 55 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_42_9_checked :
    (Witness.rising).check 55 42 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_55_42_10_checked :
    (Witness.linear .positive case_55_42_10).check 55 42 10 = true := by
  change case_55_42_10.check 55 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_55_42_11_checked :
    (Witness.linear .positive case_55_42_11).check 55 42 11 = true := by
  change case_55_42_11.check 55 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_55_42_12_checked :
    (Witness.linear .positive case_55_42_12).check 55 42 12 = true := by
  change case_55_42_12.check 55 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_55_42_13_checked :
    (Witness.linear .positive case_55_42_13).check 55 42 13 = true := by
  change case_55_42_13.check 55 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_55_42_14_checked :
    (Witness.linear .positive case_55_42_14).check 55 42 14 = true := by
  change case_55_42_14.check 55 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_55_42_15_checked :
    (Witness.linear .positive case_55_42_15).check 55 42 15 = true := by
  change case_55_42_15.check 55 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_55_42_16_checked :
    (Witness.linear .positive case_55_42_16).check 55 42 16 = true := by
  change case_55_42_16.check 55 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_55_42_17_checked :
    (Witness.linear .positive case_55_42_17).check 55 42 17 = true := by
  change case_55_42_17.check 55 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_55_42_18_checked :
    (Witness.linear .positive case_55_42_18).check 55 42 18 = true := by
  change case_55_42_18.check 55 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_55_42_19_checked :
    (Witness.linear .positive case_55_42_19).check 55 42 19 = true := by
  change case_55_42_19.check 55 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_55_42_20_checked :
    (Witness.linear .positive case_55_42_20).check 55 42 20 = true := by
  change case_55_42_20.check 55 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_21 : Certificate := {
  objectiveScale := 913
  eta := 156365263560
  rows := #[⟨.assumptionRow 21, 1236⟩]
  caps := #[0, 0, 45607672440, 13370782050, 3942760395, 1170342810, 350017335, 105580948, 32161110, 9924960, 8612384040, 6910873710, 3919248645, 1849004040] }

theorem case_55_42_21_checked :
    (Witness.linear .conditional case_55_42_21).check 55 42 21 = true := by
  change case_55_42_21.check 55 42 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_22 : Certificate := {
  objectiveScale := 993
  eta := 198841611120
  rows := #[⟨.assumptionRow 22, 1117⟩]
  caps := #[0, 0, 57562286760, 17847559320, 5515956600, 1701828765, 525038020, 162212215, 50253632, 27293640, 12639436560, 11015464980, 6831013800, 3552465345] }

theorem case_55_42_22_checked :
    (Witness.linear .conditional case_55_42_22).check 55 42 22 = true := by
  change case_55_42_22.check 55 42 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_23 : Certificate := {
  objectiveScale := 998
  eta := 107690131200
  rows := #[⟨.assumptionRow 23, 887⟩]
  caps := #[0, 0, 32717630640, 11267310840, 3731955045, 1203621510, 380882645, 127794095, 45272326, 27293640, 15971741880, 14932722630, 9997706355, 5654836005] }

theorem case_55_42_23_checked :
    (Witness.linear .conditional case_55_42_23).check 55 42 23 = true := by
  change case_55_42_23.check 55 42 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_24 : Certificate := {
  objectiveScale := 32
  eta := 190731840
  rows := #[⟨.assumptionRow 24, 19⟩]
  caps := #[0, 0, 66966510, 28484235, 10607025, 4242810, 1701425, 629717, 277761, 100776, 660009840, 648223950, 459079425, 276778320] }

theorem case_55_42_24_checked :
    (Witness.linear .conditional case_55_42_24).check 55 42 24 = true := by
  change case_55_42_24.check 55 42 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825, 15967980] }

theorem case_55_42_25_checked :
    (Witness.linear .negative case_55_42_25).check 55 42 25 = true := by
  change case_55_42_25.check 55 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845] }

theorem case_55_42_26_checked :
    (Witness.linear .negative case_55_42_26).check 55 42 26 = true := by
  change case_55_42_26.check 55 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_42_27_checked :
    (Witness.linear .negative case_55_42_27).check 55 42 27 = true := by
  change case_55_42_27.check 55 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_43_1_checked :
    (Witness.rising).check 55 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_43_2_checked :
    (Witness.rising).check 55 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_43_3_checked :
    (Witness.rising).check 55 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_43_4_checked :
    (Witness.rising).check 55 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_43_5_checked :
    (Witness.rising).check 55 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_43_6_checked :
    (Witness.rising).check 55 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_43_7_checked :
    (Witness.rising).check 55 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_43_8_checked :
    (Witness.rising).check 55 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_43_9_checked :
    (Witness.rising).check 55 43 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_55_43_10_checked :
    (Witness.linear .positive case_55_43_10).check 55 43 10 = true := by
  change case_55_43_10.check 55 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_55_43_11_checked :
    (Witness.linear .positive case_55_43_11).check 55 43 11 = true := by
  change case_55_43_11.check 55 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_55_43_12_checked :
    (Witness.linear .positive case_55_43_12).check 55 43 12 = true := by
  change case_55_43_12.check 55 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_55_43_13_checked :
    (Witness.linear .positive case_55_43_13).check 55 43 13 = true := by
  change case_55_43_13.check 55 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_55_43_14_checked :
    (Witness.linear .positive case_55_43_14).check 55 43 14 = true := by
  change case_55_43_14.check 55 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_55_43_15_checked :
    (Witness.linear .positive case_55_43_15).check 55 43 15 = true := by
  change case_55_43_15.check 55 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_55_43_16_checked :
    (Witness.linear .positive case_55_43_16).check 55 43 16 = true := by
  change case_55_43_16.check 55 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_55_43_17_checked :
    (Witness.linear .positive case_55_43_17).check 55 43 17 = true := by
  change case_55_43_17.check 55 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_55_43_18_checked :
    (Witness.linear .positive case_55_43_18).check 55 43 18 = true := by
  change case_55_43_18.check 55 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_55_43_19_checked :
    (Witness.linear .positive case_55_43_19).check 55 43 19 = true := by
  change case_55_43_19.check 55 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_55_43_20_checked :
    (Witness.linear .positive case_55_43_20).check 55 43 20 = true := by
  change case_55_43_20.check 55 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_21 : Certificate := {
  objectiveScale := 3
  eta := 5097087270
  rows := #[⟨.assumptionRow 21, 8⟩]
  caps := #[0, 0, 1391975640, 382110960, 106073010, 29654820, 8357625, 2377280, 683468, 198968, 58786, 17680, 5434] }

theorem case_55_43_21_checked :
    (Witness.linear .conditional case_55_43_21).check 55 43 21 = true := by
  change case_55_43_21.check 55 43 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_22 : Certificate := {
  objectiveScale := 8
  eta := 1602881040
  rows := #[⟨.assumptionRow 22, 9⟩]
  caps := #[0, 0, 463991880, 143911920, 44472225, 13719615, 4232345, 1307504, 405042, 295267560, 295267560, 193536720, 104832390] }

theorem case_55_43_22_checked :
    (Witness.linear .conditional case_55_43_22).check 55 43 22 = true := by
  change case_55_43_22.check 55 43 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_23 : Certificate := {
  objectiveScale := 8
  eta := 770263200
  rows := #[⟨.assumptionRow 23, 7⟩]
  caps := #[0, 0, 238199040, 76918440, 26403195, 8727810, 2812095, 889295, 326876, 463991880, 436698240, 295267560, 169344630] }

theorem case_55_43_23_checked :
    (Witness.linear .conditional case_55_43_23).check 55 43 23 = true := by
  change case_55_43_23.check 55 43 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_24 : Certificate := {
  objectiveScale := 17
  eta := 91859820
  rows := #[⟨.assumptionRow 24, 10⟩]
  caps := #[0, 0, 33307950, 13656825, 5278845, 2022735, 847550, 298034, 138567, 1275977670, 1255507440, 893246400, 542771250] }

theorem case_55_43_24_checked :
    (Witness.linear .conditional case_55_43_24).check 55 43 24 = true := by
  change case_55_43_24.check 55 43 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 129644790, 129644790, 94287120, 58929450] }

theorem case_55_43_25_checked :
    (Witness.linear .negative case_55_43_25).check 55 43 25 = true := by
  change case_55_43_25.check 55 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670] }

theorem case_55_43_26_checked :
    (Witness.linear .negative case_55_43_26).check 55 43 26 = true := by
  change case_55_43_26.check 55 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_43_27_checked :
    (Witness.linear .negative case_55_43_27).check 55 43 27 = true := by
  change case_55_43_27.check 55 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_43_28_checked :
    (Witness.linear .negative case_55_43_28).check 55 43 28 = true := by
  change case_55_43_28.check 55 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_44_1_checked :
    (Witness.rising).check 55 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_44_2_checked :
    (Witness.rising).check 55 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_44_3_checked :
    (Witness.rising).check 55 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_44_4_checked :
    (Witness.rising).check 55 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_44_5_checked :
    (Witness.rising).check 55 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_44_6_checked :
    (Witness.rising).check 55 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_44_7_checked :
    (Witness.rising).check 55 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_44_8_checked :
    (Witness.rising).check 55 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_44_9_checked :
    (Witness.rising).check 55 44 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_55_44_10_checked :
    (Witness.linear .positive case_55_44_10).check 55 44 10 = true := by
  change case_55_44_10.check 55 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_55_44_11_checked :
    (Witness.linear .positive case_55_44_11).check 55 44 11 = true := by
  change case_55_44_11.check 55 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_55_44_12_checked :
    (Witness.linear .positive case_55_44_12).check 55 44 12 = true := by
  change case_55_44_12.check 55 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_55_44_13_checked :
    (Witness.linear .positive case_55_44_13).check 55 44 13 = true := by
  change case_55_44_13.check 55 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_55_44_14_checked :
    (Witness.linear .positive case_55_44_14).check 55 44 14 = true := by
  change case_55_44_14.check 55 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_55_44_15_checked :
    (Witness.linear .positive case_55_44_15).check 55 44 15 = true := by
  change case_55_44_15.check 55 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_55_44_16_checked :
    (Witness.linear .positive case_55_44_16).check 55 44 16 = true := by
  change case_55_44_16.check 55 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_55_44_17_checked :
    (Witness.linear .positive case_55_44_17).check 55 44 17 = true := by
  change case_55_44_17.check 55 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_55_44_18_checked :
    (Witness.linear .positive case_55_44_18).check 55 44 18 = true := by
  change case_55_44_18.check 55 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_55_44_19_checked :
    (Witness.linear .positive case_55_44_19).check 55 44 19 = true := by
  change case_55_44_19.check 55 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_55_44_20_checked :
    (Witness.linear .positive case_55_44_20).check 55 44 20 = true := by
  change case_55_44_20.check 55 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_55_44_21_checked :
    (Witness.linear .positive case_55_44_21).check 55 44 21 = true := by
  change case_55_44_21.check 55 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_22 : Certificate := {
  objectiveScale := 19
  eta := 9838736910
  rows := #[⟨.assumptionRow 22, 25⟩]
  caps := #[0, 0, 2783951280, 791515560, 235717800, 70525245, 21218535, 6426085, 1961256, 604010, 656557680, 539939400] }

theorem case_55_44_22_checked :
    (Witness.linear .conditional case_55_44_22).check 55 44 22 = true := by
  change case_55_44_22.check 55 44 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_23 : Certificate := {
  objectiveScale := 838
  eta := 213175842480
  rows := #[⟨.assumptionRow 23, 823⟩]
  caps := #[0, 0, 63735611880, 19187428920, 6300488670, 2029404195, 645077550, 203167855, 63577382, 83349814080, 76389935880, 50242628760] }

theorem case_55_44_23_checked :
    (Witness.linear .conditional case_55_44_23).check 55 44 23 = true := by
  change case_55_44_23.check 55 44 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_24 : Certificate := {
  objectiveScale := 537
  eta := 31420319700
  rows := #[⟨.assumptionRow 24, 398⟩]
  caps := #[0, 0, 10261006200, 3870734400, 1332515925, 434098665, 167640330, 59967325, 20470230, 66698832750, 64494871320, 45007212360] }

theorem case_55_44_24_checked :
    (Witness.linear .conditional case_55_44_24).check 55 44 24 = true := by
  change case_55_44_24.check 55 44 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 477638700, 477638700, 347993910, 218349120] }

theorem case_55_44_25_checked :
    (Witness.linear .negative case_55_44_25).check 55 44 25 = true := by
  change case_55_44_25.check 55 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 129644790, 129644790] }

theorem case_55_44_26_checked :
    (Witness.linear .negative case_55_44_26).check 55 44 26 = true := by
  change case_55_44_26.check 55 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_44_27_checked :
    (Witness.linear .negative case_55_44_27).check 55 44 27 = true := by
  change case_55_44_27.check 55 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_44_28_checked :
    (Witness.linear .negative case_55_44_28).check 55 44 28 = true := by
  change case_55_44_28.check 55 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_45_1_checked :
    (Witness.rising).check 55 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_45_2_checked :
    (Witness.rising).check 55 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_45_3_checked :
    (Witness.rising).check 55 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_45_4_checked :
    (Witness.rising).check 55 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_45_5_checked :
    (Witness.rising).check 55 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_45_6_checked :
    (Witness.rising).check 55 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_45_7_checked :
    (Witness.rising).check 55 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_45_8_checked :
    (Witness.rising).check 55 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_45_9_checked :
    (Witness.rising).check 55 45 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_55_45_10_checked :
    (Witness.linear .positive case_55_45_10).check 55 45 10 = true := by
  change case_55_45_10.check 55 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_55_45_11_checked :
    (Witness.linear .positive case_55_45_11).check 55 45 11 = true := by
  change case_55_45_11.check 55 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_55_45_12_checked :
    (Witness.linear .positive case_55_45_12).check 55 45 12 = true := by
  change case_55_45_12.check 55 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_55_45_13_checked :
    (Witness.linear .positive case_55_45_13).check 55 45 13 = true := by
  change case_55_45_13.check 55 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_55_45_14_checked :
    (Witness.linear .positive case_55_45_14).check 55 45 14 = true := by
  change case_55_45_14.check 55 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_55_45_15_checked :
    (Witness.linear .positive case_55_45_15).check 55 45 15 = true := by
  change case_55_45_15.check 55 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_55_45_16_checked :
    (Witness.linear .positive case_55_45_16).check 55 45 16 = true := by
  change case_55_45_16.check 55 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_55_45_17_checked :
    (Witness.linear .positive case_55_45_17).check 55 45 17 = true := by
  change case_55_45_17.check 55 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_55_45_18_checked :
    (Witness.linear .positive case_55_45_18).check 55 45 18 = true := by
  change case_55_45_18.check 55 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_55_45_19_checked :
    (Witness.linear .positive case_55_45_19).check 55 45 19 = true := by
  change case_55_45_19.check 55 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_55_45_20_checked :
    (Witness.linear .positive case_55_45_20).check 55 45 20 = true := by
  change case_55_45_20.check 55 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_55_45_21_checked :
    (Witness.linear .positive case_55_45_21).check 55 45 21 = true := by
  change case_55_45_21.check 55 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_55_45_22_checked :
    (Witness.linear .positive case_55_45_22).check 55 45 22 = true := by
  change case_55_45_22.check 55 45 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_23 : Certificate := {
  objectiveScale := 397
  eta := 209880216360
  rows := #[⟨.assumptionRow 23, 428⟩]
  caps := #[0, 0, 62259274080, 18450500640, 5466792030, 1620609900, 514187310, 165061455, 52708755, 67530075120, 60190567200] }

theorem case_55_45_23_checked :
    (Witness.linear .conditional case_55_45_23).check 55 45 23 = true := by
  change case_55_45_23.check 55 45 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_24 : Certificate := {
  objectiveScale := 15
  eta := 802357500
  rows := #[⟨.assumptionRow 24, 11⟩]
  caps := #[0, 0, 259451400, 96768360, 34337160, 11396385, 4242810, 1562275, 6816586590, 6611884290, 4639918800] }

theorem case_55_45_24_checked :
    (Witness.linear .conditional case_55_45_24).check 55 45 24 = true := by
  change case_55_45_24.check 55 45 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 1767263190, 1767263190, 1289624490, 811985790] }

theorem case_55_45_25_checked :
    (Witness.linear .negative case_55_45_25).check 55 45 25 = true := by
  change case_55_45_25.check 55 45 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 477638700, 477638700] }

theorem case_55_45_26_checked :
    (Witness.linear .negative case_55_45_26).check 55 45 26 = true := by
  change case_55_45_26.check 55 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_45_27_checked :
    (Witness.linear .negative case_55_45_27).check 55 45 27 = true := by
  change case_55_45_27.check 55 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_45_28_checked :
    (Witness.linear .negative case_55_45_28).check 55 45 28 = true := by
  change case_55_45_28.check 55 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_45_29_checked :
    (Witness.linear .negative case_55_45_29).check 55 45 29 = true := by
  change case_55_45_29.check 55 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_46_1_checked :
    (Witness.rising).check 55 46 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_46_2_checked :
    (Witness.rising).check 55 46 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_46_3_checked :
    (Witness.rising).check 55 46 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_46_4_checked :
    (Witness.rising).check 55 46 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_46_5_checked :
    (Witness.rising).check 55 46 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_46_6_checked :
    (Witness.rising).check 55 46 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_46_7_checked :
    (Witness.rising).check 55 46 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_46_8_checked :
    (Witness.rising).check 55 46 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_46_9_checked :
    (Witness.rising).check 55 46 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_55_46_10_checked :
    (Witness.linear .positive case_55_46_10).check 55 46 10 = true := by
  change case_55_46_10.check 55 46 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_55_46_11_checked :
    (Witness.linear .positive case_55_46_11).check 55 46 11 = true := by
  change case_55_46_11.check 55 46 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_55_46_12_checked :
    (Witness.linear .positive case_55_46_12).check 55 46 12 = true := by
  change case_55_46_12.check 55 46 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_55_46_13_checked :
    (Witness.linear .positive case_55_46_13).check 55 46 13 = true := by
  change case_55_46_13.check 55 46 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_55_46_14_checked :
    (Witness.linear .positive case_55_46_14).check 55 46 14 = true := by
  change case_55_46_14.check 55 46 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_55_46_15_checked :
    (Witness.linear .positive case_55_46_15).check 55 46 15 = true := by
  change case_55_46_15.check 55 46 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_55_46_16_checked :
    (Witness.linear .positive case_55_46_16).check 55 46 16 = true := by
  change case_55_46_16.check 55 46 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_55_46_17_checked :
    (Witness.linear .positive case_55_46_17).check 55 46 17 = true := by
  change case_55_46_17.check 55 46 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_55_46_18_checked :
    (Witness.linear .positive case_55_46_18).check 55 46 18 = true := by
  change case_55_46_18.check 55 46 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_55_46_19_checked :
    (Witness.linear .positive case_55_46_19).check 55 46 19 = true := by
  change case_55_46_19.check 55 46 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_55_46_20_checked :
    (Witness.linear .positive case_55_46_20).check 55 46 20 = true := by
  change case_55_46_20.check 55 46 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_55_46_21_checked :
    (Witness.linear .positive case_55_46_21).check 55 46 21 = true := by
  change case_55_46_21.check 55 46 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_55_46_22_checked :
    (Witness.linear .positive case_55_46_22).check 55 46 22 = true := by
  change case_55_46_22.check 55 46 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_23 : Certificate := {
  objectiveScale := 10
  eta := 59647876860
  rows := #[⟨.assumptionRow 23, 17⟩]
  caps := #[0, 0, 16387349580, 4523920830, 1275977670, 362261040, 103601775, 29871135, 8691930, 2555576] }

theorem case_55_46_23_checked :
    (Witness.linear .conditional case_55_46_23).check 55 46 23 = true := by
  change case_55_46_23.check 55 46 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_24 : Certificate := {
  objectiveScale := 992
  eta := 227997907200
  rows := #[⟨.assumptionRow 24, 845⟩]
  caps := #[0, 0, 76109340000, 24514651200, 7701148650, 2541079905, 890173830, 492957660, 769298348250, 731221859520] }

theorem case_55_46_24_checked :
    (Witness.linear .conditional case_55_46_24).check 55 46 24 = true := by
  change case_55_46_24.check 55 46 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 6564120420, 6564120420, 4796857230, 3029594040] }

theorem case_55_46_25_checked :
    (Witness.linear .negative case_55_46_25).check 55 46 25 = true := by
  change case_55_46_25.check 55 46 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 1767263190, 1767263190] }

theorem case_55_46_26_checked :
    (Witness.linear .negative case_55_46_26).check 55 46 26 = true := by
  change case_55_46_26.check 55 46 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_46_27_checked :
    (Witness.linear .negative case_55_46_27).check 55 46 27 = true := by
  change case_55_46_27.check 55 46 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_46_28_checked :
    (Witness.linear .negative case_55_46_28).check 55 46 28 = true := by
  change case_55_46_28.check 55 46 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_46_29_checked :
    (Witness.linear .negative case_55_46_29).check 55 46 29 = true := by
  change case_55_46_29.check 55 46 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_46_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_46_30_checked :
    (Witness.linear .negative case_55_46_30).check 55 46 30 = true := by
  change case_55_46_30.check 55 46 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_47_1_checked :
    (Witness.rising).check 55 47 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_47_2_checked :
    (Witness.rising).check 55 47 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_47_3_checked :
    (Witness.rising).check 55 47 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_47_4_checked :
    (Witness.rising).check 55 47 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_47_5_checked :
    (Witness.rising).check 55 47 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_47_6_checked :
    (Witness.rising).check 55 47 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_47_7_checked :
    (Witness.rising).check 55 47 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_47_8_checked :
    (Witness.rising).check 55 47 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_47_9_checked :
    (Witness.rising).check 55 47 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_55_47_10_checked :
    (Witness.linear .positive case_55_47_10).check 55 47 10 = true := by
  change case_55_47_10.check 55 47 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_55_47_11_checked :
    (Witness.linear .positive case_55_47_11).check 55 47 11 = true := by
  change case_55_47_11.check 55 47 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_55_47_12_checked :
    (Witness.linear .positive case_55_47_12).check 55 47 12 = true := by
  change case_55_47_12.check 55 47 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_55_47_13_checked :
    (Witness.linear .positive case_55_47_13).check 55 47 13 = true := by
  change case_55_47_13.check 55 47 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_55_47_14_checked :
    (Witness.linear .positive case_55_47_14).check 55 47 14 = true := by
  change case_55_47_14.check 55 47 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_55_47_15_checked :
    (Witness.linear .positive case_55_47_15).check 55 47 15 = true := by
  change case_55_47_15.check 55 47 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_55_47_16_checked :
    (Witness.linear .positive case_55_47_16).check 55 47 16 = true := by
  change case_55_47_16.check 55 47 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_55_47_17_checked :
    (Witness.linear .positive case_55_47_17).check 55 47 17 = true := by
  change case_55_47_17.check 55 47 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_55_47_18_checked :
    (Witness.linear .positive case_55_47_18).check 55 47 18 = true := by
  change case_55_47_18.check 55 47 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_55_47_19_checked :
    (Witness.linear .positive case_55_47_19).check 55 47 19 = true := by
  change case_55_47_19.check 55 47 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_55_47_20_checked :
    (Witness.linear .positive case_55_47_20).check 55 47 20 = true := by
  change case_55_47_20.check 55 47 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_55_47_21_checked :
    (Witness.linear .positive case_55_47_21).check 55 47 21 = true := by
  change case_55_47_21.check 55 47 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_55_47_22_checked :
    (Witness.linear .positive case_55_47_22).check 55 47 22 = true := by
  change case_55_47_22.check 55 47 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_55_47_23_checked :
    (Witness.linear .positive case_55_47_23).check 55 47 23 = true := by
  change case_55_47_23.check 55 47 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_24 : Certificate := {
  objectiveScale := 986
  eta := 635289704370
  rows := #[⟨.assumptionRow 24, 939⟩]
  caps := #[0, 0, 198826939440, 61373471400, 18750730680, 5683970565, 1880089575, 1232394150, 1319894134650] }

theorem case_55_47_24_checked :
    (Witness.linear .conditional case_55_47_24).check 55 47 24 = true := by
  change case_55_47_24.check 55 47 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 24466267020, 24466267020, 17902146600, 11338026180] }

theorem case_55_47_25_checked :
    (Witness.linear .negative case_55_47_25).check 55 47 25 = true := by
  change case_55_47_25.check 55 47 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 6564120420, 6564120420] }

theorem case_55_47_26_checked :
    (Witness.linear .negative case_55_47_26).check 55 47 26 = true := by
  change case_55_47_26.check 55 47 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_47_27_checked :
    (Witness.linear .negative case_55_47_27).check 55 47 27 = true := by
  change case_55_47_27.check 55 47 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_47_28_checked :
    (Witness.linear .negative case_55_47_28).check 55 47 28 = true := by
  change case_55_47_28.check 55 47 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_47_29_checked :
    (Witness.linear .negative case_55_47_29).check 55 47 29 = true := by
  change case_55_47_29.check 55 47 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_47_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_47_30_checked :
    (Witness.linear .negative case_55_47_30).check 55 47 30 = true := by
  change case_55_47_30.check 55 47 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_48_1_checked :
    (Witness.rising).check 55 48 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_48_2_checked :
    (Witness.rising).check 55 48 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_48_3_checked :
    (Witness.rising).check 55 48 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_48_4_checked :
    (Witness.rising).check 55 48 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_48_5_checked :
    (Witness.rising).check 55 48 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_48_6_checked :
    (Witness.rising).check 55 48 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_48_7_checked :
    (Witness.rising).check 55 48 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_48_8_checked :
    (Witness.rising).check 55 48 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_48_9_checked :
    (Witness.rising).check 55 48 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_55_48_10_checked :
    (Witness.linear .positive case_55_48_10).check 55 48 10 = true := by
  change case_55_48_10.check 55 48 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_55_48_11_checked :
    (Witness.linear .positive case_55_48_11).check 55 48 11 = true := by
  change case_55_48_11.check 55 48 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_55_48_12_checked :
    (Witness.linear .positive case_55_48_12).check 55 48 12 = true := by
  change case_55_48_12.check 55 48 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_55_48_13_checked :
    (Witness.linear .positive case_55_48_13).check 55 48 13 = true := by
  change case_55_48_13.check 55 48 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_55_48_14_checked :
    (Witness.linear .positive case_55_48_14).check 55 48 14 = true := by
  change case_55_48_14.check 55 48 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_55_48_15_checked :
    (Witness.linear .positive case_55_48_15).check 55 48 15 = true := by
  change case_55_48_15.check 55 48 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_55_48_16_checked :
    (Witness.linear .positive case_55_48_16).check 55 48 16 = true := by
  change case_55_48_16.check 55 48 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_55_48_17_checked :
    (Witness.linear .positive case_55_48_17).check 55 48 17 = true := by
  change case_55_48_17.check 55 48 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_55_48_18_checked :
    (Witness.linear .positive case_55_48_18).check 55 48 18 = true := by
  change case_55_48_18.check 55 48 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_55_48_19_checked :
    (Witness.linear .positive case_55_48_19).check 55 48 19 = true := by
  change case_55_48_19.check 55 48 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_55_48_20_checked :
    (Witness.linear .positive case_55_48_20).check 55 48 20 = true := by
  change case_55_48_20.check 55 48 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_55_48_21_checked :
    (Witness.linear .positive case_55_48_21).check 55 48 21 = true := by
  change case_55_48_21.check 55 48 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_55_48_22_checked :
    (Witness.linear .positive case_55_48_22).check 55 48 22 = true := by
  change case_55_48_22.check 55 48 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_55_48_23_checked :
    (Witness.linear .positive case_55_48_23).check 55 48 23 = true := by
  change case_55_48_23.check 55 48 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_24 : Certificate := {
  objectiveScale := 23
  eta := 2081228322810
  rows := #[⟨.assumptionRow 24, 63⟩]
  caps := #[0, 0, 562724141460, 152764984320, 41656918050, 11415564930, 3145592010, 872155860] }

theorem case_55_48_24_checked :
    (Witness.linear .conditional case_55_48_24).check 55 48 24 = true := by
  change case_55_48_24.check 55 48 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_25 : Certificate := {
  objectiveScale := 7
  eta := 69140292
  rows := #[⟨.assumptionRow 25, 4⟩]
  caps := #[0, 0, 25945140, 10868910, 3771885, 1726725, 96801317340, 95737566600] }

theorem case_55_48_25_checked :
    (Witness.linear .conditional case_55_48_25).check 55 48 25 = true := by
  change case_55_48_25.check 55 48 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 24466267020, 24466267020] }

theorem case_55_48_26_checked :
    (Witness.linear .negative case_55_48_26).check 55 48 26 = true := by
  change case_55_48_26.check 55 48 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_48_27_checked :
    (Witness.linear .negative case_55_48_27).check 55 48 27 = true := by
  change case_55_48_27.check 55 48 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_48_28_checked :
    (Witness.linear .negative case_55_48_28).check 55 48 28 = true := by
  change case_55_48_28.check 55 48 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_48_29_checked :
    (Witness.linear .negative case_55_48_29).check 55 48 29 = true := by
  change case_55_48_29.check 55 48 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_48_30_checked :
    (Witness.linear .negative case_55_48_30).check 55 48 30 = true := by
  change case_55_48_30.check 55 48 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_48_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_55_48_31_checked :
    (Witness.linear .negative case_55_48_31).check 55 48 31 = true := by
  change case_55_48_31.check 55 48 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_49_1_checked :
    (Witness.rising).check 55 49 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_49_2_checked :
    (Witness.rising).check 55 49 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_49_3_checked :
    (Witness.rising).check 55 49 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_49_4_checked :
    (Witness.rising).check 55 49 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_49_5_checked :
    (Witness.rising).check 55 49 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_49_6_checked :
    (Witness.rising).check 55 49 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_49_7_checked :
    (Witness.rising).check 55 49 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_49_8_checked :
    (Witness.rising).check 55 49 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_49_9_checked :
    (Witness.rising).check 55 49 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_55_49_10_checked :
    (Witness.linear .positive case_55_49_10).check 55 49 10 = true := by
  change case_55_49_10.check 55 49 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_55_49_11_checked :
    (Witness.linear .positive case_55_49_11).check 55 49 11 = true := by
  change case_55_49_11.check 55 49 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_55_49_12_checked :
    (Witness.linear .positive case_55_49_12).check 55 49 12 = true := by
  change case_55_49_12.check 55 49 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_55_49_13_checked :
    (Witness.linear .positive case_55_49_13).check 55 49 13 = true := by
  change case_55_49_13.check 55 49 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_55_49_14_checked :
    (Witness.linear .positive case_55_49_14).check 55 49 14 = true := by
  change case_55_49_14.check 55 49 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_55_49_15_checked :
    (Witness.linear .positive case_55_49_15).check 55 49 15 = true := by
  change case_55_49_15.check 55 49 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_55_49_16_checked :
    (Witness.linear .positive case_55_49_16).check 55 49 16 = true := by
  change case_55_49_16.check 55 49 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_55_49_17_checked :
    (Witness.linear .positive case_55_49_17).check 55 49 17 = true := by
  change case_55_49_17.check 55 49 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_55_49_18_checked :
    (Witness.linear .positive case_55_49_18).check 55 49 18 = true := by
  change case_55_49_18.check 55 49 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_55_49_19_checked :
    (Witness.linear .positive case_55_49_19).check 55 49 19 = true := by
  change case_55_49_19.check 55 49 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_55_49_20_checked :
    (Witness.linear .positive case_55_49_20).check 55 49 20 = true := by
  change case_55_49_20.check 55 49 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_55_49_21_checked :
    (Witness.linear .positive case_55_49_21).check 55 49 21 = true := by
  change case_55_49_21.check 55 49 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_55_49_22_checked :
    (Witness.linear .positive case_55_49_22).check 55 49 22 = true := by
  change case_55_49_22.check 55 49 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670] }

theorem case_55_49_23_checked :
    (Witness.linear .positive case_55_49_23).check 55 49 23 = true := by
  change case_55_49_23.check 55 49 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700, 129644790] }

theorem case_55_49_24_checked :
    (Witness.linear .positive case_55_49_24).check 55 49 24 = true := by
  change case_55_49_24.check 55 49 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_25 : Certificate := {
  objectiveScale := 6
  eta := 3481039476
  rows := #[⟨.assumptionRow 25, 5⟩]
  caps := #[0, 0, 1072866600, 366792000, 124062000, 40320150, 12746370] }

theorem case_55_49_25_checked :
    (Witness.linear .conditional case_55_49_25).check 55 49 25 = true := by
  change case_55_49_25.check 55 49 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 91482563640, 91482563640] }

theorem case_55_49_26_checked :
    (Witness.linear .negative case_55_49_26).check 55 49 26 = true := by
  change case_55_49_26.check 55 49 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_55_49_27_checked :
    (Witness.linear .negative case_55_49_27).check 55 49 27 = true := by
  change case_55_49_27.check 55 49 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_55_49_28_checked :
    (Witness.linear .negative case_55_49_28).check 55 49 28 = true := by
  change case_55_49_28.check 55 49 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_55_49_29_checked :
    (Witness.linear .negative case_55_49_29).check 55 49 29 = true := by
  change case_55_49_29.check 55 49 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_55_49_30_checked :
    (Witness.linear .negative case_55_49_30).check 55 49 30 = true := by
  change case_55_49_30.check 55 49 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_55_49_31_checked :
    (Witness.linear .negative case_55_49_31).check 55 49 31 = true := by
  change case_55_49_31.check 55 49 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_49_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_55_49_32_checked :
    (Witness.linear .negative case_55_49_32).check 55 49 32 = true := by
  change case_55_49_32.check 55 49 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_50_1_checked :
    (Witness.rising).check 55 50 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_50_2_checked :
    (Witness.rising).check 55 50 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_50_3_checked :
    (Witness.rising).check 55 50 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_50_4_checked :
    (Witness.rising).check 55 50 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_50_5_checked :
    (Witness.rising).check 55 50 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_50_6_checked :
    (Witness.rising).check 55 50 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_50_7_checked :
    (Witness.rising).check 55 50 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_50_8_checked :
    (Witness.rising).check 55 50 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_50_9_checked :
    (Witness.rising).check 55 50 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_55_50_10_checked :
    (Witness.linear .positive case_55_50_10).check 55 50 10 = true := by
  change case_55_50_10.check 55 50 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_55_50_11_checked :
    (Witness.linear .positive case_55_50_11).check 55 50 11 = true := by
  change case_55_50_11.check 55 50 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_55_50_12_checked :
    (Witness.linear .positive case_55_50_12).check 55 50 12 = true := by
  change case_55_50_12.check 55 50 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_55_50_13_checked :
    (Witness.linear .positive case_55_50_13).check 55 50 13 = true := by
  change case_55_50_13.check 55 50 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_55_50_14_checked :
    (Witness.linear .positive case_55_50_14).check 55 50 14 = true := by
  change case_55_50_14.check 55 50 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_55_50_15_checked :
    (Witness.linear .positive case_55_50_15).check 55 50 15 = true := by
  change case_55_50_15.check 55 50 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_55_50_16_checked :
    (Witness.linear .positive case_55_50_16).check 55 50 16 = true := by
  change case_55_50_16.check 55 50 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_55_50_17_checked :
    (Witness.linear .positive case_55_50_17).check 55 50 17 = true := by
  change case_55_50_17.check 55 50 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_55_50_18_checked :
    (Witness.linear .positive case_55_50_18).check 55 50 18 = true := by
  change case_55_50_18.check 55 50 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_55_50_19_checked :
    (Witness.linear .positive case_55_50_19).check 55 50 19 = true := by
  change case_55_50_19.check 55 50 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_55_50_20_checked :
    (Witness.linear .positive case_55_50_20).check 55 50 20 = true := by
  change case_55_50_20.check 55 50 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845] }

theorem case_55_50_21_checked :
    (Witness.linear .positive case_55_50_21).check 55 50 21 = true := by
  change case_55_50_21.check 55 50 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670] }

theorem case_55_50_22_checked :
    (Witness.linear .positive case_55_50_22).check 55 50 22 = true := by
  change case_55_50_22.check 55 50 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790] }

theorem case_55_50_23_checked :
    (Witness.linear .positive case_55_50_23).check 55 50 23 = true := by
  change case_55_50_23.check 55 50 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700] }

theorem case_55_50_24_checked :
    (Witness.linear .positive case_55_50_24).check 55 50 24 = true := by
  change case_55_50_24.check 55 50 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020, 6564120420, 1767263190] }

theorem case_55_50_25_checked :
    (Witness.linear .positive case_55_50_25).check 55 50 25 = true := by
  change case_55_50_25.check 55 50 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 343059613650, 343059613650] }

theorem case_55_50_26_checked :
    (Witness.linear .negative case_55_50_26).check 55 50 26 = true := by
  change case_55_50_26.check 55 50 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_55_50_27_checked :
    (Witness.linear .negative case_55_50_27).check 55 50 27 = true := by
  change case_55_50_27.check 55 50 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_55_50_28_checked :
    (Witness.linear .negative case_55_50_28).check 55 50 28 = true := by
  change case_55_50_28.check 55 50 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_55_50_29_checked :
    (Witness.linear .negative case_55_50_29).check 55 50 29 = true := by
  change case_55_50_29.check 55 50 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_55_50_30_checked :
    (Witness.linear .negative case_55_50_30).check 55 50 30 = true := by
  change case_55_50_30.check 55 50 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_55_50_31_checked :
    (Witness.linear .negative case_55_50_31).check 55 50 31 = true := by
  change case_55_50_31.check 55 50 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_50_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_55_50_32_checked :
    (Witness.linear .negative case_55_50_32).check 55 50 32 = true := by
  change case_55_50_32.check 55 50 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_51_1_checked :
    (Witness.rising).check 55 51 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_51_2_checked :
    (Witness.rising).check 55 51 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_51_3_checked :
    (Witness.rising).check 55 51 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_51_4_checked :
    (Witness.rising).check 55 51 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_51_5_checked :
    (Witness.rising).check 55 51 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_51_6_checked :
    (Witness.rising).check 55 51 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_51_7_checked :
    (Witness.rising).check 55 51 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_51_8_checked :
    (Witness.rising).check 55 51 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_51_9_checked :
    (Witness.rising).check 55 51 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_55_51_10_checked :
    (Witness.linear .positive case_55_51_10).check 55 51 10 = true := by
  change case_55_51_10.check 55 51 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_55_51_11_checked :
    (Witness.linear .positive case_55_51_11).check 55 51 11 = true := by
  change case_55_51_11.check 55 51 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_55_51_12_checked :
    (Witness.linear .positive case_55_51_12).check 55 51 12 = true := by
  change case_55_51_12.check 55 51 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_55_51_13_checked :
    (Witness.linear .positive case_55_51_13).check 55 51 13 = true := by
  change case_55_51_13.check 55 51 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_55_51_14_checked :
    (Witness.linear .positive case_55_51_14).check 55 51 14 = true := by
  change case_55_51_14.check 55 51 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_55_51_15_checked :
    (Witness.linear .positive case_55_51_15).check 55 51 15 = true := by
  change case_55_51_15.check 55 51 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_55_51_16_checked :
    (Witness.linear .positive case_55_51_16).check 55 51 16 = true := by
  change case_55_51_16.check 55 51 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_55_51_17_checked :
    (Witness.linear .positive case_55_51_17).check 55 51 17 = true := by
  change case_55_51_17.check 55 51 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_55_51_18_checked :
    (Witness.linear .positive case_55_51_18).check 55 51 18 = true := by
  change case_55_51_18.check 55 51 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_55_51_19_checked :
    (Witness.linear .positive case_55_51_19).check 55 51 19 = true := by
  change case_55_51_19.check 55 51 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_55_51_20_checked :
    (Witness.linear .positive case_55_51_20).check 55 51 20 = true := by
  change case_55_51_20.check 55 51 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_55_51_21_checked :
    (Witness.linear .positive case_55_51_21).check 55 51 21 = true := by
  change case_55_51_21.check 55 51 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790] }

theorem case_55_51_22_checked :
    (Witness.linear .positive case_55_51_22).check 55 51 22 = true := by
  change case_55_51_22.check 55 51 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700] }

theorem case_55_51_23_checked :
    (Witness.linear .positive case_55_51_23).check 55 51 23 = true := by
  change case_55_51_23.check 55 51 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190] }

theorem case_55_51_24_checked :
    (Witness.linear .positive case_55_51_24).check 55 51 24 = true := by
  change case_55_51_24.check 55 51 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020, 6564120420] }

theorem case_55_51_25_checked :
    (Witness.linear .positive case_55_51_25).check 55 51 25 = true := by
  change case_55_51_25.check 55 51 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 1289904147324, 1289904147324] }

theorem case_55_51_26_checked :
    (Witness.linear .negative case_55_51_26).check 55 51 26 = true := by
  change case_55_51_26.check 55 51 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_55_51_27_checked :
    (Witness.linear .negative case_55_51_27).check 55 51 27 = true := by
  change case_55_51_27.check 55 51 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_55_51_28_checked :
    (Witness.linear .negative case_55_51_28).check 55 51 28 = true := by
  change case_55_51_28.check 55 51 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_55_51_29_checked :
    (Witness.linear .negative case_55_51_29).check 55 51 29 = true := by
  change case_55_51_29.check 55 51 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_55_51_30_checked :
    (Witness.linear .negative case_55_51_30).check 55 51 30 = true := by
  change case_55_51_30.check 55 51 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_55_51_31_checked :
    (Witness.linear .negative case_55_51_31).check 55 51 31 = true := by
  change case_55_51_31.check 55 51 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_55_51_32_checked :
    (Witness.linear .negative case_55_51_32).check 55 51 32 = true := by
  change case_55_51_32.check 55 51 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_51_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_55_51_33_checked :
    (Witness.linear .negative case_55_51_33).check 55 51 33 = true := by
  change case_55_51_33.check 55 51 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_52_1_checked :
    (Witness.rising).check 55 52 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_52_2_checked :
    (Witness.rising).check 55 52 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_52_3_checked :
    (Witness.rising).check 55 52 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_52_4_checked :
    (Witness.rising).check 55 52 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_52_5_checked :
    (Witness.rising).check 55 52 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_52_6_checked :
    (Witness.rising).check 55 52 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_52_7_checked :
    (Witness.rising).check 55 52 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_52_8_checked :
    (Witness.rising).check 55 52 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_52_9_checked :
    (Witness.rising).check 55 52 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_55_52_10_checked :
    (Witness.linear .positive case_55_52_10).check 55 52 10 = true := by
  change case_55_52_10.check 55 52 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_55_52_11_checked :
    (Witness.linear .positive case_55_52_11).check 55 52 11 = true := by
  change case_55_52_11.check 55 52 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_55_52_12_checked :
    (Witness.linear .positive case_55_52_12).check 55 52 12 = true := by
  change case_55_52_12.check 55 52 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_55_52_13_checked :
    (Witness.linear .positive case_55_52_13).check 55 52 13 = true := by
  change case_55_52_13.check 55 52 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_55_52_14_checked :
    (Witness.linear .positive case_55_52_14).check 55 52 14 = true := by
  change case_55_52_14.check 55 52 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_55_52_15_checked :
    (Witness.linear .positive case_55_52_15).check 55 52 15 = true := by
  change case_55_52_15.check 55 52 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_55_52_16_checked :
    (Witness.linear .positive case_55_52_16).check 55 52 16 = true := by
  change case_55_52_16.check 55 52 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_55_52_17_checked :
    (Witness.linear .positive case_55_52_17).check 55 52 17 = true := by
  change case_55_52_17.check 55 52 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_55_52_18_checked :
    (Witness.linear .positive case_55_52_18).check 55 52 18 = true := by
  change case_55_52_18.check 55 52 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_55_52_19_checked :
    (Witness.linear .positive case_55_52_19).check 55 52 19 = true := by
  change case_55_52_19.check 55 52 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_55_52_20_checked :
    (Witness.linear .positive case_55_52_20).check 55 52 20 = true := by
  change case_55_52_20.check 55 52 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_55_52_21_checked :
    (Witness.linear .positive case_55_52_21).check 55 52 21 = true := by
  change case_55_52_21.check 55 52 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700] }

theorem case_55_52_22_checked :
    (Witness.linear .positive case_55_52_22).check 55 52 22 = true := by
  change case_55_52_22.check 55 52 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190] }

theorem case_55_52_23_checked :
    (Witness.linear .positive case_55_52_23).check 55 52 23 = true := by
  change case_55_52_23.check 55 52 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420] }

theorem case_55_52_24_checked :
    (Witness.linear .positive case_55_52_24).check 55 52 24 = true := by
  change case_55_52_24.check 55 52 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020] }

theorem case_55_52_25_checked :
    (Witness.linear .positive case_55_52_25).check 55 52 25 = true := by
  change case_55_52_25.check 55 52 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0, 343059613650, 91482563640] }

theorem case_55_52_26_checked :
    (Witness.linear .positive case_55_52_26).check 55 52 26 = true := by
  change case_55_52_26.check 55 52 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_55_52_27_checked :
    (Witness.linear .negative case_55_52_27).check 55 52 27 = true := by
  change case_55_52_27.check 55 52 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_55_52_28_checked :
    (Witness.linear .negative case_55_52_28).check 55 52 28 = true := by
  change case_55_52_28.check 55 52 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_55_52_29_checked :
    (Witness.linear .negative case_55_52_29).check 55 52 29 = true := by
  change case_55_52_29.check 55 52 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_55_52_30_checked :
    (Witness.linear .negative case_55_52_30).check 55 52 30 = true := by
  change case_55_52_30.check 55 52 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_55_52_31_checked :
    (Witness.linear .negative case_55_52_31).check 55 52 31 = true := by
  change case_55_52_31.check 55 52 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_55_52_32_checked :
    (Witness.linear .negative case_55_52_32).check 55 52 32 = true := by
  change case_55_52_32.check 55 52 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_55_52_33_checked :
    (Witness.linear .negative case_55_52_33).check 55 52 33 = true := by
  change case_55_52_33.check 55 52 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_52_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_55_52_34_checked :
    (Witness.linear .negative case_55_52_34).check 55 52 34 = true := by
  change case_55_52_34.check 55 52 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_53_1_checked :
    (Witness.rising).check 55 53 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_53_2_checked :
    (Witness.rising).check 55 53 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_53_3_checked :
    (Witness.rising).check 55 53 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_53_4_checked :
    (Witness.rising).check 55 53 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_53_5_checked :
    (Witness.rising).check 55 53 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_53_6_checked :
    (Witness.rising).check 55 53 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_53_7_checked :
    (Witness.rising).check 55 53 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_53_8_checked :
    (Witness.rising).check 55 53 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_53_9_checked :
    (Witness.rising).check 55 53 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_55_53_10_checked :
    (Witness.linear .positive case_55_53_10).check 55 53 10 = true := by
  change case_55_53_10.check 55 53 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_55_53_11_checked :
    (Witness.linear .positive case_55_53_11).check 55 53 11 = true := by
  change case_55_53_11.check 55 53 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_55_53_12_checked :
    (Witness.linear .positive case_55_53_12).check 55 53 12 = true := by
  change case_55_53_12.check 55 53 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_55_53_13_checked :
    (Witness.linear .positive case_55_53_13).check 55 53 13 = true := by
  change case_55_53_13.check 55 53 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_55_53_14_checked :
    (Witness.linear .positive case_55_53_14).check 55 53 14 = true := by
  change case_55_53_14.check 55 53 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_55_53_15_checked :
    (Witness.linear .positive case_55_53_15).check 55 53 15 = true := by
  change case_55_53_15.check 55 53 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_55_53_16_checked :
    (Witness.linear .positive case_55_53_16).check 55 53 16 = true := by
  change case_55_53_16.check 55 53 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_55_53_17_checked :
    (Witness.linear .positive case_55_53_17).check 55 53 17 = true := by
  change case_55_53_17.check 55 53 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_55_53_18_checked :
    (Witness.linear .positive case_55_53_18).check 55 53 18 = true := by
  change case_55_53_18.check 55 53 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_55_53_19_checked :
    (Witness.linear .positive case_55_53_19).check 55 53 19 = true := by
  change case_55_53_19.check 55 53 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_55_53_20_checked :
    (Witness.linear .positive case_55_53_20).check 55 53 20 = true := by
  change case_55_53_20.check 55 53 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_55_53_21_checked :
    (Witness.linear .positive case_55_53_21).check 55 53 21 = true := by
  change case_55_53_21.check 55 53 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_55_53_22_checked :
    (Witness.linear .positive case_55_53_22).check 55 53 22 = true := by
  change case_55_53_22.check 55 53 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420] }

theorem case_55_53_23_checked :
    (Witness.linear .positive case_55_53_23).check 55 53 23 = true := by
  change case_55_53_23.check 55 53 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020] }

theorem case_55_53_24_checked :
    (Witness.linear .positive case_55_53_24).check 55 53 24 = true := by
  change case_55_53_24.check 55 53 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640] }

theorem case_55_53_25_checked :
    (Witness.linear .positive case_55_53_25).check 55 53 25 = true := by
  change case_55_53_25.check 55 53 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0, 343059613650] }

theorem case_55_53_26_checked :
    (Witness.linear .positive case_55_53_26).check 55 53 26 = true := by
  change case_55_53_26.check 55 53 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_55_53_27_checked :
    (Witness.linear .negative case_55_53_27).check 55 53 27 = true := by
  change case_55_53_27.check 55 53 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_55_53_28_checked :
    (Witness.linear .negative case_55_53_28).check 55 53 28 = true := by
  change case_55_53_28.check 55 53 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_55_53_29_checked :
    (Witness.linear .negative case_55_53_29).check 55 53 29 = true := by
  change case_55_53_29.check 55 53 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_55_53_30_checked :
    (Witness.linear .negative case_55_53_30).check 55 53 30 = true := by
  change case_55_53_30.check 55 53 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_55_53_31_checked :
    (Witness.linear .negative case_55_53_31).check 55 53 31 = true := by
  change case_55_53_31.check 55 53 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_55_53_32_checked :
    (Witness.linear .negative case_55_53_32).check 55 53 32 = true := by
  change case_55_53_32.check 55 53 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_55_53_33_checked :
    (Witness.linear .negative case_55_53_33).check 55 53 33 = true := by
  change case_55_53_33.check 55 53 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_53_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_55_53_34_checked :
    (Witness.linear .negative case_55_53_34).check 55 53 34 = true := by
  change case_55_53_34.check 55 53 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_54_1_checked :
    (Witness.rising).check 55 54 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_54_2_checked :
    (Witness.rising).check 55 54 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_54_3_checked :
    (Witness.rising).check 55 54 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_54_4_checked :
    (Witness.rising).check 55 54 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_54_5_checked :
    (Witness.rising).check 55 54 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_54_6_checked :
    (Witness.rising).check 55 54 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_54_7_checked :
    (Witness.rising).check 55 54 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_54_8_checked :
    (Witness.rising).check 55 54 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_55_54_9_checked :
    (Witness.rising).check 55 54 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_10_checked :
    (Witness.linear .positive case_55_54_10).check 55 54 10 = true := by
  change case_55_54_10.check 55 54 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_11_checked :
    (Witness.linear .positive case_55_54_11).check 55 54 11 = true := by
  change case_55_54_11.check 55 54 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_12_checked :
    (Witness.linear .positive case_55_54_12).check 55 54 12 = true := by
  change case_55_54_12.check 55 54 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_13_checked :
    (Witness.linear .positive case_55_54_13).check 55 54 13 = true := by
  change case_55_54_13.check 55 54 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_14_checked :
    (Witness.linear .positive case_55_54_14).check 55 54 14 = true := by
  change case_55_54_14.check 55 54 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_15_checked :
    (Witness.linear .positive case_55_54_15).check 55 54 15 = true := by
  change case_55_54_15.check 55 54 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_16_checked :
    (Witness.linear .positive case_55_54_16).check 55 54 16 = true := by
  change case_55_54_16.check 55 54 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_17_checked :
    (Witness.linear .positive case_55_54_17).check 55 54 17 = true := by
  change case_55_54_17.check 55 54 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_18_checked :
    (Witness.linear .positive case_55_54_18).check 55 54 18 = true := by
  change case_55_54_18.check 55 54 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_19_checked :
    (Witness.linear .positive case_55_54_19).check 55 54 19 = true := by
  change case_55_54_19.check 55 54 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_20_checked :
    (Witness.linear .positive case_55_54_20).check 55 54 20 = true := by
  change case_55_54_20.check 55 54 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_21_checked :
    (Witness.linear .positive case_55_54_21).check 55 54 21 = true := by
  change case_55_54_21.check 55 54 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_22_checked :
    (Witness.linear .positive case_55_54_22).check 55 54 22 = true := by
  change case_55_54_22.check 55 54 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_23_checked :
    (Witness.linear .positive case_55_54_23).check 55 54 23 = true := by
  change case_55_54_23.check 55 54 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_24_checked :
    (Witness.linear .positive case_55_54_24).check 55 54 24 = true := by
  change case_55_54_24.check 55 54 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_25_checked :
    (Witness.linear .positive case_55_54_25).check 55 54 25 = true := by
  change case_55_54_25.check 55 54 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_26_checked :
    (Witness.linear .positive case_55_54_26).check 55 54 26 = true := by
  change case_55_54_26.check 55 54 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_27 : Certificate := {
  objectiveScale := 1
  eta := 4861946401452
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_27_checked :
    (Witness.linear .positive case_55_54_27).check 55 54 27 = true := by
  change case_55_54_27.check 55 54 27 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_28_checked :
    (Witness.linear .negative case_55_54_28).check 55 54 28 = true := by
  change case_55_54_28.check 55 54 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_29_checked :
    (Witness.linear .negative case_55_54_29).check 55 54 29 = true := by
  change case_55_54_29.check 55 54 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_30_checked :
    (Witness.linear .negative case_55_54_30).check 55 54 30 = true := by
  change case_55_54_30.check 55 54 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_31_checked :
    (Witness.linear .negative case_55_54_31).check 55 54 31 = true := by
  change case_55_54_31.check 55 54 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_32_checked :
    (Witness.linear .negative case_55_54_32).check 55 54 32 = true := by
  change case_55_54_32.check 55 54 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_33_checked :
    (Witness.linear .negative case_55_54_33).check 55 54 33 = true := by
  change case_55_54_33.check 55 54 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_34_checked :
    (Witness.linear .negative case_55_54_34).check 55 54 34 = true := by
  change case_55_54_34.check 55 54 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_55_54_35 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_55_54_35_checked :
    (Witness.linear .negative case_55_54_35).check 55 54 35 = true := by
  change case_55_54_35.check 55 54 35 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_55 (a k : ℕ) (h : Domain 55 a k) :
    ∃ w : Witness, w.check 55 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 28 ≤ a := by omega
  have haHi : a ≤ 54 := by omega
  interval_cases a

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_28_1_checked⟩

    · exact ⟨Witness.rising, case_55_28_2_checked⟩

    · exact ⟨Witness.rising, case_55_28_3_checked⟩

    · exact ⟨Witness.rising, case_55_28_4_checked⟩

    · exact ⟨Witness.rising, case_55_28_5_checked⟩

    · exact ⟨Witness.rising, case_55_28_6_checked⟩

    · exact ⟨Witness.rising, case_55_28_7_checked⟩

    · exact ⟨Witness.rising, case_55_28_8_checked⟩

    · exact ⟨Witness.rising, case_55_28_9_checked⟩

    · exact ⟨Witness.rising, case_55_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_28_11, case_55_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_28_12, case_55_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_28_13, case_55_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_28_14, case_55_28_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_28_15, case_55_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_55_28_16, case_55_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_55_28_17, case_55_28_17_checked⟩

    · exact ⟨Witness.linear .conditional case_55_28_18, case_55_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_29_1_checked⟩

    · exact ⟨Witness.rising, case_55_29_2_checked⟩

    · exact ⟨Witness.rising, case_55_29_3_checked⟩

    · exact ⟨Witness.rising, case_55_29_4_checked⟩

    · exact ⟨Witness.rising, case_55_29_5_checked⟩

    · exact ⟨Witness.rising, case_55_29_6_checked⟩

    · exact ⟨Witness.rising, case_55_29_7_checked⟩

    · exact ⟨Witness.rising, case_55_29_8_checked⟩

    · exact ⟨Witness.rising, case_55_29_9_checked⟩

    · exact ⟨Witness.rising, case_55_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_29_11, case_55_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_29_12, case_55_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_29_13, case_55_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_29_14, case_55_29_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_29_15, case_55_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_55_29_16, case_55_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_55_29_17, case_55_29_17_checked⟩

    · exact ⟨Witness.linear .conditional case_55_29_18, case_55_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_30_1_checked⟩

    · exact ⟨Witness.rising, case_55_30_2_checked⟩

    · exact ⟨Witness.rising, case_55_30_3_checked⟩

    · exact ⟨Witness.rising, case_55_30_4_checked⟩

    · exact ⟨Witness.rising, case_55_30_5_checked⟩

    · exact ⟨Witness.rising, case_55_30_6_checked⟩

    · exact ⟨Witness.rising, case_55_30_7_checked⟩

    · exact ⟨Witness.rising, case_55_30_8_checked⟩

    · exact ⟨Witness.rising, case_55_30_9_checked⟩

    · exact ⟨Witness.rising, case_55_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_30_11, case_55_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_30_12, case_55_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_30_13, case_55_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_30_14, case_55_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_30_15, case_55_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_55_30_16, case_55_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_55_30_17, case_55_30_17_checked⟩

    · exact ⟨Witness.linear .conditional case_55_30_18, case_55_30_18_checked⟩

    · exact ⟨Witness.linear .conditional case_55_30_19, case_55_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_31_1_checked⟩

    · exact ⟨Witness.rising, case_55_31_2_checked⟩

    · exact ⟨Witness.rising, case_55_31_3_checked⟩

    · exact ⟨Witness.rising, case_55_31_4_checked⟩

    · exact ⟨Witness.rising, case_55_31_5_checked⟩

    · exact ⟨Witness.rising, case_55_31_6_checked⟩

    · exact ⟨Witness.rising, case_55_31_7_checked⟩

    · exact ⟨Witness.rising, case_55_31_8_checked⟩

    · exact ⟨Witness.rising, case_55_31_9_checked⟩

    · exact ⟨Witness.rising, case_55_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_31_11, case_55_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_31_12, case_55_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_31_13, case_55_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_31_14, case_55_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_31_15, case_55_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_55_31_16, case_55_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_55_31_17, case_55_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_55_31_18, case_55_31_18_checked⟩

    · exact ⟨Witness.linear .conditional case_55_31_19, case_55_31_19_checked⟩

    · exact ⟨Witness.linear .conditional case_55_31_20, case_55_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_32_1_checked⟩

    · exact ⟨Witness.rising, case_55_32_2_checked⟩

    · exact ⟨Witness.rising, case_55_32_3_checked⟩

    · exact ⟨Witness.rising, case_55_32_4_checked⟩

    · exact ⟨Witness.rising, case_55_32_5_checked⟩

    · exact ⟨Witness.rising, case_55_32_6_checked⟩

    · exact ⟨Witness.rising, case_55_32_7_checked⟩

    · exact ⟨Witness.rising, case_55_32_8_checked⟩

    · exact ⟨Witness.rising, case_55_32_9_checked⟩

    · exact ⟨Witness.rising, case_55_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_32_11, case_55_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_32_12, case_55_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_32_13, case_55_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_32_14, case_55_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_32_15, case_55_32_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_32_16, case_55_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_55_32_17, case_55_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_55_32_18, case_55_32_18_checked⟩

    · exact ⟨Witness.linear .conditional case_55_32_19, case_55_32_19_checked⟩

    · exact ⟨Witness.linear .conditional case_55_32_20, case_55_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_33_1_checked⟩

    · exact ⟨Witness.rising, case_55_33_2_checked⟩

    · exact ⟨Witness.rising, case_55_33_3_checked⟩

    · exact ⟨Witness.rising, case_55_33_4_checked⟩

    · exact ⟨Witness.rising, case_55_33_5_checked⟩

    · exact ⟨Witness.rising, case_55_33_6_checked⟩

    · exact ⟨Witness.rising, case_55_33_7_checked⟩

    · exact ⟨Witness.rising, case_55_33_8_checked⟩

    · exact ⟨Witness.rising, case_55_33_9_checked⟩

    · exact ⟨Witness.rising, case_55_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_33_11, case_55_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_33_12, case_55_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_33_13, case_55_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_33_14, case_55_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_33_15, case_55_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_33_16, case_55_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_55_33_17, case_55_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_55_33_18, case_55_33_18_checked⟩

    · exact ⟨Witness.linear .conditional case_55_33_19, case_55_33_19_checked⟩

    · exact ⟨Witness.linear .conditional case_55_33_20, case_55_33_20_checked⟩

    · exact ⟨Witness.linear .conditional case_55_33_21, case_55_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_34_1_checked⟩

    · exact ⟨Witness.rising, case_55_34_2_checked⟩

    · exact ⟨Witness.rising, case_55_34_3_checked⟩

    · exact ⟨Witness.rising, case_55_34_4_checked⟩

    · exact ⟨Witness.rising, case_55_34_5_checked⟩

    · exact ⟨Witness.rising, case_55_34_6_checked⟩

    · exact ⟨Witness.rising, case_55_34_7_checked⟩

    · exact ⟨Witness.rising, case_55_34_8_checked⟩

    · exact ⟨Witness.rising, case_55_34_9_checked⟩

    · exact ⟨Witness.rising, case_55_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_34_11, case_55_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_34_12, case_55_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_34_13, case_55_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_34_14, case_55_34_14_checked⟩

    · exact ⟨Witness.linear .conditional case_55_34_15, case_55_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_34_16, case_55_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_55_34_17, case_55_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_55_34_18, case_55_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_55_34_19, case_55_34_19_checked⟩

    · exact ⟨Witness.linear .conditional case_55_34_20, case_55_34_20_checked⟩

    · exact ⟨Witness.linear .conditional case_55_34_21, case_55_34_21_checked⟩

    · exact ⟨Witness.linear .conditional case_55_34_22, case_55_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_35_1_checked⟩

    · exact ⟨Witness.rising, case_55_35_2_checked⟩

    · exact ⟨Witness.rising, case_55_35_3_checked⟩

    · exact ⟨Witness.rising, case_55_35_4_checked⟩

    · exact ⟨Witness.rising, case_55_35_5_checked⟩

    · exact ⟨Witness.rising, case_55_35_6_checked⟩

    · exact ⟨Witness.rising, case_55_35_7_checked⟩

    · exact ⟨Witness.rising, case_55_35_8_checked⟩

    · exact ⟨Witness.rising, case_55_35_9_checked⟩

    · exact ⟨Witness.rising, case_55_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_35_11, case_55_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_35_12, case_55_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_35_13, case_55_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_35_14, case_55_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_35_15, case_55_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_35_16, case_55_35_16_checked⟩

    · exact ⟨Witness.linear .conditional case_55_35_17, case_55_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_55_35_18, case_55_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_55_35_19, case_55_35_19_checked⟩

    · exact ⟨Witness.linear .conditional case_55_35_20, case_55_35_20_checked⟩

    · exact ⟨Witness.linear .conditional case_55_35_21, case_55_35_21_checked⟩

    · exact ⟨Witness.linear .conditional case_55_35_22, case_55_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_36_1_checked⟩

    · exact ⟨Witness.rising, case_55_36_2_checked⟩

    · exact ⟨Witness.rising, case_55_36_3_checked⟩

    · exact ⟨Witness.rising, case_55_36_4_checked⟩

    · exact ⟨Witness.rising, case_55_36_5_checked⟩

    · exact ⟨Witness.rising, case_55_36_6_checked⟩

    · exact ⟨Witness.rising, case_55_36_7_checked⟩

    · exact ⟨Witness.rising, case_55_36_8_checked⟩

    · exact ⟨Witness.rising, case_55_36_9_checked⟩

    · exact ⟨Witness.rising, case_55_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_36_11, case_55_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_36_12, case_55_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_36_13, case_55_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_36_14, case_55_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_36_15, case_55_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_36_16, case_55_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_36_17, case_55_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_55_36_18, case_55_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_55_36_19, case_55_36_19_checked⟩

    · exact ⟨Witness.linear .conditional case_55_36_20, case_55_36_20_checked⟩

    · exact ⟨Witness.linear .conditional case_55_36_21, case_55_36_21_checked⟩

    · exact ⟨Witness.linear .conditional case_55_36_22, case_55_36_22_checked⟩

    · exact ⟨Witness.linear .conditional case_55_36_23, case_55_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_37_1_checked⟩

    · exact ⟨Witness.rising, case_55_37_2_checked⟩

    · exact ⟨Witness.rising, case_55_37_3_checked⟩

    · exact ⟨Witness.rising, case_55_37_4_checked⟩

    · exact ⟨Witness.rising, case_55_37_5_checked⟩

    · exact ⟨Witness.rising, case_55_37_6_checked⟩

    · exact ⟨Witness.rising, case_55_37_7_checked⟩

    · exact ⟨Witness.rising, case_55_37_8_checked⟩

    · exact ⟨Witness.rising, case_55_37_9_checked⟩

    · exact ⟨Witness.rising, case_55_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_37_11, case_55_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_37_12, case_55_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_37_13, case_55_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_37_14, case_55_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_37_15, case_55_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_37_16, case_55_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_37_17, case_55_37_17_checked⟩

    · exact ⟨Witness.linear .conditional case_55_37_18, case_55_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_55_37_19, case_55_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_55_37_20, case_55_37_20_checked⟩

    · exact ⟨Witness.linear .conditional case_55_37_21, case_55_37_21_checked⟩

    · exact ⟨Witness.linear .conditional case_55_37_22, case_55_37_22_checked⟩

    · exact ⟨Witness.linear .conditional case_55_37_23, case_55_37_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_37_24, case_55_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_38_1_checked⟩

    · exact ⟨Witness.rising, case_55_38_2_checked⟩

    · exact ⟨Witness.rising, case_55_38_3_checked⟩

    · exact ⟨Witness.rising, case_55_38_4_checked⟩

    · exact ⟨Witness.rising, case_55_38_5_checked⟩

    · exact ⟨Witness.rising, case_55_38_6_checked⟩

    · exact ⟨Witness.rising, case_55_38_7_checked⟩

    · exact ⟨Witness.rising, case_55_38_8_checked⟩

    · exact ⟨Witness.rising, case_55_38_9_checked⟩

    · exact ⟨Witness.rising, case_55_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_38_11, case_55_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_38_12, case_55_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_38_13, case_55_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_38_14, case_55_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_38_15, case_55_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_38_16, case_55_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_38_17, case_55_38_17_checked⟩

    · exact ⟨Witness.linear .conditional case_55_38_18, case_55_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_55_38_19, case_55_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_55_38_20, case_55_38_20_checked⟩

    · exact ⟨Witness.linear .conditional case_55_38_21, case_55_38_21_checked⟩

    · exact ⟨Witness.linear .conditional case_55_38_22, case_55_38_22_checked⟩

    · exact ⟨Witness.linear .conditional case_55_38_23, case_55_38_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_38_24, case_55_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_39_1_checked⟩

    · exact ⟨Witness.rising, case_55_39_2_checked⟩

    · exact ⟨Witness.rising, case_55_39_3_checked⟩

    · exact ⟨Witness.rising, case_55_39_4_checked⟩

    · exact ⟨Witness.rising, case_55_39_5_checked⟩

    · exact ⟨Witness.rising, case_55_39_6_checked⟩

    · exact ⟨Witness.rising, case_55_39_7_checked⟩

    · exact ⟨Witness.rising, case_55_39_8_checked⟩

    · exact ⟨Witness.rising, case_55_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_39_10, case_55_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_39_11, case_55_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_39_12, case_55_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_39_13, case_55_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_39_14, case_55_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_39_15, case_55_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_39_16, case_55_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_39_17, case_55_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_39_18, case_55_39_18_checked⟩

    · exact ⟨Witness.linear .conditional case_55_39_19, case_55_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_55_39_20, case_55_39_20_checked⟩

    · exact ⟨Witness.linear .conditional case_55_39_21, case_55_39_21_checked⟩

    · exact ⟨Witness.linear .conditional case_55_39_22, case_55_39_22_checked⟩

    · exact ⟨Witness.linear .conditional case_55_39_23, case_55_39_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_39_24, case_55_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_55_39_25, case_55_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_40_1_checked⟩

    · exact ⟨Witness.rising, case_55_40_2_checked⟩

    · exact ⟨Witness.rising, case_55_40_3_checked⟩

    · exact ⟨Witness.rising, case_55_40_4_checked⟩

    · exact ⟨Witness.rising, case_55_40_5_checked⟩

    · exact ⟨Witness.rising, case_55_40_6_checked⟩

    · exact ⟨Witness.rising, case_55_40_7_checked⟩

    · exact ⟨Witness.rising, case_55_40_8_checked⟩

    · exact ⟨Witness.rising, case_55_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_40_10, case_55_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_40_11, case_55_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_40_12, case_55_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_40_13, case_55_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_40_14, case_55_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_40_15, case_55_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_40_16, case_55_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_40_17, case_55_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_40_18, case_55_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_40_19, case_55_40_19_checked⟩

    · exact ⟨Witness.linear .conditional case_55_40_20, case_55_40_20_checked⟩

    · exact ⟨Witness.linear .conditional case_55_40_21, case_55_40_21_checked⟩

    · exact ⟨Witness.linear .conditional case_55_40_22, case_55_40_22_checked⟩

    · exact ⟨Witness.linear .conditional case_55_40_23, case_55_40_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_40_24, case_55_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_55_40_25, case_55_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_40_26, case_55_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_41_1_checked⟩

    · exact ⟨Witness.rising, case_55_41_2_checked⟩

    · exact ⟨Witness.rising, case_55_41_3_checked⟩

    · exact ⟨Witness.rising, case_55_41_4_checked⟩

    · exact ⟨Witness.rising, case_55_41_5_checked⟩

    · exact ⟨Witness.rising, case_55_41_6_checked⟩

    · exact ⟨Witness.rising, case_55_41_7_checked⟩

    · exact ⟨Witness.rising, case_55_41_8_checked⟩

    · exact ⟨Witness.rising, case_55_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_41_10, case_55_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_41_11, case_55_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_41_12, case_55_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_41_13, case_55_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_41_14, case_55_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_41_15, case_55_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_41_16, case_55_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_41_17, case_55_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_41_18, case_55_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_41_19, case_55_41_19_checked⟩

    · exact ⟨Witness.linear .conditional case_55_41_20, case_55_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_55_41_21, case_55_41_21_checked⟩

    · exact ⟨Witness.linear .conditional case_55_41_22, case_55_41_22_checked⟩

    · exact ⟨Witness.linear .conditional case_55_41_23, case_55_41_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_41_24, case_55_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_55_41_25, case_55_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_41_26, case_55_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_42_1_checked⟩

    · exact ⟨Witness.rising, case_55_42_2_checked⟩

    · exact ⟨Witness.rising, case_55_42_3_checked⟩

    · exact ⟨Witness.rising, case_55_42_4_checked⟩

    · exact ⟨Witness.rising, case_55_42_5_checked⟩

    · exact ⟨Witness.rising, case_55_42_6_checked⟩

    · exact ⟨Witness.rising, case_55_42_7_checked⟩

    · exact ⟨Witness.rising, case_55_42_8_checked⟩

    · exact ⟨Witness.rising, case_55_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_42_10, case_55_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_42_11, case_55_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_42_12, case_55_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_42_13, case_55_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_42_14, case_55_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_42_15, case_55_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_42_16, case_55_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_42_17, case_55_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_42_18, case_55_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_42_19, case_55_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_42_20, case_55_42_20_checked⟩

    · exact ⟨Witness.linear .conditional case_55_42_21, case_55_42_21_checked⟩

    · exact ⟨Witness.linear .conditional case_55_42_22, case_55_42_22_checked⟩

    · exact ⟨Witness.linear .conditional case_55_42_23, case_55_42_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_42_24, case_55_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_55_42_25, case_55_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_42_26, case_55_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_42_27, case_55_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_43_1_checked⟩

    · exact ⟨Witness.rising, case_55_43_2_checked⟩

    · exact ⟨Witness.rising, case_55_43_3_checked⟩

    · exact ⟨Witness.rising, case_55_43_4_checked⟩

    · exact ⟨Witness.rising, case_55_43_5_checked⟩

    · exact ⟨Witness.rising, case_55_43_6_checked⟩

    · exact ⟨Witness.rising, case_55_43_7_checked⟩

    · exact ⟨Witness.rising, case_55_43_8_checked⟩

    · exact ⟨Witness.rising, case_55_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_43_10, case_55_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_43_11, case_55_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_43_12, case_55_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_43_13, case_55_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_43_14, case_55_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_43_15, case_55_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_43_16, case_55_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_43_17, case_55_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_43_18, case_55_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_43_19, case_55_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_43_20, case_55_43_20_checked⟩

    · exact ⟨Witness.linear .conditional case_55_43_21, case_55_43_21_checked⟩

    · exact ⟨Witness.linear .conditional case_55_43_22, case_55_43_22_checked⟩

    · exact ⟨Witness.linear .conditional case_55_43_23, case_55_43_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_43_24, case_55_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_55_43_25, case_55_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_43_26, case_55_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_43_27, case_55_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_43_28, case_55_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_44_1_checked⟩

    · exact ⟨Witness.rising, case_55_44_2_checked⟩

    · exact ⟨Witness.rising, case_55_44_3_checked⟩

    · exact ⟨Witness.rising, case_55_44_4_checked⟩

    · exact ⟨Witness.rising, case_55_44_5_checked⟩

    · exact ⟨Witness.rising, case_55_44_6_checked⟩

    · exact ⟨Witness.rising, case_55_44_7_checked⟩

    · exact ⟨Witness.rising, case_55_44_8_checked⟩

    · exact ⟨Witness.rising, case_55_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_10, case_55_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_11, case_55_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_12, case_55_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_13, case_55_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_14, case_55_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_15, case_55_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_16, case_55_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_17, case_55_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_18, case_55_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_19, case_55_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_20, case_55_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_55_44_21, case_55_44_21_checked⟩

    · exact ⟨Witness.linear .conditional case_55_44_22, case_55_44_22_checked⟩

    · exact ⟨Witness.linear .conditional case_55_44_23, case_55_44_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_44_24, case_55_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_55_44_25, case_55_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_44_26, case_55_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_44_27, case_55_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_44_28, case_55_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_45_1_checked⟩

    · exact ⟨Witness.rising, case_55_45_2_checked⟩

    · exact ⟨Witness.rising, case_55_45_3_checked⟩

    · exact ⟨Witness.rising, case_55_45_4_checked⟩

    · exact ⟨Witness.rising, case_55_45_5_checked⟩

    · exact ⟨Witness.rising, case_55_45_6_checked⟩

    · exact ⟨Witness.rising, case_55_45_7_checked⟩

    · exact ⟨Witness.rising, case_55_45_8_checked⟩

    · exact ⟨Witness.rising, case_55_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_10, case_55_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_11, case_55_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_12, case_55_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_13, case_55_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_14, case_55_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_15, case_55_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_16, case_55_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_17, case_55_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_18, case_55_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_19, case_55_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_20, case_55_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_21, case_55_45_21_checked⟩

    · exact ⟨Witness.linear .positive case_55_45_22, case_55_45_22_checked⟩

    · exact ⟨Witness.linear .conditional case_55_45_23, case_55_45_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_45_24, case_55_45_24_checked⟩

    · exact ⟨Witness.linear .negative case_55_45_25, case_55_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_45_26, case_55_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_45_27, case_55_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_45_28, case_55_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_55_45_29, case_55_45_29_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_46_1_checked⟩

    · exact ⟨Witness.rising, case_55_46_2_checked⟩

    · exact ⟨Witness.rising, case_55_46_3_checked⟩

    · exact ⟨Witness.rising, case_55_46_4_checked⟩

    · exact ⟨Witness.rising, case_55_46_5_checked⟩

    · exact ⟨Witness.rising, case_55_46_6_checked⟩

    · exact ⟨Witness.rising, case_55_46_7_checked⟩

    · exact ⟨Witness.rising, case_55_46_8_checked⟩

    · exact ⟨Witness.rising, case_55_46_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_10, case_55_46_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_11, case_55_46_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_12, case_55_46_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_13, case_55_46_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_14, case_55_46_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_15, case_55_46_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_16, case_55_46_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_17, case_55_46_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_18, case_55_46_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_19, case_55_46_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_20, case_55_46_20_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_21, case_55_46_21_checked⟩

    · exact ⟨Witness.linear .positive case_55_46_22, case_55_46_22_checked⟩

    · exact ⟨Witness.linear .conditional case_55_46_23, case_55_46_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_46_24, case_55_46_24_checked⟩

    · exact ⟨Witness.linear .negative case_55_46_25, case_55_46_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_46_26, case_55_46_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_46_27, case_55_46_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_46_28, case_55_46_28_checked⟩

    · exact ⟨Witness.linear .negative case_55_46_29, case_55_46_29_checked⟩

    · exact ⟨Witness.linear .negative case_55_46_30, case_55_46_30_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_47_1_checked⟩

    · exact ⟨Witness.rising, case_55_47_2_checked⟩

    · exact ⟨Witness.rising, case_55_47_3_checked⟩

    · exact ⟨Witness.rising, case_55_47_4_checked⟩

    · exact ⟨Witness.rising, case_55_47_5_checked⟩

    · exact ⟨Witness.rising, case_55_47_6_checked⟩

    · exact ⟨Witness.rising, case_55_47_7_checked⟩

    · exact ⟨Witness.rising, case_55_47_8_checked⟩

    · exact ⟨Witness.rising, case_55_47_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_10, case_55_47_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_11, case_55_47_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_12, case_55_47_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_13, case_55_47_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_14, case_55_47_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_15, case_55_47_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_16, case_55_47_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_17, case_55_47_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_18, case_55_47_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_19, case_55_47_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_20, case_55_47_20_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_21, case_55_47_21_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_22, case_55_47_22_checked⟩

    · exact ⟨Witness.linear .positive case_55_47_23, case_55_47_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_47_24, case_55_47_24_checked⟩

    · exact ⟨Witness.linear .negative case_55_47_25, case_55_47_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_47_26, case_55_47_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_47_27, case_55_47_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_47_28, case_55_47_28_checked⟩

    · exact ⟨Witness.linear .negative case_55_47_29, case_55_47_29_checked⟩

    · exact ⟨Witness.linear .negative case_55_47_30, case_55_47_30_checked⟩

  · have hkHi : k ≤ 31 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_48_1_checked⟩

    · exact ⟨Witness.rising, case_55_48_2_checked⟩

    · exact ⟨Witness.rising, case_55_48_3_checked⟩

    · exact ⟨Witness.rising, case_55_48_4_checked⟩

    · exact ⟨Witness.rising, case_55_48_5_checked⟩

    · exact ⟨Witness.rising, case_55_48_6_checked⟩

    · exact ⟨Witness.rising, case_55_48_7_checked⟩

    · exact ⟨Witness.rising, case_55_48_8_checked⟩

    · exact ⟨Witness.rising, case_55_48_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_10, case_55_48_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_11, case_55_48_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_12, case_55_48_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_13, case_55_48_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_14, case_55_48_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_15, case_55_48_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_16, case_55_48_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_17, case_55_48_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_18, case_55_48_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_19, case_55_48_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_20, case_55_48_20_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_21, case_55_48_21_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_22, case_55_48_22_checked⟩

    · exact ⟨Witness.linear .positive case_55_48_23, case_55_48_23_checked⟩

    · exact ⟨Witness.linear .conditional case_55_48_24, case_55_48_24_checked⟩

    · exact ⟨Witness.linear .conditional case_55_48_25, case_55_48_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_48_26, case_55_48_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_48_27, case_55_48_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_48_28, case_55_48_28_checked⟩

    · exact ⟨Witness.linear .negative case_55_48_29, case_55_48_29_checked⟩

    · exact ⟨Witness.linear .negative case_55_48_30, case_55_48_30_checked⟩

    · exact ⟨Witness.linear .negative case_55_48_31, case_55_48_31_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_49_1_checked⟩

    · exact ⟨Witness.rising, case_55_49_2_checked⟩

    · exact ⟨Witness.rising, case_55_49_3_checked⟩

    · exact ⟨Witness.rising, case_55_49_4_checked⟩

    · exact ⟨Witness.rising, case_55_49_5_checked⟩

    · exact ⟨Witness.rising, case_55_49_6_checked⟩

    · exact ⟨Witness.rising, case_55_49_7_checked⟩

    · exact ⟨Witness.rising, case_55_49_8_checked⟩

    · exact ⟨Witness.rising, case_55_49_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_10, case_55_49_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_11, case_55_49_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_12, case_55_49_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_13, case_55_49_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_14, case_55_49_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_15, case_55_49_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_16, case_55_49_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_17, case_55_49_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_18, case_55_49_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_19, case_55_49_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_20, case_55_49_20_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_21, case_55_49_21_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_22, case_55_49_22_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_23, case_55_49_23_checked⟩

    · exact ⟨Witness.linear .positive case_55_49_24, case_55_49_24_checked⟩

    · exact ⟨Witness.linear .conditional case_55_49_25, case_55_49_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_49_26, case_55_49_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_49_27, case_55_49_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_49_28, case_55_49_28_checked⟩

    · exact ⟨Witness.linear .negative case_55_49_29, case_55_49_29_checked⟩

    · exact ⟨Witness.linear .negative case_55_49_30, case_55_49_30_checked⟩

    · exact ⟨Witness.linear .negative case_55_49_31, case_55_49_31_checked⟩

    · exact ⟨Witness.linear .negative case_55_49_32, case_55_49_32_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_50_1_checked⟩

    · exact ⟨Witness.rising, case_55_50_2_checked⟩

    · exact ⟨Witness.rising, case_55_50_3_checked⟩

    · exact ⟨Witness.rising, case_55_50_4_checked⟩

    · exact ⟨Witness.rising, case_55_50_5_checked⟩

    · exact ⟨Witness.rising, case_55_50_6_checked⟩

    · exact ⟨Witness.rising, case_55_50_7_checked⟩

    · exact ⟨Witness.rising, case_55_50_8_checked⟩

    · exact ⟨Witness.rising, case_55_50_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_10, case_55_50_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_11, case_55_50_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_12, case_55_50_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_13, case_55_50_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_14, case_55_50_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_15, case_55_50_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_16, case_55_50_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_17, case_55_50_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_18, case_55_50_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_19, case_55_50_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_20, case_55_50_20_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_21, case_55_50_21_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_22, case_55_50_22_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_23, case_55_50_23_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_24, case_55_50_24_checked⟩

    · exact ⟨Witness.linear .positive case_55_50_25, case_55_50_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_50_26, case_55_50_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_50_27, case_55_50_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_50_28, case_55_50_28_checked⟩

    · exact ⟨Witness.linear .negative case_55_50_29, case_55_50_29_checked⟩

    · exact ⟨Witness.linear .negative case_55_50_30, case_55_50_30_checked⟩

    · exact ⟨Witness.linear .negative case_55_50_31, case_55_50_31_checked⟩

    · exact ⟨Witness.linear .negative case_55_50_32, case_55_50_32_checked⟩

  · have hkHi : k ≤ 33 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_51_1_checked⟩

    · exact ⟨Witness.rising, case_55_51_2_checked⟩

    · exact ⟨Witness.rising, case_55_51_3_checked⟩

    · exact ⟨Witness.rising, case_55_51_4_checked⟩

    · exact ⟨Witness.rising, case_55_51_5_checked⟩

    · exact ⟨Witness.rising, case_55_51_6_checked⟩

    · exact ⟨Witness.rising, case_55_51_7_checked⟩

    · exact ⟨Witness.rising, case_55_51_8_checked⟩

    · exact ⟨Witness.rising, case_55_51_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_10, case_55_51_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_11, case_55_51_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_12, case_55_51_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_13, case_55_51_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_14, case_55_51_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_15, case_55_51_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_16, case_55_51_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_17, case_55_51_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_18, case_55_51_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_19, case_55_51_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_20, case_55_51_20_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_21, case_55_51_21_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_22, case_55_51_22_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_23, case_55_51_23_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_24, case_55_51_24_checked⟩

    · exact ⟨Witness.linear .positive case_55_51_25, case_55_51_25_checked⟩

    · exact ⟨Witness.linear .negative case_55_51_26, case_55_51_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_51_27, case_55_51_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_51_28, case_55_51_28_checked⟩

    · exact ⟨Witness.linear .negative case_55_51_29, case_55_51_29_checked⟩

    · exact ⟨Witness.linear .negative case_55_51_30, case_55_51_30_checked⟩

    · exact ⟨Witness.linear .negative case_55_51_31, case_55_51_31_checked⟩

    · exact ⟨Witness.linear .negative case_55_51_32, case_55_51_32_checked⟩

    · exact ⟨Witness.linear .negative case_55_51_33, case_55_51_33_checked⟩

  · have hkHi : k ≤ 34 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_52_1_checked⟩

    · exact ⟨Witness.rising, case_55_52_2_checked⟩

    · exact ⟨Witness.rising, case_55_52_3_checked⟩

    · exact ⟨Witness.rising, case_55_52_4_checked⟩

    · exact ⟨Witness.rising, case_55_52_5_checked⟩

    · exact ⟨Witness.rising, case_55_52_6_checked⟩

    · exact ⟨Witness.rising, case_55_52_7_checked⟩

    · exact ⟨Witness.rising, case_55_52_8_checked⟩

    · exact ⟨Witness.rising, case_55_52_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_10, case_55_52_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_11, case_55_52_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_12, case_55_52_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_13, case_55_52_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_14, case_55_52_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_15, case_55_52_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_16, case_55_52_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_17, case_55_52_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_18, case_55_52_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_19, case_55_52_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_20, case_55_52_20_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_21, case_55_52_21_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_22, case_55_52_22_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_23, case_55_52_23_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_24, case_55_52_24_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_25, case_55_52_25_checked⟩

    · exact ⟨Witness.linear .positive case_55_52_26, case_55_52_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_52_27, case_55_52_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_52_28, case_55_52_28_checked⟩

    · exact ⟨Witness.linear .negative case_55_52_29, case_55_52_29_checked⟩

    · exact ⟨Witness.linear .negative case_55_52_30, case_55_52_30_checked⟩

    · exact ⟨Witness.linear .negative case_55_52_31, case_55_52_31_checked⟩

    · exact ⟨Witness.linear .negative case_55_52_32, case_55_52_32_checked⟩

    · exact ⟨Witness.linear .negative case_55_52_33, case_55_52_33_checked⟩

    · exact ⟨Witness.linear .negative case_55_52_34, case_55_52_34_checked⟩

  · have hkHi : k ≤ 34 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_53_1_checked⟩

    · exact ⟨Witness.rising, case_55_53_2_checked⟩

    · exact ⟨Witness.rising, case_55_53_3_checked⟩

    · exact ⟨Witness.rising, case_55_53_4_checked⟩

    · exact ⟨Witness.rising, case_55_53_5_checked⟩

    · exact ⟨Witness.rising, case_55_53_6_checked⟩

    · exact ⟨Witness.rising, case_55_53_7_checked⟩

    · exact ⟨Witness.rising, case_55_53_8_checked⟩

    · exact ⟨Witness.rising, case_55_53_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_10, case_55_53_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_11, case_55_53_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_12, case_55_53_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_13, case_55_53_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_14, case_55_53_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_15, case_55_53_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_16, case_55_53_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_17, case_55_53_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_18, case_55_53_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_19, case_55_53_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_20, case_55_53_20_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_21, case_55_53_21_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_22, case_55_53_22_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_23, case_55_53_23_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_24, case_55_53_24_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_25, case_55_53_25_checked⟩

    · exact ⟨Witness.linear .positive case_55_53_26, case_55_53_26_checked⟩

    · exact ⟨Witness.linear .negative case_55_53_27, case_55_53_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_53_28, case_55_53_28_checked⟩

    · exact ⟨Witness.linear .negative case_55_53_29, case_55_53_29_checked⟩

    · exact ⟨Witness.linear .negative case_55_53_30, case_55_53_30_checked⟩

    · exact ⟨Witness.linear .negative case_55_53_31, case_55_53_31_checked⟩

    · exact ⟨Witness.linear .negative case_55_53_32, case_55_53_32_checked⟩

    · exact ⟨Witness.linear .negative case_55_53_33, case_55_53_33_checked⟩

    · exact ⟨Witness.linear .negative case_55_53_34, case_55_53_34_checked⟩

  · have hkHi : k ≤ 35 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_55_54_1_checked⟩

    · exact ⟨Witness.rising, case_55_54_2_checked⟩

    · exact ⟨Witness.rising, case_55_54_3_checked⟩

    · exact ⟨Witness.rising, case_55_54_4_checked⟩

    · exact ⟨Witness.rising, case_55_54_5_checked⟩

    · exact ⟨Witness.rising, case_55_54_6_checked⟩

    · exact ⟨Witness.rising, case_55_54_7_checked⟩

    · exact ⟨Witness.rising, case_55_54_8_checked⟩

    · exact ⟨Witness.rising, case_55_54_9_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_10, case_55_54_10_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_11, case_55_54_11_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_12, case_55_54_12_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_13, case_55_54_13_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_14, case_55_54_14_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_15, case_55_54_15_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_16, case_55_54_16_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_17, case_55_54_17_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_18, case_55_54_18_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_19, case_55_54_19_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_20, case_55_54_20_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_21, case_55_54_21_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_22, case_55_54_22_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_23, case_55_54_23_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_24, case_55_54_24_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_25, case_55_54_25_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_26, case_55_54_26_checked⟩

    · exact ⟨Witness.linear .positive case_55_54_27, case_55_54_27_checked⟩

    · exact ⟨Witness.linear .negative case_55_54_28, case_55_54_28_checked⟩

    · exact ⟨Witness.linear .negative case_55_54_29, case_55_54_29_checked⟩

    · exact ⟨Witness.linear .negative case_55_54_30, case_55_54_30_checked⟩

    · exact ⟨Witness.linear .negative case_55_54_31, case_55_54_31_checked⟩

    · exact ⟨Witness.linear .negative case_55_54_32, case_55_54_32_checked⟩

    · exact ⟨Witness.linear .negative case_55_54_33, case_55_54_33_checked⟩

    · exact ⟨Witness.linear .negative case_55_54_34, case_55_54_34_checked⟩

    · exact ⟨Witness.linear .negative case_55_54_35, case_55_54_35_checked⟩


#print axioms coverage_55
end ForestUnimodality.FiniteRows.FiniteData
